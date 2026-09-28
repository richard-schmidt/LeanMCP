"""Every decision the Lean MCP surface makes, with no process or protocol in sight.

Path resolution, tactic splicing, UTF-16 positions, verdicts, the search snippet
and its parser, lake-build output parsing, and all rendering to prose live here,
because this is the layer tests/test_core.py reaches. session.py only moves
values between this module and a Lean server; mcp_server.py only speaks JSON-RPC.
"""
import json
import os
import re

LAKEFILES = ("lakefile.toml", "lakefile.lean")
SEARCH_MARK = "LEANMCP_SEARCH"


class UserError(Exception):
    """A bad request from the caller. Rendered back as data, never a crash."""


# ---------------------------------------------------------------- paths

def find_project(file, default_project):
    """Resolve `file` to (project_root, relative_path).

    An absolute path finds its project by walking up to the nearest lakefile;
    a relative path is relative to `default_project`.
    """
    if not file or not file.endswith(".lean"):
        raise UserError(f"expected a .lean file, got {file!r}")
    if os.path.isabs(file):
        d = os.path.dirname(os.path.realpath(file))
        while True:
            if any(os.path.isfile(os.path.join(d, f)) for f in LAKEFILES):
                root = d
                break
            parent = os.path.dirname(d)
            if parent == d:
                raise UserError(f"{file} is not inside a Lake project (no lakefile found above it)")
            d = parent
    else:
        root = os.path.realpath(default_project)
        if not any(os.path.isfile(os.path.join(root, f)) for f in LAKEFILES):
            raise UserError(f"default project {root} has no lakefile")
    path = os.path.realpath(os.path.join(root, file))
    if not path.startswith(root + os.sep):
        raise UserError(f"{file} escapes the project {root}")
    return root, os.path.relpath(path, root)


# ---------------------------------------------------------------- positions

def utf16_len(s):
    """LSP columns count UTF-16 code units; astral characters (𝓒, 𝔸) count 2."""
    return sum(2 if ord(c) > 0xFFFF else 1 for c in s)


def goal_column(line_text):
    """Column (UTF-16) of the first non-blank character: the state BEFORE the line's tactic."""
    return utf16_len(line_text[: len(line_text) - len(line_text.lstrip())])


# ---------------------------------------------------------------- splicing

_SORRY = re.compile(r"\bsorry\b")


def splice(text, line, candidate):
    """Put `candidate` (one or more tactic lines) at 1-based `line` of `text`.

    If the line contains `sorry`, only that token is replaced: a candidate may
    span several lines only when the `sorry` stands alone on its line (it then
    inherits the line's indentation). Otherwise the line's whole content is
    replaced, keeping its indentation.
    Returns (new_text, first_line, last_line, end_col): the 1-based span the candidate
    occupies, and the UTF-16 column just past the candidate's own last character. That
    column, not the line's end, is where the goals AFTER the candidate are read: text
    that followed the `sorry` (e.g. `sorry⟩`) is outside any tactic block.
    """
    lines = text.split("\n")
    if not 1 <= line <= len(lines):
        raise UserError(f"line {line} is outside the file (1..{len(lines)})")
    cand = [l.rstrip() for l in candidate.strip("\n").split("\n")]
    while cand and not cand[-1].strip():
        cand.pop()
    if not cand or not cand[0].strip():
        raise UserError("empty tactic candidate")
    # Normalise the candidate's own indentation so its first line sits at column 0.
    lead = len(cand[0]) - len(cand[0].lstrip())
    cand = [l[lead:] if l[:lead].strip() == "" else l.lstrip() for l in cand]

    target = lines[line - 1]
    indent = target[: len(target) - len(target.lstrip())]
    m = _SORRY.search(target)
    if m and target[: m.start()].strip():
        # `... := by sorry` style: inline slot.
        if len(cand) > 1:
            raise UserError(
                f"line {line} has `sorry` after other code; an inline slot takes a one-line "
                "candidate. Chain tactics with `;`, or first move `sorry` onto its own line.")
        head = target[: m.start()] + cand[0]
        new, end_col = [head + target[m.end():]], utf16_len(head)
    else:
        new = [indent + cand[0]] + [indent + l if l.strip() else "" for l in cand[1:]]
        end_col = utf16_len(new[-1])
        if m:
            new[-1] += target[m.end():]
    out = lines[: line - 1] + new + lines[line:]
    return "\n".join(out), line, line + len(new) - 1, end_col


# ---------------------------------------------------------------- diagnostics

_SEV = {1: "error", 2: "warning", 3: "info", 4: "hint"}


def normalise_diagnostics(raw):
    """LSP diagnostics -> [{line, col, end_line, severity, message}], 1-based lines."""
    out = []
    for d in raw or []:
        r = d.get("range") or d.get("fullRange") or {}
        s, e = r.get("start", {}), r.get("end", r.get("start", {}))
        out.append({"line": s.get("line", 0) + 1, "col": s.get("character", 0),
                    "end_line": e.get("line", 0) + 1,
                    "severity": _SEV.get(d.get("severity"), "info"),
                    "message": d.get("message", "")})
    out.sort(key=lambda d: (d["line"], d["col"]))
    return out


def source_snapshot(root):
    """{relative .lean path: (mtime_ns, size)} for the project's own sources (not .lake)."""
    snap = {}
    for d, dirs, files in os.walk(root):
        dirs[:] = [x for x in dirs if not x.startswith(".")]
        for f in files:
            if f.endswith(".lean"):
                full = os.path.join(d, f)
                try:
                    st = os.stat(full)
                except OSError:
                    continue
                snap[os.path.relpath(full, root)] = (st.st_mtime_ns, st.st_size)
    return snap


def dependencies_changed(before, after, own_rel):
    """True if any source other than the open document itself changed, appeared or vanished.

    The Lean server keeps an open document's imports as they were at open time and
    does NOT notice edits to them on its own (measured: no "Imports are out of date"
    message arrives), so the caller must reopen the document when this is True.
    """
    keys = (set(before) | set(after)) - {own_rel}
    return any(before.get(k) != after.get(k) for k in keys)


def is_stale_imports(diags):
    return any("Imports are out of date" in d["message"] for d in diags)


# Lean 4.35 writes "declaration uses `sorry`"; older releases wrote 'sorry'. Match both.
_USES_SORRY = re.compile(r"declaration uses [`']sorry[`']")


def uses_sorry(message):
    return bool(_USES_SORRY.search(message))


def sorry_lines(diags):
    return [d["line"] for d in diags if uses_sorry(d["message"])]


def verdict(diags, first, last, goals_after):
    """Classify one tried candidate occupying lines first..last.

    'error'    -- Lean reported an error on the candidate's own lines
    'no goals' -- it ran cleanly and nothing is left at its end
    'progress' -- it ran cleanly and goals remain (see goals_after)
    'unknown'  -- it ran cleanly but no tactic state exists at its end
    """
    if any(d["severity"] == "error" and first <= d["line"] <= last for d in diags):
        return "error"
    if goals_after is None:
        return "unknown"
    return "no goals" if not goals_after else "progress"


# ---------------------------------------------------------------- search

def search_words(query):
    words = [w.lower() for w in re.split(r"[\s,]+", query or "") if w]
    if not words:
        raise UserError("search needs at least one word, e.g. 'union comm'")
    for w in words:
        if not re.fullmatch(r"[\w.'₀-₉]+", w):
            raise UserError(f"search words are name fragments; {w!r} is not one")
    return words


def search_snippet(words, limit):
    """Lean command appended to a file (in memory) to search constants in its scope.

    Every word must occur in the full name (case-insensitive). Shortest names first.
    """
    lean_words = ", ".join('"' + w.replace("\\", "\\\\").replace('"', '\\"') + '"' for w in words)
    return f'''

open Lean Elab Command Meta in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let words : List String := [{lean_words}]
  let hits := env.constants.fold (init := (#[] : Array Name)) fun acc n _ =>
    if n.isInternal then acc
    else
      let s := n.toString.toLower
      if words.all (fun w => (s.splitOn w).length > 1) then acc.push n else acc
  let hits := hits.qsort (fun a b => a.toString.length < b.toString.length ||
    (a.toString.length == b.toString.length && a.toString < b.toString))
  let shown := hits.extract 0 {int(limit)}
  let lines ← liftTermElabM <| shown.mapM fun n => do
    let ci ← getConstInfo n
    let t ← ppExpr ci.type
    pure s!"{{n}} : {{t}}"
  logInfo m!"{SEARCH_MARK} {{hits.size}}\\n{{"\\n".intercalate lines.toList}}"
'''


def with_lean_import(text):
    """[text] with `import Lean` added first (after a leading `module` line), for the search
    snippets, which need Lean's elaborator in scope: a Mathlib file has it through its
    imports, a plain Lean file does not. In memory only. -> (text, lines added)."""
    lines = text.split("\n")
    at = 1 if lines and lines[0].strip() == "module" else 0
    return "\n".join(lines[:at] + ["import Lean"] + lines[at:]), 1


def unimported_by_file(states, hits):
    """States found with `import Lean` added: a hit from Lean's own library (Lean.*, Std.*)
    was in scope only through that import, so for the file itself it needs one."""
    added = {h["name"] for h in hits if (h.get("module") or "").split(".")[0] in ("Lean", "Std")}
    return {n: ("import" if st == "ok" and n in added else st) for n, st in states.items()}


def needs_lean_import(err):
    """Did a search snippet fail only because `Lean` is not imported?"""
    return "unknown namespace" in str(err)


def parse_search(diags, snippet_line):
    """-> (total_hits, [entry...]) from the snippet's info message, or raise with Lean's error."""
    for d in diags:
        if d["message"].startswith(SEARCH_MARK):
            head, _, body = d["message"].partition("\n")
            total = int(head.split()[1])
            return total, [l for l in body.split("\n") if l.strip()]
    errs = [d for d in diags if d["severity"] == "error" and d["line"] >= snippet_line]
    if errs:
        raise UserError("search failed inside Lean: " + errs[0]["message"])
    raise UserError("search produced no result (does the file compile up to its end?)")


# ---------------------------------------------------------------- lake build

_BUILD_DIAG = re.compile(r"^(error|warning|info): (?:\./)*(.+?\.lean):(\d+):(\d+): (.*)$")


def parse_build(output, exit_code):
    """lake build output -> {ok, errors, warnings, sorries, failed, summary}."""
    res = {"ok": exit_code == 0, "errors": [], "warnings": [], "sorries": [], "failed": [],
           "summary": ""}
    lines = output.splitlines()
    i = 0
    while i < len(lines):
        m = _BUILD_DIAG.match(lines[i])
        if m:
            sev, f, ln, col, msg = m.groups()
            # Lean continues multi-line messages on following unprefixed lines.
            j = i + 1
            while j < len(lines) and not re.match(r"^(error|warning|info|trace|✖|✔|⚠|Build|-)\b|^[✖✔⚠]", lines[j]):
                msg += "\n" + lines[j]
                j += 1
            entry = {"file": f, "line": int(ln), "col": int(col), "message": msg.strip()}
            if sev == "error":
                res["errors"].append(entry)
            elif sev == "warning":
                (res["sorries"] if uses_sorry(msg) else res["warnings"]).append(entry)
            i = j
            continue
        m = re.match(r"^✖ \[\d+/\d+\] Building (\S+)", lines[i])
        if m:
            res["failed"].append(m.group(1))
        if lines[i].startswith("Build completed") or lines[i].startswith("error: build failed"):
            res["summary"] = lines[i]
        i += 1
    if not res["summary"]:
        res["summary"] = "build succeeded" if res["ok"] else f"build failed (exit {exit_code})"
    return res


# ---------------------------------------------------------------- rendering

def _fmt_diag(d):
    return f"{d['severity']} at line {d['line']}:{d['col']}: {d['message']}"


def _fmt_goals(goals):
    if goals is None:
        return "(no tactic state here)"
    if not goals:
        return "no goals"
    return "\n\n".join(goals)


def render_check(rel, diags, goals, seconds):
    out = [f"{rel}: checked in {seconds:.1f}s"]
    errors = [d for d in diags if d["severity"] == "error"]
    sorries = sorry_lines(diags)
    if not diags:
        out.append("clean: no errors, no warnings, no sorry")
    else:
        out.append(f"{len(errors)} error(s), {len(sorries)} declaration(s) using sorry, "
                   f"{len(diags) - len(errors) - len(sorries)} other message(s)")
        out.extend(_fmt_diag(d) for d in diags)
    for ln in sorted(goals):
        out.append(f"\ngoals before line {ln}:\n{_fmt_goals(goals[ln])}")
    return "\n".join(out)


def render_try(rel, line, results, seconds):
    out = [f"{rel}: tried {len(results)} candidate(s) at line {line} in {seconds:.1f}s "
           "(in memory; nothing written)"]
    for i, r in enumerate(results, 1):
        out.append(f"\n[{i}] {r['verdict'].upper()}: {r['candidate']}")
        own = [d for d in r["diagnostics"] if r["first"] <= d["line"] <= r["last"]]
        for d in own:
            out.append("  " + _fmt_diag(d).replace("\n", "\n  "))
        if r["verdict"] != "error":
            out.append("  goals after:\n  " + _fmt_goals(r["goals_after"]).replace("\n", "\n  "))
        elsewhere = [d for d in r["diagnostics"]
                     if d["severity"] == "error" and not r["first"] <= d["line"] <= r["last"]]
        if elsewhere:
            out.append(f"  + {len(elsewhere)} error(s) elsewhere in the file, first: "
                       + _fmt_diag(elsewhere[0]).split("\n")[0])
    return "\n".join(out)


def render_search(words, total, entries):
    q = " ".join(words)
    if not total:
        return f"no constant in scope has all of: {q}"
    head = f"{total} constant(s) in scope contain all of: {q}"
    if total > len(entries):
        head += f" (showing the {len(entries)} shortest; add a word to narrow)"
    return head + "\n" + "\n".join(entries)


def render_build(res, seconds):
    out = [f"{res['summary']} ({seconds:.0f}s)"]
    for e in res["errors"]:
        out.append(f"error {e['file']}:{e['line']}:{e['col']}: {e['message']}")
    if res["sorries"]:
        out.append(f"{len(res['sorries'])} declaration(s) use sorry: "
                   + ", ".join(f"{e['file']}:{e['line']}" for e in res["sorries"]))
    for e in res["warnings"]:
        out.append(f"warning {e['file']}:{e['line']}:{e['col']}: {e['message']}")
    if res["failed"] and not res["errors"]:
        out.append("failed modules: " + ", ".join(res["failed"]))
    return "\n".join(out)


# ---------------------------------------------------------------- bridge (app-facing JSON)

def parse_goal(goal):
    """One plainGoal string -> {case, hyps: [{names, type}], target}.

    Lean prints a goal as an optional `case tag` line, one hypothesis per line
    (`a b : T`, names sharing a type grouped), then `⊢ target`. Lines indented
    under a hypothesis or the target are its continuation, kept with their breaks;
    a hypothesis printed as `h :` alone has a type that starts with a line break.
    """
    lines = goal.split("\n")
    case = None
    if lines and lines[0].startswith("case "):
        case, lines = lines[0][5:], lines[1:]
    hyps, target = [], None
    for i, line in enumerate(lines):
        if line.startswith("⊢ "):
            target = "\n".join([line[2:]] + lines[i + 1:])
            break
        if line.startswith(" ") and hyps:
            hyps[-1]["type"] += "\n" + line
            continue
        if line.endswith(" :"):  # the type did not fit: it follows on indented lines
            names, sep, typ = line[:-2], True, ""
        else:
            names, sep, typ = line.partition(" : ")
        hyps.append({"names": names.split(" ") if sep else [], "type": typ if sep else line})
    return {"case": case, "hyps": hyps, "target": target}


def _blank_comments(text):
    """Replace comment characters with spaces, keeping newlines, so line numbers hold.

    Handles nested block comments and line comments; ignores string literals
    (a `--` inside a string is rare in a declaration header).
    """
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        two = text[i:i + 2]
        if two == "/-":
            depth += 1; out.append("  "); i += 2
        elif two == "-/" and depth:
            depth -= 1; out.append("  "); i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " "); i += 1
        elif two == "--":
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j
        else:
            out.append(text[i]); i += 1
    return "".join(out)


_DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
                   r"(theorem|lemma|def|abbrev|instance|example|structure|inductive|class)\b\s*"
                   r"([^\s:({\[⦃]*)")

# Notation commands count as declarations too; their name is the first quoted token
# (`infixl:65 " ⋆ " => f` is `⋆`), so the app can list and open them.
_NOTATION = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:scoped|local)\s+)?"
                       r"(notation|infixl|infixr|infix|prefix|postfix|macro_rules|macro|syntax)\b")
_QUOTED = re.compile(r'"([^"]+)"')


def _declaration_at(line):
    """(kind, name or None) if a top-level declaration starts on this (comment-blanked) line."""
    m = _DECL.match(line)
    if m:
        return m.group(1), m.group(2) or None
    m = _NOTATION.match(line)
    if m:
        q = _QUOTED.search(line, m.end())
        return m.group(1), (q.group(1).strip() or None) if q else None
    return None


# Lines between declarations that belong to neither: a blank (or comment-only, e.g. the
# next declaration's docstring) line, an attribute line, or a command at column 0.
_BETWEEN = re.compile(r"^\s*$|^\s*@\[[^\]]*\]\s*$|^(?:end|namespace|section|open|variable|universe|"
                      r"set_option|attribute|export|mutual|noncomputable\s+section|#\w+)\b")


def declarations(text, diags):
    """Top-level declarations -> [{line, end_line, kind, name, status}], status ok|sorry|error.

    A declaration runs from its keyword line to its last line of code before the
    next declaration (or the end of the file): trailing blank lines, the next
    declaration's docstring and attributes, and commands like `end X` are not
    part of it, so an edit of the declaration cannot touch them. Its status is
    the worst diagnostic in that range.
    """
    lines = _blank_comments(text).split("\n")
    found = []
    for i, line in enumerate(lines, 1):
        d = _declaration_at(line)
        if d:
            found.append({"line": i, "kind": d[0], "name": d[1]})
    for k, d in enumerate(found):
        end = found[k + 1]["line"] - 1 if k + 1 < len(found) else len(lines)
        while end > d["line"] and _BETWEEN.match(lines[end - 1]):
            end -= 1
        d["end_line"] = end
        own = [x for x in diags if d["line"] <= x["line"] <= d["end_line"]]
        if any(x["severity"] == "error" for x in own):
            d["status"] = "error"
        elif any(uses_sorry(x["message"]) for x in own):
            d["status"] = "sorry"
        else:
            d["status"] = "ok"
    return found


def list_sources(root):
    """The project's own .lean files, relative, sorted (never .lake)."""
    return sorted(source_snapshot(root))


_MODULE_DOC = re.compile(r"/-!\s*#+\s*([^\n]+)")
_IMPORT = re.compile(r"^import\s+(\S+)", re.M)


def file_overview(root):
    """What the landing page shows per source, from the text alone (no Lean run).

    -> {"files": [{path, title, decls, sorries, empty, role}]}, role one of
    "root" (a library root: `<Lib>.lean` for a lakefile [[lean_lib]] or a `<Lib>/` folder),
    "imported" (a root imports it), "unimported" (a library file no root
    imports: not in `lake build`), "other". `sorries` counts `sorry` tokens
    outside comments; `title` is the module doc's first heading.
    """
    files = list_sources(root)
    texts = {}
    for rel in files:
        with open(os.path.join(root, rel), encoding="utf-8", errors="replace") as f:
            texts[rel] = f.read()
    libs = set(library_names(root, files))
    roots = [f for f in files if "/" not in f and f[:-len(".lean")] in libs]
    imported = {m for r in roots for m in _IMPORT.findall(texts[r])}
    out = []
    for rel in files:
        text = texts[rel]
        code = _blank_comments(text)
        t = _MODULE_DOC.search(text)
        mod = module_of(rel)
        if rel in roots:
            role = "root"
        elif "/" in rel and rel.split("/")[0] in libs:
            role = "imported" if mod in imported else "unimported"
        else:
            role = "other"
        out.append({"path": rel, "title": t.group(1).strip() if t else None,
                    "decls": sum(1 for l in code.split("\n") if _declaration_at(l)),
                    "sorries": len(_SORRY.findall(code)), "empty": not text.strip(), "role": role})
    return {"files": out}


ABBREV_FILE = os.path.join(".leanwb", "abbreviations.json")
_ABBREV_NAME = re.compile(r"^[^\s\\]{1,32}$")


def read_abbreviations(root):
    """The project's own `\\`-abbreviations ({name: symbol}), from .leanwb/abbreviations.json."""
    path = os.path.join(root, ABBREV_FILE)
    try:
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
    except FileNotFoundError:
        return {}
    except ValueError as e:
        raise UserError(f"{ABBREV_FILE} is not valid JSON: {e}")
    if not isinstance(data, dict) or not all(isinstance(k, str) and isinstance(v, str) for k, v in data.items()):
        raise UserError(f"{ABBREV_FILE} must be an object of name -> symbol strings")
    return data


def abbreviation_request(body):
    """Validate a bridge /abbreviation body -> (name, symbol). An empty symbol removes the name."""
    if not isinstance(body, dict):
        raise UserError("body must be a JSON object")
    name, symbol = body.get("name"), body.get("symbol")
    if not isinstance(name, str) or not _ABBREV_NAME.match(name):
        raise UserError("`name` must be 1-32 characters, no spaces or backslash (typed after `\\`)")
    if not isinstance(symbol, str) or len(symbol) > 32 or "\n" in symbol:
        raise UserError("`symbol` must be a one-line string of at most 32 characters")
    return name, symbol


def write_abbreviation(root, name, symbol):
    """Set (or, with an empty symbol, remove) one project abbreviation. Only this one file is written.

    Returns the whole table after the change.
    """
    table = read_abbreviations(root)
    if symbol:
        table[name] = symbol
    else:
        table.pop(name, None)
    path = os.path.join(root, ABBREV_FILE)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".leanwb-tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(dict(sorted(table.items())), f, ensure_ascii=False, indent=1)
        f.write("\n")
    os.replace(tmp, path)
    return table


def check_request(body):
    """Validate a bridge /check body -> (file, text or None, goals_at, goals_after).

    goals_at: the state before each line (at its first non-space column).
    goals_after: the state at the end of each line, i.e. after its tactic.
    Refuses rather than guesses.
    """
    if not isinstance(body, dict):
        raise UserError("body must be a JSON object")
    file, text = body.get("file"), body.get("text")
    goals_at, goals_after = body.get("goals_at", []), body.get("goals_after", [])
    if not isinstance(file, str) or not file:
        raise UserError("`file` (a project-relative .lean path) is required")
    if os.path.isabs(file):
        raise UserError("`file` must be relative to the project; the app cannot reach other projects")
    if text is not None and not isinstance(text, str):
        raise UserError("`text` must be a string when given")
    for name, v in (("goals_at", goals_at), ("goals_after", goals_after)):
        if not isinstance(v, list) or not all(isinstance(x, int) and not isinstance(x, bool)
                                              and x >= 1 for x in v):
            raise UserError(f"`{name}` must be a list of 1-based line numbers")
    if len(goals_at) + len(goals_after) > 50:
        raise UserError("at most 50 goal lines per request")
    return file, text, goals_at, goals_after


def save_request(body):
    """Validate a bridge /save body -> (file, text, base).

    `base` is the file's text as the app last loaded it from disk. The save only
    happens if the disk still holds exactly that (see write_if_unchanged).
    """
    if not isinstance(body, dict):
        raise UserError("body must be a JSON object")
    file, text, base = body.get("file"), body.get("text"), body.get("base")
    if not isinstance(file, str) or not file or os.path.isabs(file):
        raise UserError("`file` (a project-relative .lean path) is required")
    if not isinstance(text, str) or not isinstance(base, str):
        raise UserError("`text` and `base` (the text as loaded from disk) are both required strings")
    return file, text, base


def write_if_unchanged(root, rel, text, base):
    """Write `text` to an existing project source, only if the disk still holds `base`.

    Refuses new files and anything list_sources does not list (e.g. `.lake/`), so
    the app can only change a source it could open. Git is the undo; nothing is
    committed here. The write is atomic (temp file + rename) and keeps the mode.
    Returns the number of bytes written.
    """
    if rel not in list_sources(root):
        raise UserError(f"{rel} is not an existing source of this project; the app only saves files it opened")
    path = os.path.join(root, rel)
    with open(path, encoding="utf-8") as f:
        disk = f.read()
    if disk != base:
        raise UserError(f"{rel} changed on disk since the app loaded it; nothing was written. "
                        "Revert in the app to load the disk version, then redo the edit")
    data = text.encode("utf-8")
    tmp = path + ".leanwb-tmp"
    with open(tmp, "wb") as f:
        f.write(data)
    os.chmod(tmp, os.stat(path).st_mode & 0o7777)
    os.replace(tmp, path)
    return len(data)


def create_request(body):
    """Validate a bridge /create body -> (file, text). `text` is the new file's content."""
    if not isinstance(body, dict):
        raise UserError("body must be a JSON object")
    file, text = body.get("file"), body.get("text")
    if not isinstance(file, str) or not file or os.path.isabs(file):
        raise UserError("`file` (a project-relative .lean path) is required")
    if not isinstance(text, str):
        raise UserError("`text` (the new file's content) is required")
    return file, text


_MODULE_PART = re.compile(r"^[A-Z][A-Za-z0-9_]*$")


def module_of(rel):
    """`A/B/C.lean` -> `A.B.C`, or None if a component is not a plain Lean module name."""
    if not rel.endswith(".lean"):
        return None
    parts = rel[:-len(".lean")].split("/")
    return ".".join(parts) if all(_MODULE_PART.match(p) for p in parts) else None


def add_import(text, module):
    """`text` with `import <module>` after its last import line (or first, if none).

    Unchanged if it already imports the module.
    """
    lines = text.split("\n")
    imports = [i for i, l in enumerate(lines) if re.match(r"^import\s", l)]
    if any(lines[i].split()[1:] == [module] for i in imports):
        return text
    at = imports[-1] + 1 if imports else 0
    return "\n".join(lines[:at] + [f"import {module}"] + lines[at:])


def create_source(root, rel, text):
    """Create a new project source and register it in its library's root file.

    Only a new file, never an overwrite; only inside a library's folder (a lakefile
    [[lean_lib]] or a folder that already holds sources: nothing lands in `.lake/`);
    each path component must be a Lean module name, so the file can be imported.
    Missing directories below the library directory are made (a new namespace
    folder). If the library root `<Lib>.lean` exists, `import <module>` is added
    to it, so `lake build` and CI see the new file. Nothing is committed.
    Returns (bytes written, the root file changed or None).
    """
    module = module_of(rel)
    if module is None or "/" not in rel:
        raise UserError(f"{rel}: a new file must be <Library>/<Name>.lean with capitalised "
                        "module names (letters, digits, _)")
    sources = list_sources(root)
    libs = set(library_names(root, sources))
    lib = rel.split("/")[0]
    if lib not in libs:
        raise UserError(f"{rel}: new files go in an existing library folder ({', '.join(sorted(libs)) or 'none'})")
    path = os.path.join(root, rel)
    if os.path.exists(path):
        raise UserError(f"{rel} already exists; nothing was written")
    os.makedirs(os.path.dirname(path), exist_ok=True)
    data = text.encode("utf-8")
    with open(path, "xb") as f:  # x: never replace a file that appeared meanwhile
        f.write(data)
    root_rel = lib + ".lean"
    if root_rel not in sources:
        return len(data), None
    root_path = os.path.join(root, root_rel)
    with open(root_path, encoding="utf-8") as f:
        old = f.read()
    new = add_import(old, module)
    if new != old:
        write_if_unchanged(root, root_rel, new, old)
    return len(data), root_rel


def complete_request(body):
    """Validate a bridge /complete body -> (file, text, line, col). `col` is a UTF-16 column."""
    if not isinstance(body, dict):
        raise UserError("body must be a JSON object")
    file, text, line, col = body.get("file"), body.get("text"), body.get("line"), body.get("col")
    if not isinstance(file, str) or not file or os.path.isabs(file):
        raise UserError("`file` (a project-relative .lean path) is required")
    if not isinstance(text, str):
        raise UserError("`text` (the file with the line being typed) is required")
    for name, v in (("line", line), ("col", col)):
        if not isinstance(v, int) or isinstance(v, bool) or v < (1 if name == "line" else 0):
            raise UserError(f"`{name}` must be a {'1-based line' if name == 'line' else '0-based UTF-16 column'}")
    return file, text, line, col


_IDENT_CHAR = re.compile(r"[\w'!?₀-₉ₐ-ₜᵢ-ᵪ]")


def completion_fragment(line_text, col):
    """The identifier piece being typed at UTF-16 column `col`: the characters after the
    last `.` of the name before the cursor ("hD.tr" -> "tr", "Finset.union_co" -> "union_co",
    "(h" -> "h")."""
    before, units = [], 0
    for ch in line_text:
        if units >= col:
            break
        before.append(ch)
        units += utf16_len(ch)
    frag = []
    for ch in reversed(before):
        if not _IDENT_CHAR.match(ch):
            break
        frag.append(ch)
    return "".join(reversed(frag))


def rank_completions(items, fragment, limit=20):
    """Lean's completion is fuzzy and unordered (a bare `h` gives ~16k names). Keep names
    whose last component starts with `fragment`, locals (LSP kind 6) first, then by
    length; if none start with it, those that contain it. -> [{label, kind}]"""
    frag = fragment.lower()
    def last(label):
        return label.rsplit(".", 1)[-1].lower()
    starts = [i for i in items if last(i["label"]).startswith(frag)]
    pool = starts or [i for i in items if frag in last(i["label"])]
    pool.sort(key=lambda i: (i.get("kind") != 6, len(i["label"]), i["label"]))
    seen, out = set(), []
    for i in pool:
        if i["label"] not in seen:
            seen.add(i["label"])
            out.append({"label": i["label"], "kind": i.get("kind")})
        if len(out) >= limit:
            break
    return out


def end_column(line_text):
    """UTF-16 column just past a line's last non-space character: where 'after this tactic' is read."""
    return utf16_len(line_text.rstrip())


def check_payload(rel, text, diags, goals, seconds, goals_after=None, tokens=None):
    """What the app gets back from /check: everything needed to draw the file, as data."""
    return {
        "file": rel,
        "seconds": round(seconds, 2),
        "text": text,
        "diagnostics": diags,
        "declarations": declarations(text, diags),
        "goals": _goal_entries(goals),
        "goals_after": _goal_entries(goals_after or {}),
        "tokens": tokens or [],
    }


# Lean's semantic token types the app colours, by the app's name for them. Lean core
# emits only these; any other type (from a user extension) is dropped.
TOKEN_KINDS = {"keyword": "keyword", "variable": "variable", "property": "property",
               "function": "function", "leanSorryLike": "sorry"}


def decode_tokens(data, token_types):
    """LSP semanticTokens `data` (5 relative integers per token) -> [[line, col, length, kind]].

    `line` is 1-based, `col` and `length` are UTF-16 units, as every position the app
    sends. `token_types` is the server's legend: the type numbers index into it."""
    if not data or len(data) % 5:
        return []
    out, line, col = [], 0, 0
    for i in range(0, len(data), 5):
        dl, dc, n, ty, _ = data[i:i + 5]
        if dl:
            line, col = line + dl, dc
        else:
            col += dc
        name = token_types[ty] if 0 <= ty < len(token_types) else None
        if name in TOKEN_KINDS and n > 0:
            out.append([line + 1, col, n, TOKEN_KINDS[name]])
    return out


def _goal_entries(goals):
    return [{"line": ln, "goals": None if goals[ln] is None else [parse_goal(g) for g in goals[ln]]}
            for ln in sorted(goals)]


# ---------------------------------------------------------------- API search (Loogle, LeanSearch)
#
# The bridge asks the two public services and then checks every hit against the
# project's own environment: both index current Mathlib, while a project pins a
# release, so a hit can be renamed, new, or merely not imported by the file.

LOOGLE_URL = "https://loogle.lean-lang.org/json"
LEANSEARCH_URL = "https://leansearch.net/search"
API_ENGINES = ("loogle", "leansearch")
API_MAX_HITS = 30
EXISTS_MARK = "LEANMCP_EXISTS"
_LEAN_NAME = re.compile(r"^[A-Za-z_Ͱ-Ͽἀ-῿℀-⅏][\w'!?Ͱ-Ͽἀ-῿₀-ₜ℀-⅏]*"
                        r"(\.[A-Za-z_Ͱ-Ͽἀ-῿℀-⅏0-9][\w'!?Ͱ-Ͽἀ-῿₀-ₜ℀-⅏]*)*$")
_MODULE = re.compile(r"^[A-Za-z_][\w']*(\.[A-Za-z_][\w']*)*$")


def api_search_request(body):
    """Validate a bridge /search body -> (engine, query, file or None, text or None).

    `file` (and its unsaved `text`) set the scope the hits are checked in: the file's
    imports decide between ok and import. Without it, the project's root module."""
    if not isinstance(body, dict):
        raise UserError("body must be a JSON object")
    engine, query, file, text = body.get("engine"), body.get("query"), body.get("file"), body.get("text")
    if engine not in API_ENGINES:
        raise UserError("`engine` must be one of: " + ", ".join(API_ENGINES))
    if not isinstance(query, str) or not query.strip() or len(query) > 500:
        raise UserError("`query` must be a non-empty string of at most 500 characters")
    if file is not None and not isinstance(file, str):
        raise UserError("`file` must be a string")
    if text is not None and (file is None or not isinstance(text, str)):
        raise UserError("`text` must be a string, and needs `file`")
    return engine, query.strip(), file, text


def loogle_url(query):
    from urllib.parse import quote
    return LOOGLE_URL + "?q=" + quote(query, safe="")


def leansearch_body(query, n=API_MAX_HITS):
    return json.dumps({"query": [query], "num_results": int(n)}).encode("utf-8")


def _hit(name, type_, module, doc=None, informal=None):
    return {"name": name, "type": " ".join((type_ or "").split()), "module": module,
            "doc": doc or None, "informal": informal or None}


def parse_loogle(obj):
    """Loogle's JSON -> {count, hits, error, suggestions}. A bad query is data, not an exception."""
    if not isinstance(obj, dict):
        raise UserError("Loogle answered something that is not a JSON object")
    if "error" in obj:
        sugg = [s for s in obj.get("suggestions") or [] if isinstance(s, str)]
        return {"count": 0, "hits": [], "error": str(obj["error"]).strip(), "suggestions": sugg[:5]}
    hits = [_hit(h.get("name"), h.get("type"), h.get("module"), h.get("doc"))
            for h in obj.get("hits") or [] if isinstance(h, dict) and isinstance(h.get("name"), str)]
    return {"count": int(obj.get("count") or len(hits)), "hits": hits[:API_MAX_HITS],
            "error": None, "suggestions": []}


def parse_leansearch(obj):
    """LeanSearch's JSON ([[{result: {...}}]], one list per query) -> {count, hits, error, suggestions}."""
    if not isinstance(obj, list) or not obj or not isinstance(obj[0], list):
        raise UserError("LeanSearch answered in an unexpected shape")
    hits = []
    for x in obj[0]:
        r = x.get("result") if isinstance(x, dict) else None
        if not isinstance(r, dict) or not isinstance(r.get("name"), list):
            continue
        hits.append(_hit(".".join(map(str, r["name"])), r.get("type") or r.get("signature"),
                         ".".join(map(str, r.get("module_name") or [])), r.get("docstring"),
                         r.get("informal_name")))
    return {"count": len(hits), "hits": hits[:API_MAX_HITS], "error": None, "suggestions": []}


def exists_snippet(hits):
    """Lean command appended to a file (in memory): for each hit, whether its name is in scope
    ("ok"), exists in its module's compiled file but that module is not imported ("import"),
    or neither ("missing"). Hits whose name or module this cannot express are left out."""
    pairs = [(h["name"], h["module"]) for h in hits
             if _LEAN_NAME.match(h["name"] or "") and _MODULE.match(h["module"] or "")]
    if not pairs:
        return None
    q = lambda s: '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'
    items = ", ".join(f"({q(n)}, {q(m)})" for n, m in pairs)
    return f'''

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let qs : List (String × String) := [{items}]
  let mut out : Array String := #["{EXISTS_MARK}"]
  for (s, m) in qs do
    let n := s.toName
    if env.contains n then out := out.push s!"ok {{s}}"
    else
      let r ← (show IO String from do
        try
          let p ← findOLean m.toName
          if !(← p.pathExists) then return "missing"
          let (d, _) ← readModuleData p
          return if d.constNames.contains n then "import" else "missing"
        catch _ => return "missing")
      out := out.push s!"{{r}} {{s}}"
  logInfo (String.intercalate "\\n" out.toList)
'''


def parse_exists(diags, snippet_line):
    """-> {name: "ok" | "import" | "missing"} from the snippet's info message, or raise."""
    for d in diags:
        if d["message"].startswith(EXISTS_MARK):
            out = {}
            for l in d["message"].split("\n")[1:]:
                state, _, name = l.partition(" ")
                if state in ("ok", "import", "missing") and name:
                    out[name] = state
            return out
    errs = [d for d in diags if d["severity"] == "error" and d["line"] >= snippet_line]
    if errs:
        raise UserError("the check against your Mathlib failed inside Lean: " + errs[0]["message"])
    raise UserError("the check against your Mathlib produced no result (does the file compile up to its end?)")


def mark_hits(hits, states):
    """Each hit gains `state`: ok / import / missing, or unchecked when Lean was not asked."""
    return [dict(h, state=states.get(h["name"], "unchecked")) for h in hits]


# ---------------------------------------------------------------- toolbox (pinned lemmas)

TOOLBOX_FILE = os.path.join(".leanwb", "toolbox.json")


def read_toolbox(root):
    """The package's pinned lemmas, [{name, module, type}], in pinning order."""
    path = os.path.join(root, TOOLBOX_FILE)
    try:
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
    except FileNotFoundError:
        return []
    except ValueError as e:
        raise UserError(f"{TOOLBOX_FILE} is not valid JSON: {e}")
    ok = isinstance(data, list) and all(isinstance(e, dict) and isinstance(e.get("name"), str) for e in data)
    if not ok:
        raise UserError(f"{TOOLBOX_FILE} must be a list of {{name, module, type}} objects")
    return data


def toolbox_request(body):
    """Validate a bridge /toolbox body -> (entry {name, module, type}, pinned)."""
    if not isinstance(body, dict):
        raise UserError("body must be a JSON object")
    name, module, type_, pinned = body.get("name"), body.get("module", ""), body.get("type", ""), body.get("pinned")
    if not isinstance(name, str) or not _LEAN_NAME.match(name) or len(name) > 200:
        raise UserError("`name` must be a Lean name")
    if not isinstance(module, str) or (module and not _MODULE.match(module)):
        raise UserError("`module` must be a module name")
    if not isinstance(type_, str) or len(type_) > 2000:
        raise UserError("`type` must be a string of at most 2000 characters")
    if not isinstance(pinned, bool):
        raise UserError("`pinned` must be true or false")
    return {"name": name, "module": module, "type": " ".join(type_.split())}, pinned


def write_toolbox(root, entry, pinned):
    """Pin (append, once) or unpin one lemma. Only this one file is written. Returns the list."""
    box = [e for e in read_toolbox(root) if e.get("name") != entry["name"]]
    if pinned:
        box.append(entry)
    path = os.path.join(root, TOOLBOX_FILE)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".leanwb-tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(box, f, ensure_ascii=False, indent=1)
        f.write("\n")
    os.replace(tmp, path)
    return box


# ---------------------------------------------------------------- source of a lemma (read-only)

def source_request(body):
    """Validate a bridge /source body -> (module, name)."""
    if not isinstance(body, dict):
        raise UserError("body must be a JSON object")
    module, name = body.get("module"), body.get("name", "")
    if not isinstance(module, str) or not _MODULE.match(module):
        raise UserError("`module` must be a module name such as Mathlib.Order.Lattice")
    if not isinstance(name, str) or (name and not _LEAN_NAME.match(name)):
        raise UserError("`name` must be a Lean name")
    return module, name


def module_candidates(root, module):
    """Where a module's source can be: the project, then each package under .lake/packages."""
    rel = os.path.join(*module.split(".")) + ".lean"
    out = [os.path.join(root, rel)]
    pk = os.path.join(root, ".lake", "packages")
    if os.path.isdir(pk):
        out += [os.path.join(pk, p, rel) for p in sorted(os.listdir(pk))]
    return out


_DECL_KW = r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|axiom|opaque)"


def declaration_line(text, name):
    """1-based line where [name] is declared in [text], by its last component (and the namespace
    when the source spells it out); 1 when not found. A scroll target, not a proof of identity."""
    if not name:
        return 1
    last = name.split(".")[-1]
    full = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|unsafe|partial)\s+)*"
                      + _DECL_KW + r"\s+(?:[\w'.]*\.)?" + re.escape(last) + r"(?![\w'!?])")
    lines = text.split("\n")
    exact = [i for i, l in enumerate(lines) if full.match(l) and (name in l or "." not in name)]
    loose = [i for i, l in enumerate(lines) if full.match(l)]
    hit = (exact or loose or [0])[0]
    return hit + 1


# ---------------------------------------------------------------- packages and libraries
#
# A package is a folder with a lakefile; its libraries are its [[lean_lib]] targets
# (plus any top-level folder that holds sources, for a lakefile this cannot read);
# its dependencies come from lake-manifest.json and live in .lake/packages/<name>.

_LEAN_LIB = re.compile(r"^\s*(@\[[^\]]*\]\s*)?lean_lib\s+«?([A-Za-z_][\w']*)»?", re.M)


def lakefile_of(root):
    for n in ("lakefile.toml", "lakefile.lean"):
        if os.path.isfile(os.path.join(root, n)):
            return n
    return None


def lakefile_libs(root):
    """-> (library names in lakefile order, default target names). Empty when unreadable."""
    lf = lakefile_of(root)
    if lf is None:
        return [], []
    path = os.path.join(root, lf)
    try:
        if lf == "lakefile.toml":
            import tomllib
            with open(path, "rb") as f:
                d = tomllib.load(f)
            libs = [l["name"] for l in d.get("lean_lib", []) if isinstance(l, dict) and isinstance(l.get("name"), str)]
            dt = [t for t in d.get("defaultTargets", []) if isinstance(t, str)]
            return libs, dt
        with open(path, encoding="utf-8") as f:
            text = f.read()
    except (OSError, ValueError):
        return [], []
    libs, dt = [], []
    for m in _LEAN_LIB.finditer(text):
        if m.group(2) not in libs:
            libs.append(m.group(2))
        if m.group(1) and "default_target" in m.group(1):
            dt.append(m.group(2))
    return libs, dt


def main_library(package, libs, default_targets):
    """The library a dependency's card stands for: a default target, else the one named like
    the package, else the first that is not a test library."""
    for l in libs:
        if l in default_targets:
            return l
    for l in libs:
        if l.lower() == package.lower():
            return l
    rest = [l for l in libs if not l.lower().endswith("test")]
    return (rest or libs or [None])[0]


def library_names(root, sources=None):
    """The package's libraries: lakefile targets first, then source folders not declared."""
    declared, _ = lakefile_libs(root)
    sources = list_sources(root) if sources is None else sources
    folders = sorted({s.split("/")[0] for s in sources if "/" in s and _MODULE_PART.match(s.split("/")[0])})
    return declared + [f for f in folders if f not in declared]


def library_of(rel, libs):
    """The library a source belongs to (`Lib.lean` or `Lib/...`), or None."""
    top = rel.split("/")[0]
    if "/" not in rel:
        top = top[:-len(".lean")] if top.endswith(".lean") else top
    return top if top in libs else None


def read_manifest(root):
    """lake-manifest.json -> [{name, rev, inputRev}] (empty when there is none)."""
    try:
        with open(os.path.join(root, "lake-manifest.json"), encoding="utf-8") as f:
            m = json.load(f)
    except (OSError, ValueError):
        return []
    out = []
    for p in m.get("packages", []) if isinstance(m, dict) else []:
        if isinstance(p, dict) and isinstance(p.get("name"), str):
            out.append({"name": p["name"], "rev": (p.get("rev") or "")[:7], "inputRev": p.get("inputRev")})
    return out


def count_sources(folder):
    n = 0
    for d, dirs, fs in os.walk(folder):
        dirs[:] = [x for x in dirs if x != ".lake"]
        n += sum(1 for f in fs if f.endswith(".lean"))
    return n


def dependency_cards(root, count=count_sources):
    """-> [{name, library, rev, inputRev, files}] for each dependency present in .lake/packages."""
    out = []
    for p in read_manifest(root):
        pdir = os.path.join(root, ".lake", "packages", p["name"])
        if not os.path.isdir(pdir):
            continue
        libs, dt = lakefile_libs(pdir)
        lib = main_library(p["name"], libs, dt)
        files = count(os.path.join(pdir, lib)) + (1 if lib and os.path.isfile(os.path.join(pdir, lib + ".lean")) else 0) if lib else 0
        out.append(dict(p, library=lib, files=files))
    return out


def toolchain_of(root):
    try:
        with open(os.path.join(root, "lean-toolchain"), encoding="utf-8") as f:
            t = f.read().strip()
        return t.split(":")[-1] or None
    except OSError:
        return None


def package_overview(root):
    """A package for the landing page (no Lean run, no git): its libraries, each with the
    overview of its own files, and the sources that belong to no library."""
    ov = file_overview(root)["files"]
    libs = library_names(root, [f["path"] for f in ov])
    by_lib = {l: [] for l in libs}
    loose = []
    for f in ov:
        l = library_of(f["path"], libs)
        (by_lib[l] if l else loose).append(f)
    return {"name": os.path.basename(root), "toolchain": toolchain_of(root), "lakefile": lakefile_of(root),
            "libraries": [{"name": l, "root": l + ".lean", "files": by_lib[l]} for l in libs],
            "loose": loose}


def find_packages(base):
    """Folders directly under [base] that hold a lakefile, sorted by name."""
    try:
        names = sorted(os.listdir(base))
    except OSError:
        return []
    return [n for n in names if not n.startswith(".") and lakefile_of(os.path.join(base, n))]


def parse_git_status(porcelain_v2):
    """`git status --porcelain=v2 --branch` -> {branch, changed, ahead, behind}."""
    st = {"branch": None, "changed": 0, "ahead": 0, "behind": 0}
    for l in porcelain_v2.splitlines():
        if l.startswith("# branch.head "):
            st["branch"] = l.split(" ", 2)[2]
        elif l.startswith("# branch.ab "):
            a, b = l.split()[2:4]
            st["ahead"], st["behind"] = int(a), -int(b)
        elif l and not l.startswith("#"):
            st["changed"] += 1
    return st


def parse_ci(gh_json):
    """`gh run list -L 1 --json status,conclusion,createdAt,headSha,workflowName` -> the last run or None."""
    try:
        runs = json.loads(gh_json)
    except ValueError:
        return None
    if not isinstance(runs, list) or not runs or not isinstance(runs[0], dict):
        return None
    r = runs[0]
    return {"status": r.get("status"), "conclusion": r.get("conclusion") or None, "at": r.get("createdAt"),
            "sha": (r.get("headSha") or "")[:7], "workflow": r.get("workflowName")}


# ---------------------------------------------------------------- a new library (+ lean_lib)

def library_request(body):
    """Validate a bridge /library body -> the new library's name."""
    if not isinstance(body, dict):
        raise UserError("body must be a JSON object")
    name = body.get("name")
    if not isinstance(name, str) or not _MODULE_PART.match(name) or len(name) > 64:
        raise UserError("`name` must be a capitalised Lean module name (letters, digits, _)")
    return name


_DEFAULT_TARGETS = re.compile(r"^(defaultTargets\s*=\s*\[)([^\]]*)(\])", re.M)


def add_library(root, name):
    """Declare a new [[lean_lib]] `name` in lakefile.toml, add it to defaultTargets (so
    `lake build` and CI build it), and create its root file `<name>.lean`. Writes only
    those two files: the root file is new (never an overwrite), the lakefile changes only
    if it still holds what was read. lakefile.lean is refused: it is code, not data.
    Returns (lakefile, root file)."""
    lf = lakefile_of(root)
    if lf != "lakefile.toml":
        raise UserError(f"only a lakefile.toml can be extended from the app (this package has {lf or 'no lakefile'})")
    libs = library_names(root)
    if name in libs:
        raise UserError(f"{name} is already a library of this package")
    root_rel = name + ".lean"
    for taken in (root_rel, name):
        if os.path.exists(os.path.join(root, taken)):
            raise UserError(f"{taken} already exists; nothing was written")
    with open(os.path.join(root, lf), encoding="utf-8") as f:
        old = f.read()
    new = old.rstrip("\n") + f'\n\n[[lean_lib]]\nname = "{name}"\n'
    m = _DEFAULT_TARGETS.search(new)
    if m:
        items = m.group(2).strip()
        new = new[:m.start()] + m.group(1) + (items + ", " if items else "") + f'"{name}"' + m.group(3) + new[m.end():]
    import tomllib
    try:
        d = tomllib.loads(new)
    except ValueError as e:
        raise UserError(f"the new lakefile would not parse ({e}); nothing was written")
    if name not in [l.get("name") for l in d.get("lean_lib", [])]:
        raise UserError("the new library did not land in the lakefile; nothing was written")
    data = f"/-!\n# {name}\n\nThe root of the {name} library: it imports each of its modules.\n-/\n".encode("utf-8")
    path = os.path.join(root, root_rel)
    with open(path, "xb") as f:
        f.write(data)
    try:
        _replace_lakefile(root, lf, new, old)
    except Exception:
        os.remove(path)
        raise
    return lf, root_rel


def _replace_lakefile(root, lf, text, base):
    """Atomically replace the lakefile, only if the disk still holds [base]; keeps the mode."""
    path = os.path.join(root, lf)
    with open(path, encoding="utf-8") as f:
        if f.read() != base:
            raise UserError(f"{lf} changed on disk meanwhile; nothing was written")
    tmp = path + ".leanwb-tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(text)
    os.chmod(tmp, os.stat(path).st_mode & 0o7777)
    os.replace(tmp, path)
