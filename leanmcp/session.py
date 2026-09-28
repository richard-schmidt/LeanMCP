"""A warm Lean server behind four operations. Moves values; core.py decides.

The stateless contract holds: every operation takes the full text it is about
(or reads it from disk at call time) and returns a result that depends only on
that text and the built dependencies. The server kept between calls is a cache:
it only makes the second call fast. If it dies, the next call starts a new one.
"""
import json
import os
import subprocess
import threading
import time
import urllib.error
import urllib.request
from urllib.parse import urlsplit

from . import core
from .lsp import LeanServer, ServerDied, lean_env

MAX_OPEN_DOCS = 2      # ~350-400 MB anon each, measured on a phone
IDLE_SECONDS = 15 * 60  # release the memory when nobody is using it


def fetch_json(url, data=None, timeout=25):
    """GET (or POST [data]) a JSON API. Network failures become UserError: they are data."""
    host = urlsplit(url).netloc
    req = urllib.request.Request(url, data=data, headers={
        "User-Agent": "lean-workbench-bridge (lean-mcp)", "Accept": "application/json",
        "Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return json.loads(r.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        raise core.UserError(f"{host} answered HTTP {e.code}")
    except (urllib.error.URLError, TimeoutError, OSError) as e:
        raise core.UserError(f"could not reach {host}: {getattr(e, 'reason', e)}")
    except ValueError:
        raise core.UserError(f"{host} did not answer JSON")


class Session:
    def __init__(self, default_project, idle_seconds=IDLE_SECONDS):
        self.default_project = default_project
        self.idle_seconds = idle_seconds
        self.server = None
        self.docs = {}  # uri -> version, in open order (LRU at the front)
        self.opened_with = {}  # uri -> source snapshot when the document was opened
        self.lock = threading.RLock()
        self.last_used = time.time()
        if idle_seconds:
            threading.Thread(target=self._idle_reaper, daemon=True).start()

    # ------------------------------------------------------------ plumbing

    def _idle_reaper(self):
        while True:
            time.sleep(30)
            with self.lock:
                if self.server and time.time() - self.last_used > self.idle_seconds:
                    self._stop()

    def _stop(self):
        if self.server:
            self.server.close()
        self.server, self.docs, self.opened_with = None, {}, {}

    def close(self):
        with self.lock:
            self._stop()

    def _server_for(self, root):
        if self.server and (self.server.project != root or not self.server.alive):
            self._stop()
        if not self.server:
            self.server = LeanServer(root)
        return self.server

    def _sync(self, root, rel, text, timeout):
        """Make the server's copy of the document equal `text`; return normalised diagnostics."""
        uri = "file://" + os.path.join(root, rel)
        for attempt in (1, 2):
            srv = self._server_for(root)
            try:
                snap = core.source_snapshot(root)
                if uri in self.docs and core.dependencies_changed(self.opened_with[uri], snap, rel):
                    self._close_doc(uri)
                if uri in self.docs:
                    v = self.docs.pop(uri) + 1
                    srv.notify("textDocument/didChange", {"textDocument": {"uri": uri, "version": v},
                                                          "contentChanges": [{"text": text}]})
                else:
                    while len(self.docs) >= MAX_OPEN_DOCS:
                        self._close_doc(next(iter(self.docs)))
                    v = 1
                    self.opened_with[uri] = snap
                    srv.notify("textDocument/didOpen", {"textDocument": {
                        "uri": uri, "languageId": "lean4", "version": v, "text": text}})
                self.docs[uri] = v
                srv.request("textDocument/waitForDiagnostics", {"uri": uri, "version": v},
                            timeout=timeout)
                raw = srv.diagnostics_for(uri, v)
                diags = core.normalise_diagnostics(raw or [])
                if core.is_stale_imports(diags) and attempt == 1:
                    # A dependency changed on disk since this document was opened:
                    # reopening makes the worker rebuild its imports (what an editor's
                    # "Restart File" does).
                    self._close_doc(uri)
                    continue
                return uri, diags
            except ServerDied:
                self._stop()
                if attempt == 2:
                    raise
        return uri, diags

    def _close_doc(self, uri):
        self.docs.pop(uri, None)
        self.opened_with.pop(uri, None)
        if self.server and self.server.alive:
            self.server.notify("textDocument/didClose", {"textDocument": {"uri": uri}})

    def _goal(self, uri, line_no, col):
        r = self.server.request("$/lean/plainGoal", {"textDocument": {"uri": uri},
                                                     "position": {"line": line_no - 1, "character": col}})
        return r["goals"] if r else None

    def _resolve(self, file, text):
        root, rel = core.find_project(file, self.default_project)
        if text is None:
            try:
                with open(os.path.join(root, rel), encoding="utf-8") as f:
                    text = f.read()
            except FileNotFoundError:
                raise core.UserError(f"{rel} does not exist in {root}; pass `text` to check a new file")
        return root, rel, text

    # ------------------------------------------------------------ operations

    def check(self, file, text=None, goals_at=(), timeout=600):
        rel, _, diags, goals, _, seconds, _ = self.check_data(file, text, goals_at, (), timeout)
        return core.render_check(rel, diags, goals, seconds)

    def check_data(self, file, text=None, goals_at=(), goals_after=(), timeout=600):
        """-> (rel, text, diagnostics, {line: goals before}, {line: goals after}, seconds, tokens).

        A value of None means Lean has no tactic state at that point. `tokens` are Lean's
        semantic tokens for `text` (core.decode_tokens); [] when Lean gives none.
        """
        with self.lock:
            self.last_used = time.time()
            t0 = time.time()
            root, rel, text = self._resolve(file, text)
            uri, diags = self._sync(root, rel, text, timeout)
            lines = text.split("\n")

            def at(ln, column):
                return self._goal(uri, ln, column(lines[ln - 1])) if 1 <= ln <= len(lines) else None

            before = {ln: at(ln, core.goal_column) for ln in goals_at or ()}
            after = {ln: at(ln, core.end_column) for ln in goals_after or ()}
            return rel, text, diags, before, after, time.time() - t0, self._tokens(uri)

    def _tokens(self, uri):
        """Colouring is optional: a server that cannot give tokens leaves the check intact."""
        try:
            r = self.server.request("textDocument/semanticTokens/full", {"textDocument": {"uri": uri}},
                                    timeout=60)
        except (RuntimeError, TimeoutError):
            return []
        return core.decode_tokens((r or {}).get("data"), self.server.token_types)

    def save(self, file, text, base):
        """Write an app edit to disk if the file is unchanged since it was loaded (core decides)."""
        with self.lock:
            root, rel = core.find_project(file, self.default_project)
            return rel, core.write_if_unchanged(root, rel, text, base)

    def create(self, file, text):
        """Create a new source and register it in its library root (core decides)."""
        with self.lock:
            root, rel = core.find_project(file, self.default_project)
            nbytes, registered = core.create_source(root, rel, text)
            return rel, nbytes, registered

    def complete(self, file, text, line, col, timeout=120):
        """Lean's completions at (line, UTF-16 col) of `text`, ranked by core."""
        with self.lock:
            self.last_used = time.time()
            root, rel, text = self._resolve(file, text)
            lines = text.split("\n")
            if not 1 <= line <= len(lines):
                raise core.UserError(f"line {line} is outside the text (1..{len(lines)})")
            uri, _ = self._sync(root, rel, text, timeout)
            r = self.server.request("textDocument/completion", {"textDocument": {"uri": uri},
                                    "position": {"line": line - 1, "character": col}}, timeout=timeout)
            items = r.get("items", []) if isinstance(r, dict) else (r or [])
            frag = core.completion_fragment(lines[line - 1], col)
            return {"fragment": frag, "items": core.rank_completions(items, frag)}

    def overview(self):
        return core.file_overview(os.path.realpath(self.default_project))

    def abbreviations(self):
        return core.read_abbreviations(os.path.realpath(self.default_project))

    def set_abbreviation(self, name, symbol):
        with self.lock:
            return core.write_abbreviation(os.path.realpath(self.default_project), name, symbol)

    def files(self):
        return core.list_sources(os.path.realpath(self.default_project))

    def try_tactics(self, file, line, candidates, text=None, timeout=600):
        if not candidates:
            raise core.UserError("give at least one candidate tactic")
        with self.lock:
            self.last_used = time.time()
            t0 = time.time()
            root, rel, text = self._resolve(file, text)
            results = []
            for cand in candidates:
                new_text, first, last, end_col = core.splice(text, line, cand)
                uri, diags = self._sync(root, rel, new_text, timeout)
                after = self._goal(uri, last, end_col)
                results.append({"candidate": cand, "first": first, "last": last,
                                "diagnostics": diags, "goals_after": after,
                                "verdict": core.verdict(diags, first, last, after)})
            return core.render_try(rel, line, results, time.time() - t0)

    def search(self, words, file=None, limit=30, timeout=600):
        words = core.search_words(words)
        limit = max(1, min(int(limit or 30), 100))
        with self.lock:
            self.last_used = time.time()
            root, rel, text = self._resolve(file or self._default_file(), None)
            base = text.rstrip("\n")
            snippet = core.search_snippet(words, limit)
            _, diags = self._sync(root, rel, base + snippet, timeout)
            try:
                total, entries = core.parse_search(diags, base.count("\n") + 3)
            except core.UserError as e:
                if not core.needs_lean_import(e):
                    raise
                base, _ = core.with_lean_import(base)
                _, diags = self._sync(root, rel, base + snippet, timeout)
                total, entries = core.parse_search(diags, base.count("\n") + 3)
            return core.render_search(words, total, entries)

    def api_search(self, engine, query, file=None, text=None, fetch=fetch_json, timeout=600):
        """Ask Loogle or LeanSearch, then check every hit in the scope of [file] (default: the
        root module) so each one says ok / import / missing against this project's Mathlib."""
        t0 = time.time()
        if engine == "loogle":
            res = core.parse_loogle(fetch(core.loogle_url(query)))
        else:
            res = core.parse_leansearch(fetch(core.LEANSEARCH_URL, core.leansearch_body(query)))
        t_api = time.time() - t0
        snippet = core.exists_snippet(res["hits"])
        states, rel = {}, file
        if snippet:
            with self.lock:
                self.last_used = time.time()
                root, rel, disk = self._resolve(file or self._default_file(), None)
                base = (text if text is not None else disk).rstrip("\n")
                _, diags = self._sync(root, rel, base + snippet, timeout)
                try:
                    states = core.parse_exists(diags, base.count("\n") + 3)
                except core.UserError as e:
                    if not core.needs_lean_import(e):
                        raise
                    base, _ = core.with_lean_import(base)
                    _, diags = self._sync(root, rel, base + snippet, timeout)
                    states = core.unimported_by_file(core.parse_exists(diags, base.count("\n") + 3), res["hits"])
        return dict(res, engine=engine, query=query, file=rel, hits=core.mark_hits(res["hits"], states),
                    seconds={"api": round(t_api, 2), "total": round(time.time() - t0, 2)})

    # ------------------------------------------------------------ packages

    VCS_TTL = 120  # git and CI change slowly, and gh goes to the network

    def package(self, fresh=False):
        """This package for the landing page: libraries with their files' overview, git
        state and the last CI run (cached for VCS_TTL), and its dependencies."""
        root = os.path.realpath(self.default_project)
        out = core.package_overview(root)
        out.update(self._vcs(root, fresh))
        out["dependencies"] = [dict(d) for d in core.dependency_cards(root, self._count)]
        return out

    def _count(self, folder):
        cache = self.__dict__.setdefault("_counts", {})
        if folder not in cache:
            cache[folder] = core.count_sources(folder)
        return cache[folder]

    def _vcs(self, root, fresh):
        cached = self.__dict__.get("_vcs_cache")
        if cached and not fresh and time.time() - cached[0] < self.VCS_TTL:
            return cached[1]
        git = ci = None
        try:
            p = subprocess.run(["git", "status", "--porcelain=v2", "--branch"], cwd=root,
                               capture_output=True, text=True, timeout=10)
            if p.returncode == 0:
                git = core.parse_git_status(p.stdout)
        except (OSError, subprocess.TimeoutExpired):
            pass
        if git is not None:
            try:
                p = subprocess.run(["gh", "run", "list", "-L", "1", "--json",
                                    "status,conclusion,createdAt,headSha,workflowName"],
                                   cwd=root, capture_output=True, text=True, timeout=20)
                if p.returncode == 0:
                    ci = core.parse_ci(p.stdout)
            except (OSError, subprocess.TimeoutExpired):
                pass
        val = {"git": git, "ci": ci}
        self._vcs_cache = (time.time(), val)
        return val

    def add_library(self, name):
        """+ lean_lib: declare it in the lakefile and create its root; then restart Lean so
        `lake serve` reads the new lakefile."""
        with self.lock:
            lf, root_rel = core.add_library(os.path.realpath(self.default_project), name)
            self._stop()
            return lf, root_rel

    def toolbox(self):
        return core.read_toolbox(os.path.realpath(self.default_project))

    def set_toolbox(self, entry, pinned):
        with self.lock:
            return core.write_toolbox(os.path.realpath(self.default_project), entry, pinned)

    def source(self, module, name):
        """A module's source, read-only, from the project or one of its packages."""
        root = os.path.realpath(self.default_project)
        for cand in core.module_candidates(root, module):
            real = os.path.realpath(cand)
            if not real.startswith(root + os.sep) or not os.path.isfile(real):
                continue
            if os.path.getsize(real) > 4 * 1024 * 1024:
                raise core.UserError(f"{module} is too large to show")
            with open(real, encoding="utf-8") as f:
                text = f.read()
            return {"module": module, "path": os.path.relpath(real, root), "text": text,
                    "line": core.declaration_line(text, name)}
        raise core.UserError(f"no source for {module} in the project or its packages")

    def _default_file(self):
        """The project's root module (e.g. SyntheticSystems.lean): it imports everything."""
        root = os.path.realpath(self.default_project)
        tops = sorted(f for f in os.listdir(root) if f.endswith(".lean") and f[0].isupper())
        if not tops:
            raise core.UserError("no root module found; pass `file` to search in its scope")
        return tops[0]

    def build(self, file=None, timeout=1800):
        root, _ = core.find_project(file or self._default_file(), self.default_project)
        t0 = time.time()
        try:
            p = subprocess.run(["lake", "build"], cwd=root, env=lean_env(), capture_output=True,
                               text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            raise core.UserError(f"lake build did not finish within {timeout}s")
        res = core.parse_build(p.stdout + "\n" + p.stderr, p.returncode)
        return core.render_build(res, time.time() - t0)
