"""Lean MCP server: protocol only. Newline-delimited JSON-RPC on stdin/stdout.

Nothing but JSON-RPC may reach stdout; Lean's own stderr and our tracebacks go to
stderr. Every judgment lives in leanmcp/core.py; the warm Lean server lives in
leanmcp/session.py (in-process, so it stays warm between calls: the one reason
this server does not shell out to the CLI).
"""
import json
import os
import sys
import traceback

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from leanmcp import core  # noqa: E402
from leanmcp.session import Session  # noqa: E402

DEFAULT_PROJECT = os.environ.get("LEAN_PROJECT", os.path.expanduser("~/LeanProjects/synthetic-systems"))

FILE_DESC = ("A .lean file: absolute (its Lake project is found from the path), or relative to the "
             f"default project {DEFAULT_PROJECT}.")

TOOLS = [
    {
        "name": "lean_check",
        "description": (
            "Check one Lean file with the real Lean + Mathlib checker: every error, warning and "
            "`sorry`, and optionally the goal state at chosen lines. Pass `text` to check a version "
            "that is not on disk -- nothing is ever written, so this is how you validate an edit "
            "BEFORE making it. The goal shown for a line is the state before that line's tactic. "
            "'clean' means no messages at all; a `sorry` warning means the proof is NOT done. "
            "First call ~15-30 s (starts Lean); later calls on the same file take seconds."),
        "inputSchema": {"type": "object", "required": ["file"], "properties": {
            "file": {"type": "string", "description": FILE_DESC},
            "text": {"type": "string", "description": "Full contents to check instead of the disk copy."},
            "goals_at": {"type": "array", "items": {"type": "integer"},
                         "description": "1-based lines to show the goal state before."}}},
    },
    {
        "name": "lean_try",
        "description": (
            "Try several candidate tactics at one line and compare them, without writing anything. "
            "Use it to explore a proof step: put `sorry` on its own line where the step goes, then "
            "pass that line and candidates such as `simp`, `exact foo`, `rw [bar]`, `aesop`, "
            "`exact?`. If the line contains `sorry`, only the `sorry` is replaced; otherwise the "
            "whole line is. A candidate may span several lines (use \\n) when the `sorry` stands "
            "alone on its line. Each candidate gets a verdict -- NO GOALS (this step closes its "
            "goal), PROGRESS (runs, goals remain: shown), ERROR (Lean's message) -- plus any "
            "info such as `exact?`'s 'Try this' suggestion. The verdict is about that step only; "
            "run lean_check on the final text to confirm the whole file."),
        "inputSchema": {"type": "object", "required": ["file", "line", "candidates"], "properties": {
            "file": {"type": "string", "description": FILE_DESC},
            "line": {"type": "integer", "description": "1-based line to put each candidate on."},
            "candidates": {"type": "array", "items": {"type": "string"}, "minItems": 1,
                           "description": "Tactics to try, each on its own (tried one at a time)."},
            "text": {"type": "string", "description": "Contents to start from instead of the disk copy."}}},
    },
    {
        "name": "lean_search",
        "description": (
            "Find lemmas and definitions by name fragments, offline, among everything in scope for "
            "a file (default: the project's root module, which imports all of it, including the "
            "Mathlib parts it uses). Every word must occur in the full name, e.g. 'finset union "
            "comm' or 'inter subset'. Mathlib names follow its conventions (union_comm, "
            "inter_subset_left, mul_le_mul), so search by the shape of the statement. Returns names "
            "with their types, shortest first. To search by GOAL rather than name, use lean_try "
            "with `exact?` or `apply?` instead."),
        "inputSchema": {"type": "object", "required": ["words"], "properties": {
            "words": {"type": "string", "description": "Space-separated name fragments."},
            "file": {"type": "string", "description": FILE_DESC + " Search runs in its scope."},
            "limit": {"type": "integer", "description": "Max results (default 30, max 100)."}}},
    },
    {
        "name": "lean_build",
        "description": (
            "Run `lake build` on the whole project and summarise errors, sorries and warnings. "
            "Use it as the final gate after editing files on disk -- it is what CI would run. "
            "Slower than lean_check (it rebuilds changed modules and everything depending on "
            "them); use lean_check while iterating on one file."),
        "inputSchema": {"type": "object", "properties": {
            "file": {"type": "string", "description": "Any .lean file of the project to build (optional)."}}},
    },
]

_session = None


def session():
    global _session
    if _session is None:
        _session = Session(DEFAULT_PROJECT)
    return _session


def call_tool(name, a):
    try:
        if name == "lean_check":
            return session().check(a["file"], a.get("text"), a.get("goals_at") or []), False
        if name == "lean_try":
            return session().try_tactics(a["file"], int(a["line"]), a["candidates"], a.get("text")), False
        if name == "lean_search":
            return session().search(a["words"], a.get("file"), a.get("limit") or 30), False
        if name == "lean_build":
            return session().build(a.get("file")), False
        return f"unknown tool {name!r}; the tools are " + ", ".join(t["name"] for t in TOOLS), True
    except core.UserError as e:
        return str(e), True
    except KeyError as e:
        return f"missing required argument {e}", True
    except Exception as e:  # errors are data, never a crash
        traceback.print_exc(file=sys.stderr)
        return f"{name} failed: {type(e).__name__}: {e}", True


def reply(rid, result=None, error=None):
    msg = {"jsonrpc": "2.0", "id": rid}
    if error:
        msg["error"] = error
    else:
        msg["result"] = result
    sys.stdout.write(json.dumps(msg, ensure_ascii=False) + "\n")
    sys.stdout.flush()


def main():
    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        try:
            req = json.loads(line)
        except ValueError:
            continue
        if req.get("id") is None:  # a notification: never answered
            continue
        m, rid = req.get("method"), req["id"]
        if m == "initialize":
            reply(rid, {"protocolVersion": "2024-11-05", "capabilities": {"tools": {}},
                        "serverInfo": {"name": "lean", "version": "1.0.0"}})
        elif m == "tools/list":
            reply(rid, {"tools": TOOLS})
        elif m == "tools/call":
            p = req.get("params") or {}
            text, is_err = call_tool(p.get("name"), p.get("arguments") or {})
            reply(rid, {"content": [{"type": "text", "text": text}], "isError": is_err})
        elif m == "ping":
            reply(rid, {})
        else:
            reply(rid, error={"code": -32601, "message": f"method not found: {m}"})
    if _session:
        _session.close()


if __name__ == "__main__":
    main()
