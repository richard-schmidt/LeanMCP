"""Thin CLI over Session, for humans and the integration tests. No decisions.

  python3 -m leanmcp.cli check  FILE [--text-file F] [--goals 3,7]
  python3 -m leanmcp.cli try    FILE LINE CANDIDATE... [--text-file F]
  python3 -m leanmcp.cli search WORDS [--file FILE] [--limit N]
  python3 -m leanmcp.cli build  [--file FILE]
"""
import argparse
import os
import sys

from . import core
from .session import Session

DEFAULT_PROJECT = os.environ.get("LEAN_PROJECT", os.path.expanduser("~/LeanProjects/synthetic-systems"))


def main(argv=None):
    ap = argparse.ArgumentParser(prog="leanmcp")
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("check"); c.add_argument("file"); c.add_argument("--text-file"); c.add_argument("--goals", default="")
    t = sub.add_parser("try"); t.add_argument("file"); t.add_argument("line", type=int); t.add_argument("candidates", nargs="+"); t.add_argument("--text-file")
    s = sub.add_parser("search"); s.add_argument("words"); s.add_argument("--file"); s.add_argument("--limit", type=int, default=30)
    b = sub.add_parser("build"); b.add_argument("--file")
    a = ap.parse_args(argv)
    text = open(a.text_file, encoding="utf-8").read() if getattr(a, "text_file", None) else None
    sess = Session(DEFAULT_PROJECT, idle_seconds=0)
    try:
        if a.cmd == "check":
            goals = [int(x) for x in a.goals.split(",") if x]
            print(sess.check(a.file, text, goals))
        elif a.cmd == "try":
            print(sess.try_tactics(a.file, a.line, a.candidates, text))
        elif a.cmd == "search":
            print(sess.search(a.words, a.file, a.limit))
        else:
            print(sess.build(a.file))
    except core.UserError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    finally:
        sess.close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
