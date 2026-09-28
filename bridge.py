#!/data/data/com.termux/files/usr/bin/env python3
"""Localhost HTTP bridge from the Lean Workbench app to warm Lean servers.

An Android app cannot run Termux's binaries, so this Termux process owns the
Sessions and answers the app over 127.0.0.1. HTTP and auth only; every decision
is in leanmcp/core.py. Endpoints, auth and write paths: README.md.

  python3 bridge.py [--port 8766] [--pair]
"""
import argparse
import hmac
import json
import os
import secrets
import signal
import threading
import subprocess
import sys
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import quote

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from leanmcp import core  # noqa: E402
from leanmcp.session import Session  # noqa: E402

PROJECT = os.environ.get("LEAN_PROJECT", os.path.expanduser("~/LeanProjects/synthetic-systems"))
# Every folder with a lakefile under here is a package the app can open (X-Lean-Package).
PACKAGES = os.environ.get("LEAN_PACKAGES", os.path.dirname(os.path.realpath(PROJECT)))
PACKAGE_HEADER = "X-Lean-Package"
TOKEN_FILE = os.environ.get("LEAN_BRIDGE_TOKEN_FILE", os.path.expanduser("~/.config/lean-bridge/token"))
APP_PACKAGE = "com.leanworkbench.app"
MAX_BODY = 4 * 1024 * 1024


def load_token():
    try:
        with open(TOKEN_FILE, encoding="ascii") as f:
            tok = f.read().strip()
        if tok:
            return tok
    except FileNotFoundError:
        pass
    os.makedirs(os.path.dirname(TOKEN_FILE), mode=0o700, exist_ok=True)
    tok = secrets.token_urlsafe(32)
    fd = os.open(TOKEN_FILE, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    with os.fdopen(fd, "w") as f:
        f.write(tok + "\n")
    return tok


def log(*a):
    print(*a, file=sys.stderr, flush=True)


class Sessions:
    """One Session per package, made when the app first asks for it. Each starts Lean only
    when used and stops it when idle, so an unused package costs nothing."""

    def __init__(self, base, default):
        self.base, self.default = base, default
        self.by_name = {}
        self.lock = threading.Lock()

    def get(self, name):
        name = name or self.default
        if name not in core.find_packages(self.base):
            raise core.UserError(f"no Lean package {name!r} under {self.base}")
        with self.lock:
            if name not in self.by_name:
                self.by_name[name] = Session(os.path.join(self.base, name))
            return self.by_name[name]

    def names(self):
        return core.find_packages(self.base)

    def close(self):
        for s in list(self.by_name.values()):
            s.close()


def make_handler(sessions, token):
    class Handler(BaseHTTPRequestHandler):
        protocol_version = "HTTP/1.1"

        def log_message(self, fmt, *args):
            log("bridge:", fmt % args)

        def _send(self, status, obj):
            body = json.dumps(obj, ensure_ascii=False).encode("utf-8")
            self.send_response(status)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def _authorised(self):
            got = self.headers.get("Authorization", "")
            ok = hmac.compare_digest(got.encode(), ("Bearer " + token).encode())
            if not ok:
                self._send(401, {"error": "missing or wrong token; pair the app with `bridge.py --pair`"})
            return ok

        def do_GET(self):
            if self.path == "/v1/health":
                return self._send(200, {"ok": True, "project": os.path.basename(PROJECT)})
            if not self._authorised():
                return
            try:
                if self.path == "/v1/packages":
                    names = sessions.names()
                    return self._send(200, {"base": sessions.base, "default": sessions.default,
                                            "packages": [sessions.get(n).package() for n in names]})
                session = sessions.get(self.headers.get(PACKAGE_HEADER))
                if self.path == "/v1/files":
                    return self._send(200, {"files": session.files()})
                if self.path == "/v1/overview":
                    return self._send(200, session.overview())
                if self.path == "/v1/abbreviations":
                    return self._send(200, session.abbreviations())
                if self.path == "/v1/toolbox":
                    return self._send(200, session.toolbox())
            except core.UserError as e:
                return self._send(400, {"error": str(e)})
            self._send(404, {"error": f"no such endpoint: GET {self.path}"})

        def do_POST(self):
            if not self._authorised():
                return
            if self.path not in ("/v1/check", "/v1/save", "/v1/complete", "/v1/create", "/v1/abbreviation",
                                 "/v1/search", "/v1/toolbox", "/v1/source", "/v1/library"):
                return self._send(404, {"error": f"no such endpoint: POST {self.path}"})
            try:
                n = int(self.headers.get("Content-Length", "0"))
                if n > MAX_BODY:
                    raise core.UserError("request body too large")
                body = json.loads(self.rfile.read(n).decode("utf-8") or "null")
                session = sessions.get(self.headers.get(PACKAGE_HEADER))
                if self.path == "/v1/library":
                    lf, root_rel = session.add_library(core.library_request(body))
                    log(f"bridge: new library {root_rel} declared in {lf}")
                    return self._send(200, {"lakefile": lf, "root": root_rel})
                if self.path == "/v1/complete":
                    return self._send(200, session.complete(*core.complete_request(body)))
                if self.path == "/v1/search":
                    engine, query, file, text = core.api_search_request(body)
                    res = session.api_search(engine, query, file, text)
                    log(f"bridge: {engine} {query!r}: {len(res['hits'])} hits in {res['seconds']['total']}s")
                    return self._send(200, res)
                if self.path == "/v1/toolbox":
                    entry, pinned = core.toolbox_request(body)
                    box = session.set_toolbox(entry, pinned)
                    log(f"bridge: toolbox {'pin' if pinned else 'unpin'} {entry['name']}")
                    return self._send(200, box)
                if self.path == "/v1/source":
                    return self._send(200, session.source(*core.source_request(body)))
                if self.path == "/v1/abbreviation":
                    name, symbol = core.abbreviation_request(body)
                    table = session.set_abbreviation(name, symbol)
                    log(f"bridge: abbreviation \\{name} -> {symbol!r}")
                    return self._send(200, table)
                if self.path == "/v1/create":
                    rel, nbytes, registered = session.create(*core.create_request(body))
                    log(f"bridge: created {rel} ({nbytes} bytes), registered in {registered}")
                    return self._send(200, {"file": rel, "bytes": nbytes, "registered": registered})
                if self.path == "/v1/save":
                    rel, nbytes = session.save(*core.save_request(body))
                    log(f"bridge: saved {rel} ({nbytes} bytes)")
                    return self._send(200, {"file": rel, "bytes": nbytes})
                file, text, goals_at, goals_after = core.check_request(body)
                rel, text, diags, before, after, secs, tokens = session.check_data(file, text, goals_at, goals_after)
                self._send(200, core.check_payload(rel, text, diags, before, secs, after, tokens))
            except core.UserError as e:
                self._send(400, {"error": str(e)})
            except (ValueError, UnicodeDecodeError) as e:
                self._send(400, {"error": f"body is not JSON: {e}"})
            except Exception as e:  # errors are data; the bridge stays up
                log("bridge: check failed:", repr(e))
                self._send(500, {"error": f"{type(e).__name__}: {e}"})

    return Handler


def pair(port, token):
    url = f"leanwb://pair?port={port}&token={quote(token)}"
    r = subprocess.run(["termux-open-url", url, APP_PACKAGE], capture_output=True, text=True)
    if r.returncode != 0:
        log("pairing link could not be opened:", r.stdout + r.stderr)
        return 1
    log("pairing link sent to", APP_PACKAGE)
    return 0


def _terminate(*_):
    raise KeyboardInterrupt  # so `finally` closes the Lean server on SIGTERM too


def main(argv=None):
    ap = argparse.ArgumentParser(prog="bridge")
    ap.add_argument("--port", type=int, default=8766)
    ap.add_argument("--pair", action="store_true", help="send the token to the app, then exit")
    a = ap.parse_args(argv)
    token = load_token()
    if a.pair:
        return pair(a.port, token)
    sessions = Sessions(PACKAGES, os.path.basename(os.path.realpath(PROJECT)))
    httpd = ThreadingHTTPServer(("127.0.0.1", a.port), make_handler(sessions, token))
    signal.signal(signal.SIGTERM, _terminate)
    log(f"bridge: serving {PROJECT} on 127.0.0.1:{a.port}")
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        sessions.close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
