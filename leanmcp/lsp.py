"""A `lake serve` process and the LSP framing to talk to it. Stdlib only, Termux-aware.

No decisions here beyond transport: requests, notifications, and remembering the
latest diagnostics per (uri, version).
"""
import json
import os
import subprocess
import sys
import threading

HOME = os.path.expanduser("~")


def lean_env():
    """Environment Lean needs on Termux (see ~/.elan/termux-lean-toolchain.sh)."""
    env = dict(os.environ)
    env["PATH"] = ":".join([f"{HOME}/.elan/termux-shims", f"{HOME}/.elan/bin", env.get("PATH", "")])
    # Android has no /etc/localtime; Lean's watchdog dies without a TZif file and
    # accepts only an absolute path to one. Set for the Lean process only.
    if not os.path.isfile(env.get("TZ", "")):
        zone = "UTC"
        try:
            z = subprocess.run(["getprop", "persist.sys.timezone"], capture_output=True,
                               text=True, timeout=5).stdout.strip()
            if z and os.path.isfile(f"{HOME}/.local/share/zoneinfo/{z}"):
                zone = z
        except (OSError, subprocess.TimeoutExpired):
            pass
        env["TZ"] = f"{HOME}/.local/share/zoneinfo/{zone}"
    return env


class ServerDied(RuntimeError):
    pass


class LeanServer:
    def __init__(self, project):
        self.project = project
        # stderr goes to OUR stderr: never to stdout, which may be an MCP transport.
        self.p = subprocess.Popen(["lake", "serve"], cwd=project, env=lean_env(),
                                  stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  stderr=sys.stderr)
        self.next_id = 0
        self.responses = {}
        self.diagnostics = {}  # uri -> (version, [raw diagnostics])
        self.dead = False
        self.cv = threading.Condition()
        self.write_lock = threading.Lock()
        threading.Thread(target=self._reader, daemon=True).start()
        init = self.request("initialize", {"processId": os.getpid(), "rootUri": "file://" + project,
                                           "capabilities": {}}, timeout=120) or {}
        # The names behind semantic token type numbers (Lean's order, read, not assumed).
        self.token_types = (((init.get("capabilities") or {}).get("semanticTokensProvider") or {})
                            .get("legend") or {}).get("tokenTypes") or []
        self.notify("initialized", {})

    @property
    def alive(self):
        return not self.dead and self.p.poll() is None

    def _reader(self):
        out = self.p.stdout
        try:
            while True:
                hdr = {}
                while True:
                    line = out.readline()
                    if not line:
                        return
                    line = line.decode().strip()
                    if not line:
                        break
                    k, v = line.split(":", 1)
                    hdr[k.lower()] = v.strip()
                msg = json.loads(out.read(int(hdr["content-length"])))
                if "id" in msg and "method" not in msg:
                    with self.cv:
                        self.responses[msg["id"]] = msg
                        self.cv.notify_all()
                elif "id" in msg:  # server->client request (e.g. client/registerCapability)
                    self._send({"jsonrpc": "2.0", "id": msg["id"], "result": None})
                elif msg.get("method") == "textDocument/publishDiagnostics":
                    p = msg["params"]
                    with self.cv:
                        self.diagnostics[p["uri"]] = (p.get("version"), p["diagnostics"])
                        self.cv.notify_all()
        finally:
            with self.cv:
                self.dead = True
                self.cv.notify_all()

    def _send(self, msg):
        b = json.dumps(msg).encode()
        with self.write_lock:
            try:
                self.p.stdin.write(b"Content-Length: %d\r\n\r\n" % len(b) + b)
                self.p.stdin.flush()
            except (BrokenPipeError, ValueError) as e:
                raise ServerDied(f"Lean server is gone ({e})") from None

    def request(self, method, params, timeout=300):
        with self.cv:
            self.next_id += 1
            rid = self.next_id
        self._send({"jsonrpc": "2.0", "id": rid, "method": method, "params": params})
        with self.cv:
            if not self.cv.wait_for(lambda: rid in self.responses or self.dead, timeout):
                raise TimeoutError(f"Lean server did not answer {method} within {timeout}s")
            if rid not in self.responses:
                raise ServerDied(f"Lean server exited during {method}")
            r = self.responses.pop(rid)
        if "error" in r:
            raise RuntimeError(f"{method}: {r['error'].get('message')}")
        return r.get("result")

    def notify(self, method, params):
        self._send({"jsonrpc": "2.0", "method": method, "params": params})

    def diagnostics_for(self, uri, version, grace=5.0):
        """Diagnostics published for exactly `version`; waits briefly if they lag the response."""
        with self.cv:
            self.cv.wait_for(lambda: self.diagnostics.get(uri, (None,))[0] == version or self.dead,
                             grace)
            v, d = self.diagnostics.get(uri, (None, []))
            return d if v == version else None

    def close(self):
        try:
            if self.alive:
                self.request("shutdown", None, timeout=20)
                self.notify("exit", None)
            self.p.wait(timeout=20)
        except Exception:
            self.p.kill()
        for f in (self.p.stdin, self.p.stdout):
            try:
                f.close()
            except Exception:
                pass
