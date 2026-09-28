"""Against a real Lean toolchain: sessions, the MCP protocol and the HTTP bridge.

Two groups:
- Lean only (always run by ./test.sh --integration): a small Lake package committed in
  tests/project/, copied to a temporary folder for each run, so nothing here writes to
  the repo. Needs only the toolchain named in tests/project/lean-toolchain.
- Mathlib (skipped unless LEAN_MATHLIB_PROJECT and LEAN_MATHLIB_FILE are set): read-only
  checks against any Lake package with Mathlib built, and a file of it that imports
  Mathlib.Data.Finset.Basic. Every variant is passed as in-memory `text`, and the
  package's `git status` must be unchanged afterwards.

Each test's wrong input carries a fresh nonce, so a stale result cannot pass.
Slow (a Lean server start is ~15-30 s).
"""
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
import uuid

from leanmcp.session import Session

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEMO = os.path.join(HERE, "tests", "project")
F = "Demo/Basic.lean"

MATHLIB_PROJECT = os.environ.get("LEAN_MATHLIB_PROJECT")
MATHLIB_FILE = os.environ.get("LEAN_MATHLIB_FILE")


def nonce():
    return "n" + uuid.uuid4().hex[:8]


def demo_copy():
    """A fresh copy of the demo package, as a git repo on `main`: (packages dir, project)."""
    base = os.path.realpath(tempfile.mkdtemp(prefix="leanmcp-", dir=os.environ.get("TMPDIR")))
    project = os.path.join(base, "demo")
    shutil.copytree(DEMO, project)
    git = ["git", "-C", project, "-c", "user.name=test", "-c", "user.email=test@example.com"]
    subprocess.run(git[:3] + ["init", "-q", "-b", "main"], check=True)
    subprocess.run(git[:3] + ["add", "-A"], check=True)
    subprocess.run(git + ["commit", "-q", "-m", "demo"], check=True)
    return base, project


def read(project, rel):
    with open(os.path.join(project, rel), encoding="utf-8") as f:
        return f.read()


def with_theorem(base, stmt, *tactic_lines):
    base = base.rstrip("\n")
    text = base + "\n\n" + stmt + " := by\n" + "".join("  " + t + "\n" for t in tactic_lines)
    return text, base.count("\n") + 4


class Live(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.base, cls.project = demo_copy()
        cls.s = Session(cls.project, idle_seconds=0)

    @classmethod
    def tearDownClass(cls):
        cls.s.close()
        shutil.rmtree(cls.base)

    def thm(self, stmt, *tactics):
        return with_theorem(read(self.project, F), stmt, *tactics)

    def test_1_disk_file_clean_then_warm(self):
        t = time.time()
        self.assertIn("clean: no errors", self.s.check(F))
        cold = time.time() - t
        t = time.time()
        self.assertIn("clean: no errors", self.s.check(F))
        warm = time.time() - t
        print(f"\n  cold check {cold:.1f}s, warm check {warm:.1f}s", file=sys.stderr)
        self.assertLess(warm, 5.0)

    def test_2_nonce_error_and_goal(self):
        n = nonce()
        text, ln = self.thm("theorem t_" + n + " (a b : List Nat) : a ++ b ++ [] = a ++ b", "exact " + n)
        out = self.s.check(F, text, [ln])
        self.assertIn(f"error at line {ln}:", out)
        self.assertIn(n, out)
        self.assertIn("⊢ a ++ b ++ [] = a ++ b", out)

    def test_3_sorry_is_not_clean(self):
        text, _ = self.thm("theorem t_" + nonce() + " : (1 : Nat) = 1", "sorry")
        out = self.s.check(F, text)
        self.assertNotIn("clean", out)
        self.assertIn("1 declaration(s) using sorry", out)

    def test_4_try_verdicts(self):
        n = nonce()
        text, ln = self.thm("theorem t_" + n + " : ∀ a b : List Nat, a ++ b ++ [] = a ++ b", "sorry")
        out = self.s.try_tactics(F, ln, ["exact " + n, "intro a b", "intro a b\nexact List.append_nil (a ++ b)"],
                                 text)
        self.assertIn("[1] ERROR: exact " + n, out)
        self.assertIn(n, out.split("[2]")[0])
        self.assertIn("[2] PROGRESS: intro a b", out)
        self.assertIn("⊢ a ++ b ++ [] = a ++ b", out.split("[2]")[1].split("[3]")[0])
        self.assertIn("[3] NO GOALS", out)

    def test_5_try_exact_query_suggests(self):
        text, ln = self.thm("theorem t_" + nonce() + " (a : List Nat) : a ++ [] = a", "sorry")
        out = self.s.try_tactics(F, ln, ["exact?"], text)
        self.assertIn("Try this", out)

    def test_6_search(self):
        out = self.s.search("list append nil")
        self.assertIn("List.append_nil :", out)
        self.assertIn("no constant", self.s.search("zz" + nonce()))

    def test_7_build(self):
        out = self.s.build()
        self.assertIn("Build completed successfully", out)

    def test_8_api_search_states(self):
        # The services are faked (no network in tests); the scope check is real Lean.
        n = nonce()
        hits = [{"name": "List.append_nil", "type": "t", "module": "Init.Data.List.Basic", "doc": None},
                {"name": "Lean.Json.compress", "type": "t", "module": "Lean.Data.Json.Printer", "doc": None},
                {"name": "List.append_nil_" + n, "type": "t", "module": "Init.Data.List.Basic", "doc": None},
                {"name": "x_" + n, "type": "t", "module": "Init.No" + n, "doc": None}]
        fake = lambda url, data=None: {"count": 4, "hits": hits}
        r = self.s.api_search("loogle", "q " + n, fetch=fake)
        self.assertEqual([h["state"] for h in r["hits"]], ["ok", "import", "missing", "missing"])
        self.assertEqual(r["file"], "Demo.lean")


class DependencyEdit(unittest.TestCase):
    """An import edited on disk while the importer is open in the warm server.

    Lean does not notice this by itself (it keeps the old imports and reports a false
    'unknown identifier'); the session must reopen the document.
    """

    def test_new_definition_in_dependency_is_seen(self):
        base, project = demo_copy()
        root = os.path.join(base, "t")
        try:
            os.makedirs(os.path.join(root, "T"))
            shutil.copy(os.path.join(DEMO, "lean-toolchain"), root)
            with open(os.path.join(root, "lakefile.toml"), "w") as f:
                f.write('name = "t"\n[[lean_lib]]\nname = "T"\n')
            a, b = os.path.join(root, "T", "A.lean"), os.path.join(root, "T", "B.lean")
            with open(a, "w") as f:
                f.write("def one : Nat := 1\n")
            with open(b, "w") as f:
                f.write("import T.A\n\nexample : one = 1 := rfl\n")
            s = Session(project, idle_seconds=0)   # default project differs: B found by absolute path
            try:
                self.assertIn("clean", s.check(b))
                n = nonce()
                with open(a, "a") as f:
                    f.write(f"def {n} : Nat := 42\n")
                text = f"import T.A\n\nexample : {n} = 42 := rfl\n"
                self.assertIn("clean", s.check(b, text))
            finally:
                s.close()
        finally:
            shutil.rmtree(base)


class Protocol(unittest.TestCase):
    """Real JSON-RPC through mcp_server.py: n requests + 1 notification -> n replies, stdout pure JSON."""

    def test_roundtrip(self):
        base, project = demo_copy()
        try:
            n = nonce()
            text, ln = with_theorem(read(project, F), "theorem t_" + n + " : (2 : Nat) + 2 = 4", "sorry")
            msgs = [
                {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {}},
                {"jsonrpc": "2.0", "method": "notifications/initialized"},
                {"jsonrpc": "2.0", "id": 2, "method": "tools/list"},
                {"jsonrpc": "2.0", "id": 3, "method": "tools/call", "params": {
                    "name": "lean_try", "arguments": {"file": F, "line": ln, "text": text,
                                                      "candidates": ["exact " + n, "rfl"]}}},
                {"jsonrpc": "2.0", "id": 4, "method": "tools/call", "params": {
                    "name": "lean_check", "arguments": {"file": "../escape.lean"}}},
                {"jsonrpc": "2.0", "id": 5, "method": "nope"},
            ]
            p = subprocess.run([sys.executable, os.path.join(HERE, "mcp_server.py")],
                               input="\n".join(json.dumps(m, ensure_ascii=False) for m in msgs) + "\n",
                               capture_output=True, text=True, timeout=600,
                               env=dict(os.environ, LEAN_PROJECT=project))
            replies = [json.loads(l) for l in p.stdout.splitlines()]  # raises if anything non-JSON reached stdout
            self.assertEqual([r["id"] for r in replies], [1, 2, 3, 4, 5])
            self.assertEqual({t["name"] for t in replies[1]["result"]["tools"]},
                             {"lean_check", "lean_try", "lean_search", "lean_build"})
            tried = replies[2]["result"]["content"][0]["text"]
            self.assertIn("ERROR: exact " + n, tried)
            self.assertIn("NO GOALS: rfl", tried)
            self.assertTrue(replies[3]["result"]["isError"])
            self.assertIn("escapes", replies[3]["result"]["content"][0]["text"])
            self.assertEqual(replies[4]["error"]["code"], -32601)
        finally:
            shutil.rmtree(base)


class BridgeProcess:
    """bridge.py on a free port against [project], with a throwaway token."""

    def __init__(self, project, packages):
        import socket
        with socket.socket() as sk:
            sk.bind(("127.0.0.1", 0))
            self.port = sk.getsockname()[1]
        self.tokdir = tempfile.mkdtemp(dir=os.environ.get("TMPDIR"))
        env = dict(os.environ, LEAN_BRIDGE_TOKEN_FILE=os.path.join(self.tokdir, "token"),
                   LEAN_PROJECT=project, LEAN_PACKAGES=packages)
        self.p = subprocess.Popen([sys.executable, os.path.join(HERE, "bridge.py"), "--port", str(self.port)],
                                  env=env, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        self.base = f"http://127.0.0.1:{self.port}/v1"
        for _ in range(100):
            try:
                if self.call("/health")[0] == 200:
                    break
            except OSError:
                time.sleep(0.2)
        with open(os.path.join(self.tokdir, "token")) as f:
            self.token = f.read().strip()

    def call(self, path, body=None, token=None, headers=None):
        import urllib.request, urllib.error
        req = urllib.request.Request(self.base + path, data=None if body is None else json.dumps(body).encode())
        if token:
            req.add_header("Authorization", "Bearer " + token)
        for k, v in (headers or {}).items():
            req.add_header(k, v)
        try:
            with urllib.request.urlopen(req, timeout=600) as r:
                return r.status, json.loads(r.read())
        except urllib.error.HTTPError as e:
            return e.code, json.loads(e.read())

    def close(self):
        self.p.terminate()
        self.p.wait(timeout=30)
        shutil.rmtree(self.tokdir)
        return self.p.stdout.read()


class Bridge(unittest.TestCase):
    """bridge.py over real HTTP: auth, refusal, an in-app edit changing diagnostics and goals."""

    def test_http(self):
        base, project = demo_copy()
        b = BridgeProcess(project, base)
        call, tok = b.call, b.token
        try:
            self.assertEqual(call("/files")[0], 401)
            self.assertEqual(call("/files", token="x" + tok)[0], 401)
            st, files = call("/files", token=tok)
            self.assertIn(F, files["files"])
            self.assertEqual(call("/check", {"file": "/etc/passwd.lean"}, tok)[0], 400)

            n = nonce()
            text, ln = with_theorem(read(project, F), "theorem t_" + n + " (a b : List Nat) : a ++ b ++ [] = a ++ b",
                                    "exact " + n)
            st, p1 = call("/check", {"file": F, "text": text, "goals_at": [ln]}, tok)
            self.assertEqual(st, 200)
            decl = [d for d in p1["declarations"] if d["name"] == "t_" + n][0]
            self.assertEqual(decl["status"], "error")
            self.assertEqual(p1["goals"][0]["goals"][0]["target"], "a ++ b ++ [] = a ++ b")
            self.assertEqual(p1["goals"][0]["goals"][0]["hyps"][0]["names"], ["a", "b"])

            fixed = text.replace("exact " + n, "exact List.append_nil (a ++ b)")
            st, p2 = call("/check", {"file": F, "text": fixed, "goals_at": [ln], "goals_after": [ln]}, tok)
            decl = [d for d in p2["declarations"] if d["name"] == "t_" + n][0]
            self.assertEqual(decl["status"], "ok")
            self.assertEqual(p2["goals"][0]["goals"][0]["target"], "a ++ b ++ [] = a ++ b")  # before: unchanged
            self.assertEqual(p2["goals_after"], [{"line": ln, "goals": []}])                 # after: closed
            # Lean's semantic tokens for the edited text: `exact` a keyword, `a` a local.
            self.assertIn([ln, 2, 5, "keyword"], p2["tokens"])
            self.assertIn([ln, len("  exact List.append_nil ("), 1, "variable"], p2["tokens"])
            self.assertNotIn(ln, [t[0] for t in p1["tokens"] if t[1] == len("  exact ")])  # the nonce is no local

            # Completion: a dotted name, and local names first for a bare prefix.
            cl = fixed.split("\n")
            probe = "\n".join(cl[:ln - 1] + ["  have hx : a ++ [] = a := List.append_ni"] + cl[ln - 1:])
            st, c1 = call("/complete", {"file": F, "text": probe, "line": ln,
                                        "col": len("  have hx : a ++ [] = a := List.append_ni")}, tok)
            self.assertEqual(st, 200)
            self.assertEqual(c1["fragment"], "append_ni")
            self.assertIn("append_nil", [i["label"] for i in c1["items"]])
            probe2 = "\n".join(cl[:ln - 1] + ["  exact a"] + cl[ln - 1:])
            st, c2 = call("/complete", {"file": F, "text": probe2, "line": ln, "col": len("  exact a")}, tok)
            self.assertEqual(c2["items"][0], {"label": "a", "kind": 6})
            self.assertEqual(call("/complete", {"file": F, "text": probe2, "line": 0, "col": 0}, tok)[0], 400)

            # Save: refused when the disk moved on (file untouched); a same-content save goes through.
            disk = read(project, F)
            st, e = call("/save", {"file": F, "text": fixed, "base": disk + "-- " + n}, tok)
            self.assertEqual((st, "changed on disk" in e["error"]), (400, True))
            self.assertEqual(read(project, F), disk)
            self.assertEqual(call("/save", {"file": "New.lean", "text": "x", "base": "x"}, tok)[0], 400)
            self.assertEqual(call("/save", {"file": F, "text": disk, "base": disk})[0], 401)
            st, ok = call("/save", {"file": F, "text": disk, "base": disk}, tok)
            self.assertEqual((st, ok["bytes"]), (200, len(disk.encode("utf-8"))))
            self.assertEqual(read(project, F), disk)

            # Overview and abbreviations: read-only routes (the writes are unit-tested on a temp tree).
            st, ov = call("/overview", None, tok)
            roles = {f["path"]: f["role"] for f in ov["files"]}
            self.assertEqual((st, roles["Demo.lean"], roles[F]), (200, "root", "imported"))
            self.assertEqual(call("/abbreviations", None, tok)[0], 200)
            self.assertEqual(call("/abbreviation", {"name": "a b", "symbol": "x"}, tok)[0], 400)

            # Search and toolbox: refusals and read-only routes (no network here; the scope
            # check is Live.test_8, the toolbox writes are unit-tested on a temp tree).
            self.assertEqual(call("/search", {"engine": "google", "query": "x"}, tok)[0], 400)
            self.assertEqual(call("/search", {"engine": "loogle", "query": "x"})[0], 401)
            st, box = call("/toolbox", None, tok)
            self.assertEqual((st, isinstance(box, list)), (200, True))
            self.assertEqual(call("/toolbox", {"name": "a b", "pinned": True}, tok)[0], 400)
            self.assertEqual(call("/source", {"module": "..etc"}, tok)[0], 400)

            # Packages: the demo package and its library; unknown packages and an existing
            # library name are refused without writing.
            st, pk = call("/packages", None, tok)
            self.assertEqual((st, pk["default"]), (200, "demo"))
            demo = [x for x in pk["packages"] if x["name"] == "demo"][0]
            self.assertEqual([l["name"] for l in demo["libraries"]], ["Demo"])
            self.assertIn(F, [f["path"] for f in demo["libraries"][0]["files"]])
            self.assertEqual(demo["git"]["branch"], "main")
            self.assertEqual(call("/files", token=tok, headers={"X-Lean-Package": "nope"})[0], 400)
            lakefile = read(project, "lakefile.toml")
            st, e = call("/library", {"name": "Demo"}, tok)
            self.assertEqual((st, "already a library" in e["error"]), (400, True))
            self.assertEqual(read(project, "lakefile.toml"), lakefile)

            # Create: routed, and refuses without writing (the writes are unit-tested on a temp tree).
            st, e = call("/create", {"file": F, "text": "x"}, tok)
            self.assertEqual((st, "already exists" in e["error"]), (400, True))
            self.assertEqual(read(project, F), disk)
            self.assertEqual(call("/create", {"file": "Top.lean", "text": "x"}, tok)[0], 400)
            self.assertEqual(call("/create", {"file": "Demo/Zz.lean", "text": "x"})[0], 401)
        finally:
            out = b.close()
            shutil.rmtree(base)
            self.assertEqual(out, b"", "the bridge wrote to stdout")


@unittest.skipUnless(MATHLIB_PROJECT and MATHLIB_FILE,
                     "set LEAN_MATHLIB_PROJECT (a Lake package with Mathlib built) and LEAN_MATHLIB_FILE "
                     "(a file of it importing Mathlib.Data.Finset.Basic)")
class Mathlib(unittest.TestCase):
    """What needs Mathlib: Finset goals, `exact?` over Mathlib, constant search, source, dependencies."""

    @classmethod
    def setUpClass(cls):
        cls.project = os.path.realpath(os.path.expanduser(MATHLIB_PROJECT))
        cls.s = Session(cls.project, idle_seconds=0)
        cls.git_before = cls.git_status()

    @classmethod
    def git_status(cls):
        return subprocess.run(["git", "-C", cls.project, "status", "--porcelain"],
                              capture_output=True, text=True).stdout

    @classmethod
    def tearDownClass(cls):
        cls.s.close()
        assert cls.git_status() == cls.git_before, "the package changed on disk during the tests"

    def thm(self, stmt, *tactics):
        return with_theorem(read(self.project, MATHLIB_FILE), stmt, *tactics)

    def test_finset_goal_and_try(self):
        n = nonce()
        text, ln = self.thm("theorem t_" + n + " (s t : Finset ℕ) : s ∪ t = t ∪ s", "exact " + n)
        out = self.s.check(MATHLIB_FILE, text, [ln])
        self.assertIn(n, out)
        self.assertIn("⊢ s ∪ t = t ∪ s", out)
        text, ln = self.thm("theorem t_" + n + " : ∀ s t : Finset ℕ, s ∪ t = t ∪ s", "sorry")
        out = self.s.try_tactics(MATHLIB_FILE, ln, ["intro s t\nexact Finset.union_comm s t"], text)
        self.assertIn("[1] NO GOALS", out)

    def test_exact_query_over_mathlib(self):
        text, ln = self.thm("theorem t_" + nonce() + " (s t : Finset ℕ) : s ∩ t ⊆ s", "sorry")
        self.assertIn("Try this", self.s.try_tactics(MATHLIB_FILE, ln, ["exact?"], text))

    def test_search(self):
        self.assertIn("Finset.union_comm :", self.s.search("finset union comm", MATHLIB_FILE))

    def test_api_search_states(self):
        n = nonce()
        hits = [{"name": "Finset.union_comm", "type": "t", "module": "Mathlib.Data.Finset.Basic", "doc": None},
                {"name": "Real.pi_gt_three", "type": "t", "module": "Mathlib.Analysis.Real.Pi.Bounds", "doc": None},
                {"name": "x_" + n, "type": "t", "module": "Mathlib.No" + n, "doc": None}]
        fake = lambda url, data=None: {"count": 3, "hits": hits}
        r = self.s.api_search("loogle", "q " + n, file=MATHLIB_FILE, fetch=fake)
        self.assertEqual([h["state"] for h in r["hits"]], ["ok", "import", "missing"])

    def test_bridge_source_and_dependencies(self):
        b = BridgeProcess(self.project, os.path.dirname(self.project))
        try:
            st, src = b.call("/source", {"module": "Mathlib.Order.Lattice", "name": "sup_le"}, b.token)
            self.assertEqual(st, 200)
            self.assertTrue(src["text"].split("\n")[src["line"] - 1].startswith("theorem sup_le "))
            self.assertTrue(src["path"].startswith(".lake/packages/mathlib/"))
            self.assertEqual(b.call("/source", {"module": "Mathlib.Nope"}, b.token)[0], 400)
            st, pk = b.call("/packages", None, b.token)
            me = [x for x in pk["packages"] if x["name"] == pk["default"]][0]
            ml = [d for d in me["dependencies"] if d["name"] == "mathlib"][0]
            self.assertEqual(ml["library"], "Mathlib")
            self.assertGreater(ml["files"], 5000)
        finally:
            self.assertEqual(b.close(), b"", "the bridge wrote to stdout")


if __name__ == "__main__":
    unittest.main()
