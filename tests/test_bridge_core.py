"""The app-facing JSON decisions in core.py: goal parsing, declarations, request checks."""
import os
import unittest

from leanmcp import core
from leanmcp.core import UserError

# Real $/lean/plainGoal strings from SyntheticSystems/Systems/Category.lean (Lean 4.35).
GOALS = [
    "S : System\n⊢ ∀ {e : Entity} {d : Domain}, S.entityDomain e d → ∀ e' ∈ {e}, ∀ d' ∈ {d}, S.entityDomain e' d'",
    "S : System\ne : Entity\nd : Domain\nh : S.entityDomain e d\ne' : Entity\nhe : e' ∈ {e}\nd' : Domain\nhd : d' ∈ {d}\n⊢ S.entityDomain e' d'",
    "case onEntity\nS T U : System\nf : Hom S T\ng : Hom T U\n⊢ Entity → Set Entity",
    "case preserve\nS T U : System\nf : Hom S T\ng : Hom T U\n⊢ ∀ {e : Entity} {d : Domain},\n    S.entityDomain e d →\n      ∀ e' ∈ {u | ∃ t ∈ f.onEntity e, u ∈ g.onEntity t},\n        ∀ d' ∈ {u | ∃ t ∈ f.onDomain d, u ∈ g.onDomain t}, U.entityDomain e' d'",
    # constructed: a hypothesis whose type wraps, and a let-bound one
    "x : Nat := 3\nh :\n  a = b ∧\n    c = d\n⊢ True",
]


def unparse(g):
    lines = ["case " + g["case"]] if g["case"] is not None else []
    for h in g["hyps"]:
        if not h["names"]:
            lines.append(h["type"])
        else:
            sep = " :" if h["type"].startswith("\n") else " : "
            lines.append(" ".join(h["names"]) + sep + h["type"])
    return "\n".join(lines + ["⊢ " + g["target"]])


class ParseGoal(unittest.TestCase):
    def test_nothing_is_lost(self):
        # Invariant over every fixture: the parse is a lossless split of Lean's text.
        for s in GOALS:
            self.assertEqual(unparse(core.parse_goal(s)), s)

    def test_grouped_names_and_case(self):
        g = core.parse_goal(GOALS[2])
        self.assertEqual(g["case"], "onEntity")
        self.assertEqual(g["hyps"][0], {"names": ["S", "T", "U"], "type": "System"})
        self.assertEqual(g["target"], "Entity → Set Entity")

    def test_multiline_target_stays_one_target(self):
        g = core.parse_goal(GOALS[3])
        self.assertEqual(len(g["hyps"]), 3)
        self.assertTrue(g["target"].endswith("U.entityDomain e' d'"))
        self.assertEqual(g["target"].count("\n"), 3)

    def test_wrapped_hypothesis_and_let(self):
        g = core.parse_goal(GOALS[4])
        self.assertEqual(g["hyps"][0], {"names": ["x"], "type": "Nat := 3"})
        self.assertEqual(g["hyps"][1]["names"], ["h"])
        self.assertEqual(g["hyps"][1]["type"], "\n  a = b ∧\n    c = d")


SRC = """import Mathlib
/- a block comment
theorem not_real : True := trivial
/- nested -/ still comment -/
namespace X

@[simp]
def one : Nat := 1  -- theorem in a line comment

@[simp] theorem one_eq : one = 1 := rfl

private theorem hidden : True := by
  sorry

instance : Inhabited Nat := ⟨0⟩
example : 1 = 2 := by
  rfl
end X
"""


class Declarations(unittest.TestCase):
    def setUp(self):
        diags = [{"line": 12, "col": 16, "end_line": 12, "severity": "warning",
                  "message": "declaration uses `sorry`"},
                 {"line": 17, "col": 2, "end_line": 17, "severity": "error", "message": "rfl failed"}]
        self.d = core.declarations(SRC, diags)

    def test_found_in_order_skipping_comments(self):
        self.assertEqual([(x["line"], x["kind"], x["name"]) for x in self.d],
                         [(8, "def", "one"), (10, "theorem", "one_eq"), (12, "theorem", "hidden"),
                          (15, "instance", None), (16, "example", None)])

    def test_ranges_end_at_last_code_line_and_status(self):
        self.assertEqual([x["end_line"] for x in self.d], [8, 10, 13, 15, 17])
        self.assertEqual([x["status"] for x in self.d], ["ok", "ok", "sorry", "ok", "error"])

    def test_next_docstring_and_attribute_are_not_in_the_range(self):
        src = ("theorem a : True := by\n  trivial\n\n/-- Doc of b,\n  two lines. -/\n@[simp]\n"
               "theorem b : True := by\n  trivial\n\nend X\n")
        self.assertEqual([(x["line"], x["end_line"]) for x in core.declarations(src, [])], [(1, 2), (7, 8)])

    def test_column_zero_continuations_stay_in_the_range(self):
        src = "inductive S\n  | a | b\nderiving DecidableEq\n\ndef f : S → Nat\n| .a => 0\n| .b => 1\n"
        self.assertEqual([(x["line"], x["end_line"]) for x in core.declarations(src, [])], [(1, 3), (5, 7)])

    def test_error_beats_sorry(self):
        diags = [{"line": 3, "col": 0, "end_line": 3, "severity": "warning", "message": "declaration uses 'sorry'"},
                 {"line": 3, "col": 0, "end_line": 3, "severity": "error", "message": "x"}]
        d = core.declarations("\n\ntheorem t : True := sorry\n", diags)
        self.assertEqual(d[0]["status"], "error")


class CheckRequest(unittest.TestCase):
    def test_accepts(self):
        self.assertEqual(core.check_request({"file": "A.lean", "goals_at": [3]}), ("A.lean", None, [3], []))
        self.assertEqual(core.check_request({"file": "A.lean", "text": "x", "goals_after": [2]}),
                         ("A.lean", "x", [], [2]))

    def test_refuses(self):
        for body in ([], {}, {"file": 3}, {"file": "A.lean", "text": 1},
                     {"file": "A.lean", "goals_at": [0]}, {"file": "A.lean", "goals_at": [True]},
                     {"file": "A.lean", "goals_at": "3"}, {"file": "A.lean", "goals_at": list(range(1, 52))},
                     {"file": "/abs/Other.lean"}, {"file": "A.lean", "goals_after": [-1]},
                     {"file": "A.lean", "goals_at": list(range(1, 30)), "goals_after": list(range(1, 30))}):
            with self.assertRaises(UserError, msg=repr(body)):
                core.check_request(body)


class Payload(unittest.TestCase):
    def test_goals_parsed_and_missing_state_is_null(self):
        p = core.check_payload("A.lean", "theorem t : True := by\n  trivial\n", [],
                               {2: [GOALS[0]], 1: None}, 1.234)
        self.assertEqual([g["line"] for g in p["goals"]], [1, 2])
        self.assertIsNone(p["goals"][0]["goals"])
        self.assertEqual(p["goals"][1]["goals"][0]["hyps"][0]["names"], ["S"])
        self.assertEqual(p["declarations"][0]["name"], "t")
        self.assertEqual(p["seconds"], 1.23)
        self.assertEqual(p["goals_after"], [])
        q = core.check_payload("A.lean", "x", [], {}, 0, {1: []})
        self.assertEqual(q["goals_after"], [{"line": 1, "goals": []}])

    def test_end_column_is_after_last_visible_character(self):
        self.assertEqual(core.end_column("  exact h  "), 9)
        self.assertEqual(core.end_column("  rcases he with ⟨tE, 𝔽⟩"), 25)  # 𝔽 is two UTF-16 units


class Tokens(unittest.TestCase):
    LEGEND = ["keyword", "variable", "property", "function", "namespace", "leanSorryLike"]

    def test_relative_positions_decode_to_absolute(self):
        # line 0: `def` at 0; line 2: `h` at 8, then `.x` 3 further on the same line.
        data = [0, 0, 3, 0, 0,  2, 8, 1, 1, 0,  0, 3, 1, 2, 0]
        self.assertEqual(core.decode_tokens(data, self.LEGEND),
                         [[1, 0, 3, "keyword"], [3, 8, 1, "variable"], [3, 11, 1, "property"]])

    def test_new_line_resets_the_column(self):
        data = [1, 4, 2, 0, 0,  0, 5, 1, 1, 0,  1, 2, 1, 1, 0]
        self.assertEqual([t[:2] for t in core.decode_tokens(data, self.LEGEND)], [[2, 4], [2, 9], [3, 2]])

    def test_kinds_are_mapped_and_unknown_ones_dropped(self):
        data = [0, 0, 5, 5, 0,  0, 6, 2, 4, 0,  0, 3, 1, 9, 0,  0, 2, 1, 3, 0]
        self.assertEqual(core.decode_tokens(data, self.LEGEND), [[1, 0, 5, "sorry"], [1, 11, 1, "function"]])

    def test_malformed_data_gives_nothing(self):
        for data in (None, [], [0, 0, 3, 0]):
            self.assertEqual(core.decode_tokens(data, self.LEGEND), [])

    def test_payload_carries_tokens(self):
        self.assertEqual(core.check_payload("A.lean", "x", [], {}, 0)["tokens"], [])
        self.assertEqual(core.check_payload("A.lean", "x", [], {}, 0, None, [[1, 0, 1, "keyword"]])["tokens"],
                         [[1, 0, 1, "keyword"]])


class Save(unittest.TestCase):
    def setUp(self):
        import tempfile
        self.root = tempfile.mkdtemp()
        os.makedirs(os.path.join(self.root, "A"))
        os.makedirs(os.path.join(self.root, ".lake", "packages"))
        self.path = os.path.join(self.root, "A", "B.lean")
        with open(self.path, "w", encoding="utf-8") as f:
            f.write("theorem t : True := by\n  sorry\n")
        os.chmod(self.path, 0o640)
        with open(os.path.join(self.root, ".lake", "packages", "D.lean"), "w") as f:
            f.write("x")

    def read(self):
        with open(self.path, encoding="utf-8") as f:
            return f.read()

    def test_writes_when_disk_equals_base(self):
        base = self.read()
        new = "theorem t : True := by\n  trivial -- ⊢ 𝔽\n"
        n = core.write_if_unchanged(self.root, "A/B.lean", new, base)
        self.assertEqual(self.read(), new)
        self.assertEqual(n, len(new.encode("utf-8")))
        self.assertEqual(os.stat(self.path).st_mode & 0o777, 0o640)
        self.assertEqual(sorted(os.listdir(os.path.join(self.root, "A"))), ["B.lean"])  # no temp file left

    def test_refuses_when_disk_changed(self):
        before = self.read()
        with self.assertRaisesRegex(UserError, "changed on disk"):
            core.write_if_unchanged(self.root, "A/B.lean", "new", before + "edited elsewhere")
        self.assertEqual(self.read(), before)

    def test_refuses_new_files_and_dot_dirs(self):
        for rel in ("A/New.lean", ".lake/packages/D.lean"):
            with self.assertRaisesRegex(UserError, "not an existing source"):
                core.write_if_unchanged(self.root, rel, "x", "x")
        self.assertFalse(os.path.exists(os.path.join(self.root, "A", "New.lean")))

    def test_request(self):
        self.assertEqual(core.save_request({"file": "A.lean", "text": "t", "base": "b"}), ("A.lean", "t", "b"))
        for bad in (None, [], {"file": "A.lean", "text": "t"}, {"file": "/abs/A.lean", "text": "t", "base": "b"},
                    {"file": "A.lean", "text": 3, "base": "b"}, {"file": "", "text": "t", "base": "b"}):
            with self.assertRaises(UserError):
                core.save_request(bad)


class Create(unittest.TestCase):
    def setUp(self):
        import tempfile
        self.root = tempfile.mkdtemp()
        os.makedirs(os.path.join(self.root, "Lib", "Sub"))
        os.makedirs(os.path.join(self.root, ".lake", "Pkg"))
        self.write("Lib.lean", "import Lib.Sub.A\nimport Lib.Sub.B\n")
        self.write("Lib/Sub/A.lean", "theorem a : True := trivial\n")
        self.write(".lake/Pkg/D.lean", "x")

    def write(self, rel, text):
        with open(os.path.join(self.root, rel), "w", encoding="utf-8") as f:
            f.write(text)

    def read(self, rel):
        with open(os.path.join(self.root, rel), encoding="utf-8") as f:
            return f.read()

    def test_creates_and_registers(self):
        n, reg = core.create_source(self.root, "Lib/Sub/New.lean", "namespace X\nend X\n")
        self.assertEqual((n, reg), (len("namespace X\nend X\n"), "Lib.lean"))
        self.assertEqual(self.read("Lib/Sub/New.lean"), "namespace X\nend X\n")
        self.assertEqual(self.read("Lib.lean"), "import Lib.Sub.A\nimport Lib.Sub.B\nimport Lib.Sub.New\n")

    def test_new_folder_below_a_library(self):
        core.create_source(self.root, "Lib/Fresh/Deep.lean", "")
        self.assertIn("Lib/Fresh/Deep.lean", core.list_sources(self.root))
        self.assertTrue(self.read("Lib.lean").endswith("import Lib.Fresh.Deep\n"))

    def test_refuses(self):
        before = (core.list_sources(self.root), self.read("Lib.lean"))
        for rel, why in (("Lib/Sub/A.lean", "already exists"), ("Top.lean", "Library>/<Name>"),
                         ("Lib/sub/x.lean", "Library>/<Name>"), ("Lib/Sub/A.txt", "Library>/<Name>"),
                         ("Other/New.lean", "existing library"), (".lake/Pkg/New.lean", "Library>/<Name>"),
                         ("Lib/../Other/X.lean", "Library>/<Name>")):
            with self.assertRaisesRegex(UserError, why, msg=rel):
                core.create_source(self.root, rel, "x")
        self.assertEqual((core.list_sources(self.root), self.read("Lib.lean")), before)
        self.assertEqual(self.read("Lib/Sub/A.lean"), "theorem a : True := trivial\n")

    def test_add_import(self):
        self.assertEqual(core.add_import("import A\n\ndef x := 1\n", "B"), "import A\nimport B\n\ndef x := 1\n")
        self.assertEqual(core.add_import("def x := 1\n", "B"), "import B\ndef x := 1\n")
        self.assertEqual(core.add_import("import A\nimport B\n", "B"), "import A\nimport B\n")
        self.assertEqual(core.add_import("import A.BC\n", "A.B"), "import A.BC\nimport A.B\n")

    def test_request(self):
        self.assertEqual(core.create_request({"file": "L/A.lean", "text": ""}), ("L/A.lean", ""))
        for bad in (None, {"file": "L/A.lean"}, {"file": "/abs/A.lean", "text": ""}, {"file": "", "text": ""}):
            with self.assertRaises(UserError):
                core.create_request(bad)


class Overview(unittest.TestCase):
    def setUp(self):
        import tempfile
        self.root = tempfile.mkdtemp()
        os.makedirs(os.path.join(self.root, "Lib", "Sub"))
        files = {
            "Lib.lean": "import Lib.Sub.A\nimport Mathlib\n",
            "Lib/Sub/A.lean": "/-!\n# Generation (step 4)\n\ntext -/\ntheorem a : True := by\n  sorry -- sorry\n"
                              "/- sorry -/\ndef b := 1\nscoped infixl:65 \" ⋆ \" => f\n",
            "Lib/Sub/Empty.lean": "\n",
            "Scratch.lean": "def x := sorry\n",
        }
        for rel, text in files.items():
            with open(os.path.join(self.root, rel), "w", encoding="utf-8") as f:
                f.write(text)

    def test_overview(self):
        got = {f["path"]: f for f in core.file_overview(self.root)["files"]}
        self.assertEqual(got["Lib.lean"]["role"], "root")
        self.assertEqual(got["Lib/Sub/A.lean"], {"path": "Lib/Sub/A.lean", "title": "Generation (step 4)", "decls": 3,
                                                 "sorries": 1, "empty": False, "role": "imported"})
        self.assertEqual((got["Lib/Sub/Empty.lean"]["role"], got["Lib/Sub/Empty.lean"]["empty"]), ("unimported", True))
        self.assertEqual((got["Scratch.lean"]["role"], got["Scratch.lean"]["sorries"]), ("other", 1))

    def test_notation_is_a_declaration(self):
        text = "def f := 1\n\nscoped infixl:65 \" ⋆ \" => f\nnotation:50 a \" ≺ \" b => f a b\nprefix:max \"√\" => g\n"
        ds = core.declarations(text, [])
        self.assertEqual([(d["kind"], d["name"], d["line"], d["end_line"]) for d in ds],
                         [("def", "f", 1, 1), ("infixl", "⋆", 3, 3), ("notation", "≺", 4, 4), ("prefix", "√", 5, 5)])


class Abbreviations(unittest.TestCase):
    def setUp(self):
        import tempfile
        self.root = tempfile.mkdtemp()

    def test_round_trip(self):
        self.assertEqual(core.read_abbreviations(self.root), {})
        self.assertEqual(core.write_abbreviation(self.root, "cmb", "⋆"), {"cmb": "⋆"})
        core.write_abbreviation(self.root, "aa", "≺")
        self.assertEqual(core.read_abbreviations(self.root), {"aa": "≺", "cmb": "⋆"})
        self.assertEqual(core.write_abbreviation(self.root, "cmb", ""), {"aa": "≺"})
        self.assertEqual(os.listdir(os.path.join(self.root, ".leanwb")), ["abbreviations.json"])
        self.assertNotIn(".leanwb/abbreviations.json", core.list_sources(self.root))

    def test_bad_file_and_requests(self):
        os.makedirs(os.path.join(self.root, ".leanwb"))
        with open(os.path.join(self.root, ".leanwb", "abbreviations.json"), "w") as f:
            f.write("[1]")
        with self.assertRaisesRegex(UserError, "object"):
            core.read_abbreviations(self.root)
        self.assertEqual(core.abbreviation_request({"name": "cmb", "symbol": "⋆"}), ("cmb", "⋆"))
        for bad in (None, {"name": "a b", "symbol": "x"}, {"name": "a\\b", "symbol": "x"}, {"name": "", "symbol": "x"},
                    {"name": "a", "symbol": 1}, {"name": "a", "symbol": "x\ny"}):
            with self.assertRaises(UserError):
                core.abbreviation_request(bad)


class Complete(unittest.TestCase):
    def test_fragment(self):
        cases = [("  exact ⟨hE.trans h1, hD.tr", "tr"), ("  exact Finset.union_co", "union_co"),
                 ("  exact h3 (h", "h"), ("  exact ", ""), ("  simp [h₁", "h₁"), ("  exact 𝔽.x", "x")]
        for line, frag in cases:
            self.assertEqual(core.completion_fragment(line, core.utf16_len(line)), frag, line)
        self.assertEqual(core.completion_fragment("  exact hD.trans h1", 13), "tr")  # cursor mid-line

    def test_rank(self):
        items = [{"label": "Batteries.x.hash", "kind": 3}, {"label": "hD", "kind": 6}, {"label": "h1", "kind": 6},
                 {"label": "trans", "kind": 23}, {"label": "eq_or_lt", "kind": 23}, {"label": "trans_ssubset", "kind": 23},
                 {"label": "Nat.hmul", "kind": 3}, {"label": "hD", "kind": 6}]
        self.assertEqual([i["label"] for i in core.rank_completions(items, "h")], ["h1", "hD", "Nat.hmul", "Batteries.x.hash"])
        self.assertEqual([i["label"] for i in core.rank_completions(items, "tr")], ["trans", "trans_ssubset"])
        self.assertEqual([i["label"] for i in core.rank_completions(items, "ssub")], ["trans_ssubset"])  # contains
        locals_first = [{"label": "hash", "kind": 3}, {"label": "hypothesis_long", "kind": 6}]
        self.assertEqual([i["label"] for i in core.rank_completions(locals_first, "h")], ["hypothesis_long", "hash"])
        self.assertEqual(len(core.rank_completions([{"label": f"a{i}", "kind": 3} for i in range(99)], "a")), 20)

    def test_request(self):
        self.assertEqual(core.complete_request({"file": "A.lean", "text": "t", "line": 1, "col": 0}), ("A.lean", "t", 1, 0))
        for bad in ({"file": "A.lean", "text": "t", "line": 0, "col": 0}, {"file": "A.lean", "text": "t", "line": 1, "col": -1},
                    {"file": "A.lean", "line": 1, "col": 0}, {"file": "/a.lean", "text": "", "line": 1, "col": 0},
                    {"file": "A.lean", "text": "t", "line": True, "col": 0}):
            with self.assertRaises(UserError):
                core.complete_request(bad)


if __name__ == "__main__":
    unittest.main()


FIX = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fixtures")


def fixture(name):
    import json
    with open(os.path.join(FIX, name), encoding="utf-8") as f:
        return json.load(f)


class ApiSearch(unittest.TestCase):
    """/v1/search: request checks, the two services' real answers, the scope check's Lean text."""

    def test_request(self):
        self.assertEqual(core.api_search_request({"engine": "loogle", "query": " |- _ ⊔ _ ≤ _ "}),
                         ("loogle", "|- _ ⊔ _ ≤ _", None, None))
        self.assertEqual(core.api_search_request({"engine": "leansearch", "query": "q", "file": "A.lean", "text": "t"}),
                         ("leansearch", "q", "A.lean", "t"))
        for bad in [{"engine": "google", "query": "q"}, {"engine": "loogle", "query": "  "},
                    {"engine": "loogle", "query": "x" * 501}, {"engine": "loogle", "query": "q", "text": "t"},
                    {"engine": "loogle", "query": "q", "file": 3}, []]:
            with self.assertRaises(UserError):
                core.api_search_request(bad)

    def test_loogle_url_encodes_everything(self):
        u = core.loogle_url("|- _ ⊔ _ ≤ _, Finset.sum & x")
        self.assertTrue(u.startswith(core.LOOGLE_URL + "?q="))
        self.assertNotIn(" ", u); self.assertNotIn("&", u.split("?q=")[1]); self.assertNotIn("⊔", u)

    def test_parse_loogle_real_answer(self):
        # Fetched 2026-09-23: loogle.lean-lang.org/json?q=|- _ ⊔ _ ≤ _
        r = core.parse_loogle(fixture("loogle_sup_le.json"))
        self.assertEqual(r["count"], 75)
        self.assertIsNone(r["error"])
        self.assertLessEqual(len(r["hits"]), core.API_MAX_HITS)
        sup = [h for h in r["hits"] if h["name"] == "sup_le"][0]
        self.assertEqual(sup["module"], "Mathlib.Order.Lattice")
        self.assertIn("a ⊔ b ≤ c", sup["type"])
        self.assertNotIn("\n", sup["type"])

    def test_parse_loogle_error_is_data(self):
        r = core.parse_loogle(fixture("loogle_error.json"))
        self.assertEqual((r["hits"], r["count"]), ([], 0))
        self.assertIn("unknown identifier", r["error"])
        self.assertEqual(r["suggestions"], ['"Finset.sum_comn"'])

    def test_parse_leansearch_real_answer(self):
        r = core.parse_leansearch(fixture("leansearch_sup_le.json"))
        self.assertEqual([h["name"] for h in r["hits"]][:3], ["SemilatticeSup.sup_le", "sup_le", "sup_le_iff"])
        self.assertEqual(r["hits"][1]["module"], "Mathlib.Order.Lattice")
        self.assertTrue(r["hits"][1]["informal"].startswith("Supremum"))
        with self.assertRaises(UserError):
            core.parse_leansearch({"hits": []})

    def test_exists_snippet(self):
        hits = [core._hit("sup_le", "t", "Mathlib.Order.Lattice"), core._hit('a"b', "t", "M"),
                core._hit("«term_∘_»", "t", "M"), core._hit("x", "t", "../etc")]
        s = core.exists_snippet(hits)
        self.assertIn('("sup_le", "Mathlib.Order.Lattice")', s)
        self.assertNotIn('a"b', s); self.assertNotIn("«", s); self.assertNotIn("../etc", s)
        self.assertIn(core.EXISTS_MARK, s)
        self.assertIsNone(core.exists_snippet(hits[1:]))

    def test_parse_exists_and_mark(self):
        msg = core.EXISTS_MARK + "\nok sup_le\nimport Real.pi_gt_three\nmissing sup_le_nope"
        st = core.parse_exists([{"message": msg, "severity": "info", "line": 9}], 9)
        self.assertEqual(st, {"sup_le": "ok", "Real.pi_gt_three": "import", "sup_le_nope": "missing"})
        with self.assertRaises(UserError):
            core.parse_exists([{"message": "boom", "severity": "error", "line": 10}], 9)
        with self.assertRaises(UserError):
            core.parse_exists([], 9)
        marked = core.mark_hits([{"name": "sup_le"}, {"name": "«x»"}], st)
        self.assertEqual([h["state"] for h in marked], ["ok", "unchecked"])


class Toolbox(unittest.TestCase):
    def setUp(self):
        import tempfile
        self.root = tempfile.mkdtemp(dir=os.environ.get("TMPDIR"))

    def tearDown(self):
        import shutil
        shutil.rmtree(self.root)

    def test_request(self):
        e, p = core.toolbox_request({"name": "sup_le", "module": "Mathlib.Order.Lattice", "type": "a\n  ≤ c", "pinned": True})
        self.assertEqual((e, p), ({"name": "sup_le", "module": "Mathlib.Order.Lattice", "type": "a ≤ c"}, True))
        for bad in [{"name": "a b", "pinned": True}, {"name": "x", "pinned": "yes"},
                    {"name": "x", "module": "../m", "pinned": True}, {"name": "x", "type": 3, "pinned": True}]:
            with self.assertRaises(UserError):
                core.toolbox_request(bad)

    def test_pin_once_unpin_and_only_that_file(self):
        self.assertEqual(core.read_toolbox(self.root), [])
        a = {"name": "sup_le", "module": "M", "type": "t"}
        b = {"name": "le_inf", "module": "M", "type": "u"}
        core.write_toolbox(self.root, a, True)
        core.write_toolbox(self.root, b, True)
        box = core.write_toolbox(self.root, a, True)          # pinning again moves it last, once
        self.assertEqual([e["name"] for e in box], ["le_inf", "sup_le"])
        self.assertEqual(core.write_toolbox(self.root, b, False), [a])
        self.assertEqual(core.read_toolbox(self.root), [a])
        files = [os.path.relpath(os.path.join(d, f), self.root) for d, _, fs in os.walk(self.root) for f in fs]
        self.assertEqual(files, [core.TOOLBOX_FILE])

    def test_bad_file_is_an_error(self):
        os.makedirs(os.path.join(self.root, ".leanwb"))
        with open(os.path.join(self.root, core.TOOLBOX_FILE), "w") as f:
            f.write('{"a": 1}')
        with self.assertRaises(UserError):
            core.read_toolbox(self.root)


class Source(unittest.TestCase):
    TEXT = "\n".join(["namespace Real", "", "/-- doc -/", "theorem pi_gt_three : 3 < π := by", "  sorry",
                      "@[simp] protected lemma Foo.bar : True := trivial", "theorem pi_gt_three' : True := trivial"])

    def test_request(self):
        self.assertEqual(core.source_request({"module": "Mathlib.Order.Lattice", "name": "sup_le"}),
                         ("Mathlib.Order.Lattice", "sup_le"))
        for bad in [{"module": "../x"}, {"module": "A/B"}, {"module": "A", "name": "a b"}, {}]:
            with self.assertRaises(UserError):
                core.source_request(bad)

    def test_declaration_line(self):
        self.assertEqual(core.declaration_line(self.TEXT, "Real.pi_gt_three"), 4)   # not pi_gt_three'
        self.assertEqual(core.declaration_line(self.TEXT, "Real.Foo.bar"), 6)
        self.assertEqual(core.declaration_line(self.TEXT, "nowhere"), 1)
        self.assertEqual(core.declaration_line(self.TEXT, ""), 1)

    def test_session_reads_packages_and_refuses_escapes(self):
        import tempfile, shutil
        from leanmcp.session import Session
        root = tempfile.mkdtemp(dir=os.environ.get("TMPDIR"))
        outside = tempfile.mkdtemp(dir=os.environ.get("TMPDIR"))
        try:
            pk = os.path.join(root, ".lake", "packages", "mathlib", "Mathlib", "Order")
            os.makedirs(pk)
            with open(os.path.join(pk, "Lattice.lean"), "w") as f:
                f.write("x\ntheorem sup_le : True := trivial\n")
            with open(os.path.join(outside, "Secret.lean"), "w") as f:
                f.write("secret")
            os.symlink(os.path.join(outside, "Secret.lean"), os.path.join(root, "Secret.lean"))
            s = Session(root, idle_seconds=0)
            r = s.source("Mathlib.Order.Lattice", "sup_le")
            self.assertEqual((r["path"], r["line"]), (os.path.join(".lake", "packages", "mathlib", "Mathlib", "Order", "Lattice.lean"), 2))
            with self.assertRaises(UserError):
                s.source("Secret", "")
            with self.assertRaises(UserError):
                s.source("Mathlib.Nope", "")
        finally:
            shutil.rmtree(root); shutil.rmtree(outside)

    def test_api_search_without_expressible_names_skips_lean(self):
        from leanmcp.session import Session
        s = Session("/nonexistent", idle_seconds=0)
        fake = lambda url, data=None: {"count": 1, "hits": [{"name": "«x»", "type": "t", "module": "M", "doc": None}]}
        r = s.api_search("loogle", "q", fetch=fake)
        self.assertEqual([h["state"] for h in r["hits"]], ["unchecked"])
        self.assertEqual((r["engine"], r["query"], r["count"]), ("loogle", "q", 1))


class Packages(unittest.TestCase):
    """Packages, their libraries and dependencies, a new library (all on temp trees)."""

    TOML = 'name = "demo"\ndefaultTargets = ["Demo"]\n\n[[require]]\nname = "mathlib"\n\n[[lean_lib]]\nname = "Demo"\n'

    def setUp(self):
        import tempfile
        self.base = tempfile.mkdtemp(dir=os.environ.get("TMPDIR"))
        self.root = os.path.join(self.base, "demo")
        self.w("lakefile.toml", self.TOML)
        self.w("lean-toolchain", "leanprover/lean4:v4.35.0-rc2\n")
        self.w("Demo.lean", "import Demo.A\n")
        self.w("Demo/A.lean", "/-! # Alpha -/\ntheorem a : True := sorry\n")
        self.w("Demo/B.lean", "theorem b : True := trivial\n")
        self.w("Old/C.lean", "def c := 1\n")          # a folder the lakefile does not declare
        self.w("Scratch.lean", "example : True := trivial\n")
        os.makedirs(os.path.join(self.base, "not-a-package"))

    def tearDown(self):
        import shutil
        shutil.rmtree(self.base)

    def w(self, rel, text, root=None):
        path = os.path.join(root or self.root, rel)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as f:
            f.write(text)

    def files(self):
        return sorted(os.path.relpath(os.path.join(d, f), self.root) for d, _, fs in os.walk(self.root) for f in fs)

    def test_lakefile_libs(self):
        self.assertEqual(core.lakefile_libs(self.root), (["Demo"], ["Demo"]))
        lean = os.path.join(self.base, "lean")
        self.w("lakefile.lean", "import Lake\nopen Lake DSL\npackage x\n@[default_target]\nlean_lib Mathlib where\n"
               "lean_lib Cache\nlean_lib «MathlibTest» where\n", root=lean)
        self.assertEqual(core.lakefile_libs(lean), (["Mathlib", "Cache", "MathlibTest"], ["Mathlib"]))
        self.assertEqual(core.lakefile_libs(os.path.join(self.base, "not-a-package")), ([], []))

    def test_main_library(self):
        self.assertEqual(core.main_library("mathlib", ["Mathlib", "Cache", "MathlibTest"], []), "Mathlib")
        self.assertEqual(core.main_library("plausible", ["PlausibleTest", "Plausible"], ["Plausible"]), "Plausible")
        self.assertEqual(core.main_library("proofwidgets", ["ProofWidgets", "test"], []), "ProofWidgets")
        self.assertEqual(core.main_library("x", ["XTest", "Other"], []), "Other")
        self.assertIsNone(core.main_library("x", [], []))

    def test_libraries_and_membership(self):
        libs = core.library_names(self.root)
        self.assertEqual(libs, ["Demo", "Old"])
        self.assertEqual([core.library_of(p, libs) for p in ["Demo.lean", "Demo/A.lean", "Old/C.lean", "Scratch.lean", "Demon.lean"]],
                         ["Demo", "Demo", "Old", None, None])

    def test_package_overview(self):
        ov = core.package_overview(self.root)
        self.assertEqual((ov["name"], ov["toolchain"], ov["lakefile"]), ("demo", "v4.35.0-rc2", "lakefile.toml"))
        demo = ov["libraries"][0]
        self.assertEqual((demo["name"], demo["root"]), ("Demo", "Demo.lean"))
        roles = {f["path"]: f["role"] for f in demo["files"]}
        self.assertEqual(roles, {"Demo.lean": "root", "Demo/A.lean": "imported", "Demo/B.lean": "unimported"})
        self.assertEqual([f["path"] for f in ov["loose"]], ["Scratch.lean"])
        # Nothing is lost: every source is in exactly one library or loose.
        seen = [f["path"] for l in ov["libraries"] for f in l["files"]] + [f["path"] for f in ov["loose"]]
        self.assertEqual(sorted(seen), core.list_sources(self.root))

    def test_dependencies(self):
        self.w("lake-manifest.json", '{"packages": [{"name": "mathlib", "rev": "0653561abcdef", "inputRev": "v4.35.0-rc2"},'
               ' {"name": "gone", "rev": "1"}]}')
        pk = os.path.join(self.root, ".lake", "packages", "mathlib")
        self.w("lakefile.lean", "lean_lib Mathlib\nlean_lib MathlibTest\n", root=pk)
        self.w("Mathlib.lean", "", root=pk)
        self.w("Mathlib/Order/Lattice.lean", "", root=pk)
        self.w("Mathlib/Data/X.lean", "", root=pk)
        self.w("MathlibTest/T.lean", "", root=pk)
        cards = core.dependency_cards(self.root)
        self.assertEqual(cards, [{"name": "mathlib", "rev": "0653561", "inputRev": "v4.35.0-rc2", "library": "Mathlib", "files": 3}])
        self.assertEqual(core.read_manifest(os.path.join(self.base, "not-a-package")), [])

    def test_find_packages(self):
        self.assertEqual(core.find_packages(self.base), ["demo"])
        self.assertEqual(core.find_packages(os.path.join(self.base, "nope")), [])

    def test_git_and_ci_parsing(self):
        st = core.parse_git_status("# branch.oid abc\n# branch.head main\n# branch.upstream origin/main\n"
                                   "# branch.ab +2 -1\n1 .M N... 100644 100644 100644 a b f.lean\n? new.lean\n")
        self.assertEqual(st, {"branch": "main", "changed": 2, "ahead": 2, "behind": 1})
        self.assertEqual(core.parse_git_status("# branch.head main\n")["ahead"], 0)
        ci = core.parse_ci('[{"status":"completed","conclusion":"success","createdAt":"2026-09-22T12:43:16Z",'
                           '"headSha":"c9a3c27ffff","workflowName":"Lean Action CI"}]')
        self.assertEqual(ci, {"status": "completed", "conclusion": "success", "at": "2026-09-22T12:43:16Z",
                              "sha": "c9a3c27", "workflow": "Lean Action CI"})
        self.assertIsNone(core.parse_ci("[]"))
        self.assertIsNone(core.parse_ci("not json"))

    def test_add_library_writes_two_files(self):
        before = {f: open(os.path.join(self.root, f), encoding="utf-8").read() for f in self.files()}
        self.assertEqual(core.add_library(self.root, "Examples"), ("lakefile.toml", "Examples.lean"))
        after = self.files()
        self.assertEqual(sorted(set(after) - set(before)), ["Examples.lean"])
        changed = [f for f in before if open(os.path.join(self.root, f), encoding="utf-8").read() != before[f]]
        self.assertEqual(changed, ["lakefile.toml"])
        self.assertEqual(core.lakefile_libs(self.root), (["Demo", "Examples"], ["Demo", "Examples"]))
        self.assertEqual(core.library_names(self.root), ["Demo", "Examples", "Old"])
        # The new library takes new files, registered in its root.
        self.assertEqual(core.create_source(self.root, "Examples/Small.lean", "theorem s : True := trivial\n"),
                         (len("theorem s : True := trivial\n"), "Examples.lean"))
        self.assertIn("import Examples.Small", open(os.path.join(self.root, "Examples.lean")).read())
        roles = {f["path"]: f["role"] for f in core.file_overview(self.root)["files"]}
        self.assertEqual((roles["Examples.lean"], roles["Examples/Small.lean"]), ("root", "imported"))

    def test_add_library_refusals(self):
        for name in ["Demo", "Old"]:
            with self.assertRaises(UserError):
                core.add_library(self.root, name)
        self.w("Taken.lean", "")
        with self.assertRaises(UserError):
            core.add_library(self.root, "Taken")
        lean = os.path.join(self.base, "lean")
        self.w("lakefile.lean", "lean_lib A\n", root=lean)
        with self.assertRaises(UserError):
            core.add_library(lean, "B")
        for bad in [{"name": "lower"}, {"name": "A/B"}, {"name": ""}, {}]:
            with self.assertRaises(UserError):
                core.library_request(bad)
        self.assertEqual(open(os.path.join(self.root, "lakefile.toml")).read(), self.TOML)

    def test_add_library_without_default_targets(self):
        self.w("lakefile.toml", 'name = "demo"\n\n[[lean_lib]]\nname = "Demo"\n')
        core.add_library(self.root, "Examples")
        self.assertEqual(core.lakefile_libs(self.root), (["Demo", "Examples"], []))
