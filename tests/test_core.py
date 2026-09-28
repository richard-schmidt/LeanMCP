import os
import tempfile
import unittest

from leanmcp import core
from leanmcp.core import UserError


class FindProject(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = os.path.realpath(self.tmp.name)
        open(os.path.join(self.root, "lakefile.toml"), "w").close()
        os.makedirs(os.path.join(self.root, "A", "B"))

    def tearDown(self):
        self.tmp.cleanup()

    def test_relative_is_relative_to_default(self):
        self.assertEqual(core.find_project("A/B/X.lean", self.root), (self.root, "A/B/X.lean"))

    def test_absolute_walks_up_to_lakefile(self):
        p = os.path.join(self.root, "A", "B", "X.lean")
        self.assertEqual(core.find_project(p, "/nonexistent"), (self.root, "A/B/X.lean"))

    def test_refuses_escape_and_non_lean(self):
        with self.assertRaises(UserError):
            core.find_project("../outside.lean", self.root)
        with self.assertRaises(UserError):
            core.find_project("A/notes.md", self.root)
        with self.assertRaises(UserError):
            core.find_project("/tmp/definitely/not/a/project/X.lean", self.root)


class Staleness(unittest.TestCase):
    def test_snapshot_skips_dot_dirs_and_non_lean(self):
        with tempfile.TemporaryDirectory() as root:
            for rel in ["A.lean", "S/B.lean", ".lake/packages/m/C.lean", "notes.md"]:
                os.makedirs(os.path.dirname(os.path.join(root, rel)) or root, exist_ok=True)
                open(os.path.join(root, rel), "w").write("x")
            self.assertEqual(sorted(core.source_snapshot(root)), ["A.lean", "S/B.lean"])

    def test_dependency_edit_is_detected_own_edit_is_not(self):
        before = {"P.lean": (1, 10), "Q.lean": (1, 10)}
        self.assertFalse(core.dependencies_changed(before, dict(before), "Q.lean"))
        self.assertFalse(core.dependencies_changed(before, {**before, "Q.lean": (2, 11)}, "Q.lean"))
        self.assertTrue(core.dependencies_changed(before, {**before, "P.lean": (2, 10)}, "Q.lean"))
        self.assertTrue(core.dependencies_changed(before, {**before, "N.lean": (1, 1)}, "Q.lean"))
        self.assertTrue(core.dependencies_changed(before, {"Q.lean": (1, 10)}, "Q.lean"))


class Positions(unittest.TestCase):
    def test_utf16_counts_astral_as_two(self):
        self.assertEqual(core.utf16_len("ℕ∪"), 2)      # BMP: one unit each
        self.assertEqual(core.utf16_len("𝓒x"), 3)      # astral: two units

    def test_goal_column(self):
        self.assertEqual(core.goal_column("    simp"), 4)
        self.assertEqual(core.goal_column("\t𝓒"), 1)


DOC = "theorem t : P := by\n  intro h\n  sorry\nend"


class Splice(unittest.TestCase):
    def test_lone_sorry_single_line(self):
        new, a, b, _ = core.splice(DOC, 3, "simp")
        self.assertEqual(new, "theorem t : P := by\n  intro h\n  simp\nend")
        self.assertEqual((a, b), (3, 3))

    def test_lone_sorry_multi_line_inherits_indent(self):
        new, a, b, _ = core.splice(DOC, 3, "constructor\n· simp\n· rfl")
        self.assertEqual(new.split("\n")[2:5], ["  constructor", "  · simp", "  · rfl"])
        self.assertEqual((a, b), (3, 5))
        self.assertEqual(new.split("\n")[-1], "end")

    def test_candidate_own_indentation_is_normalised(self):
        new, _, _, _ = core.splice(DOC, 3, "    cases h\n      rfl")
        self.assertEqual(new.split("\n")[2:4], ["  cases h", "    rfl"])

    def test_inline_sorry_replaces_token_only(self):
        doc = "theorem t : P := by sorry\nend"
        new, a, b, _ = core.splice(doc, 1, "simp")
        self.assertEqual(new, "theorem t : P := by simp\nend")
        self.assertEqual((a, b), (1, 1))

    def test_end_col_is_end_of_candidate_not_of_line(self):
        # `sorry⟩`: the goals after the tactic live before the `⟩`, not after it.
        doc = "def h : X := ⟨f, by\n    sorry⟩"
        new, _, _, col = core.splice(doc, 2, "simp at h")
        self.assertEqual(new.split("\n")[1], "    simp at h⟩")
        self.assertEqual(col, len("    simp at h"))
        new, _, _, col = core.splice("  exact (by sorry) x", 1, "rfl")
        self.assertEqual(col, len("  exact (by rfl"))
        new, _, _, col = core.splice(DOC, 3, "cases h\n  · 𝓒")
        self.assertEqual(col, len("    · ") + 2)                  # astral 𝓒 counts 2
        _, _, _, col = core.splice(DOC, 2, "intro x")               # no sorry: line end
        self.assertEqual(col, len("  intro x"))

    def test_inline_sorry_refuses_multi_line(self):
        with self.assertRaises(UserError):
            core.splice("theorem t : P := by sorry", 1, "constructor\nsimp")

    def test_no_sorry_replaces_whole_line(self):
        new, _, _, _ = core.splice(DOC, 2, "intro x")
        self.assertEqual(new.split("\n")[1], "  intro x")

    def test_sorry_inside_identifier_is_not_a_slot(self):
        doc = "  exact not_sorryish"
        new, _, _, _ = core.splice(doc, 1, "rfl")
        self.assertEqual(new, "  rfl")

    def test_bad_line_and_empty_candidate(self):
        for line, cand in [(0, "simp"), (5, "simp"), (3, ""), (3, "\n\n")]:
            with self.assertRaises(UserError):
                core.splice(DOC, line, cand)

    def test_invariant_other_lines_untouched(self):
        # Every line outside the candidate's span is byte-identical, whatever the candidate.
        for cand in ["simp", "a\nb\nc", "  x\n    y", "exact (by simp)"]:
            for line in (2, 3):
                new, a, b, _ = core.splice(DOC, line, cand)
                old_l, new_l = DOC.split("\n"), new.split("\n")
                self.assertEqual(new_l[: a - 1], old_l[: line - 1])
                self.assertEqual(new_l[b:], old_l[line:])


def diag(line, sev, msg, col=0):
    return {"line": line, "col": col, "end_line": line, "severity": sev, "message": msg}


class Verdicts(unittest.TestCase):
    def test_error_on_candidate_lines(self):
        self.assertEqual(core.verdict([diag(3, "error", "x")], 3, 3, []), "error")

    def test_error_elsewhere_does_not_blame_candidate(self):
        # "unsolved goals" lands on the theorem's line, not the tactic's.
        self.assertEqual(core.verdict([diag(1, "error", "unsolved goals")], 3, 3, ["⊢ P"]), "progress")

    def test_no_goals_and_unknown(self):
        self.assertEqual(core.verdict([], 3, 4, []), "no goals")
        self.assertEqual(core.verdict([], 3, 4, None), "unknown")

    def test_normalise_sorts_and_maps(self):
        raw = [{"range": {"start": {"line": 4, "character": 2}, "end": {"line": 4, "character": 5}},
                "severity": 2, "message": "declaration uses 'sorry'"},
               {"range": {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 1}},
                "severity": 1, "message": "boom"}]
        out = core.normalise_diagnostics(raw)
        self.assertEqual([(d["line"], d["severity"]) for d in out], [(1, "error"), (5, "warning")])
        self.assertEqual(core.sorry_lines(out), [5])

    def test_sorry_matches_both_quote_styles(self):
        # The backtick form is verbatim from Lean 4.35.0-rc2; the quote form from older Lean.
        new = diag(30, "warning", "declaration uses `sorry`")
        old = diag(31, "warning", "declaration uses 'sorry'")
        self.assertEqual(core.sorry_lines([new, old, diag(32, "warning", "unused variable `sorry`")]), [30, 31])
        r = core.parse_build("warning: X.lean:30:8: declaration uses `sorry`\n", 0)
        self.assertEqual((len(r["sorries"]), len(r["warnings"])), (1, 0))

    def test_stale_imports_detected(self):
        self.assertTrue(core.is_stale_imports([diag(1, "error", "Imports are out of date and must be rebuilt")]))
        self.assertFalse(core.is_stale_imports([diag(1, "error", "unknown identifier")]))


class LeanImport(unittest.TestCase):
    def test_import_goes_first_or_after_module(self):
        self.assertEqual(core.with_lean_import("import Foo\n\ndef x := 1"), ("import Lean\nimport Foo\n\ndef x := 1", 1))
        self.assertEqual(core.with_lean_import("module\nimport Foo"), ("module\nimport Lean\nimport Foo", 1))

    def test_lean_library_hits_need_an_import_after_the_retry(self):
        hits = [{"name": "Lean.Json.compress", "module": "Lean.Data.Json.Printer"},
                {"name": "List.append_nil", "module": "Init.Data.List.Basic"}]
        self.assertEqual(core.unimported_by_file({"Lean.Json.compress": "ok", "List.append_nil": "ok"}, hits),
                         {"Lean.Json.compress": "import", "List.append_nil": "ok"})

    def test_only_a_missing_namespace_triggers_the_retry(self):
        self.assertTrue(core.needs_lean_import(core.UserError("search failed inside Lean: unknown namespace `Command`")))
        self.assertFalse(core.needs_lean_import(core.UserError("search failed inside Lean: unexpected token")))


class Search(unittest.TestCase):
    def test_words(self):
        self.assertEqual(core.search_words(" Union,  comm "), ["union", "comm"])
        for bad in ["", "   ", 'a"b', "x) #eval"]:
            with self.assertRaises(UserError):
                core.search_words(bad)

    def test_snippet_embeds_words_and_limit(self):
        s = core.search_snippet(["union", "comm"], 7)
        self.assertIn('["union", "comm"]', s)
        self.assertIn("extract 0 7", s)
        self.assertIn(core.SEARCH_MARK, s)

    def test_parse(self):
        d = [diag(40, "info", f"{core.SEARCH_MARK} 12\nA.b : P\nC.d : Q")]
        self.assertEqual(core.parse_search(d, 40), (12, ["A.b : P", "C.d : Q"]))
        self.assertEqual(core.parse_search([diag(40, "info", f"{core.SEARCH_MARK} 0\n")], 40), (0, []))

    def test_parse_surfaces_lean_error_and_absence(self):
        with self.assertRaisesRegex(UserError, "inside Lean: bad"):
            core.parse_search([diag(41, "error", "bad")], 40)
        with self.assertRaisesRegex(UserError, "no result"):
            core.parse_search([diag(3, "error", "earlier")], 40)


BUILD_OUT = """\
⚠ [617/621] Built SyntheticSystems.Systems.System
warning: SyntheticSystems/Systems/System.lean:12:8: declaration uses 'sorry'
✖ [618/621] Building SyntheticSystems.Systems.Hom
error: ./././SyntheticSystems/Systems/Hom.lean:30:42: unknown tactic
error: SyntheticSystems/Systems/Hom.lean:31:4: unsolved goals
a b : ℕ
⊢ a = b
warning: SyntheticSystems/Systems/Hom.lean:2:0: unused variable `x`
error: build failed
"""


class Build(unittest.TestCase):
    def test_parse_failure(self):
        r = core.parse_build(BUILD_OUT, 1)
        self.assertFalse(r["ok"])
        self.assertEqual([(e["file"], e["line"]) for e in r["errors"]],
                         [("SyntheticSystems/Systems/Hom.lean", 30), ("SyntheticSystems/Systems/Hom.lean", 31)])
        self.assertIn("⊢ a = b", r["errors"][1]["message"])        # continuation lines kept
        self.assertEqual([e["line"] for e in r["sorries"]], [12])
        self.assertEqual(len(r["warnings"]), 1)
        self.assertEqual(r["failed"], ["SyntheticSystems.Systems.Hom"])
        self.assertEqual(r["summary"], "error: build failed")

    def test_parse_success(self):
        r = core.parse_build("✔ [620/621] Built X\nBuild completed successfully (621 jobs).\n", 0)
        self.assertTrue(r["ok"])
        self.assertEqual(r["summary"], "Build completed successfully (621 jobs).")
        self.assertIn("Build completed", core.render_build(r, 3))


class Render(unittest.TestCase):
    def test_check_clean_vs_sorry(self):
        self.assertIn("clean", core.render_check("F.lean", [], {}, 1.0))
        out = core.render_check("F.lean", [diag(5, "warning", "declaration uses 'sorry'")], {}, 1.0)
        self.assertNotIn("clean", out)
        self.assertIn("1 declaration(s) using sorry", out)

    def test_check_goals(self):
        out = core.render_check("F.lean", [], {3: ["h : P\n⊢ Q"], 9: None, 4: []}, 1.0)
        self.assertIn("goals before line 3:\nh : P\n⊢ Q", out)
        self.assertIn("goals before line 4:\nno goals", out)
        self.assertIn("goals before line 9:\n(no tactic state here)", out)

    def test_try_shows_own_errors_and_counts_elsewhere(self):
        r = [{"candidate": "simp", "first": 3, "last": 3, "verdict": "error", "goals_after": None,
              "diagnostics": [diag(1, "error", "unsolved goals"), diag(3, "error", "simp made no progress")]},
             {"candidate": "exact h", "first": 3, "last": 3, "verdict": "no goals", "goals_after": [],
              "diagnostics": []}]
        out = core.render_try("F.lean", 3, r, 2.0)
        self.assertIn("[1] ERROR: simp", out)
        self.assertIn("simp made no progress", out)
        self.assertIn("1 error(s) elsewhere", out)
        self.assertIn("[2] NO GOALS: exact h", out)

    def test_search_render(self):
        self.assertIn("no constant", core.render_search(["zz"], 0, []))
        out = core.render_search(["a"], 50, ["x : P"])
        self.assertIn("showing the 1 shortest", out)


if __name__ == "__main__":
    unittest.main()
