"""Regression tests for the historical-assumption inventory."""
import runpy
from pathlib import Path
import unittest

TOOLS = runpy.run_path(str(Path(__file__).with_name("kipbase-migration.py")))


class TrustInventoryTests(unittest.TestCase):
    def test_nested_comments_and_strings_are_not_assumptions(self):
        text = '/- axiom fake : False /- sorry -/ -/\ndef s := "sorry"\n'
        text += 'theorem actual : True := by\n  sorry -- axiom ignored\n'
        declarations, debt = TOOLS["inventory"](text)
        self.assertEqual(declarations, [("def", "s"), ("theorem", "actual")])
        self.assertEqual(debt, [{"kind": "sorry", "declaration": "actual", "line": 4}])

    def test_data_placeholders_and_indented_assumptions_are_recorded(self):
        text = 'noncomputable def data : Nat := sorry\n  axiom claim : True\n'
        _, debt = TOOLS["inventory"](text)
        self.assertEqual([(x["kind"], x["declaration"]) for x in debt],
                         [("sorry", "data"), ("axiom", "claim")])

    def test_private_named_declarations_are_covered(self):
        declarations, _ = TOOLS["inventory"]('private lemma f : True := by trivial\n')
        self.assertEqual(declarations, [("lemma", "f")])


if __name__ == "__main__":
    unittest.main()
