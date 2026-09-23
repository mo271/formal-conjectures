#!/usr/bin/env python3
"""Tests for `check_build_warnings.py`.

Run with `python3 -m unittest discover -s scripts -p 'test_*.py'`.
No dependencies beyond the standard library.
"""

import contextlib
import io
import json
import pathlib
import tempfile
import unittest

import check_build_warnings as cbw


def block(target):
    return {"file_info": {"target": target}, "full_output": f"warning in {target}"}


class IsOwnTest(unittest.TestCase):

    def test_own_modules(self):
        for target in ("FormalConjectures.Wikipedia.RiemannZetaValues",
                       "FormalConjectures.ErdosProblems.«361»",
                       "FormalConjecturesForMathlib.Data.Nat.Foo",
                       "FormalConjecturesUtil",
                       "formal_conjectures:extract_names"):
            self.assertTrue(cbw.is_own(block(target)), target)

    def test_dependency_modules(self):
        for target in ("Apery.Table.U01",
                       "PrimeNumberTheoremAnd.Wiener",
                       "Mathlib.Algebra.Quandle",
                       "FormalConjecturesExtra.Foo",
                       "batteries:extraDep"):
            self.assertFalse(cbw.is_own(block(target)), target)

    def test_unknown_origin_counts_as_own(self):
        self.assertTrue(cbw.is_own({}))
        self.assertTrue(cbw.is_own({"file_info": {}}))


class MainTest(unittest.TestCase):

    def run_main(self, summary):
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp) / "summary.json"
            path.write_text(json.dumps(summary), encoding="utf-8")
            with contextlib.redirect_stdout(io.StringIO()):
                return cbw.main([str(path)])

    def test_dependency_warnings_pass(self):
        summary = {"warnings": [block("Apery.Main")], "errors": [],
                   "warning_count": 1, "error_count": 0}
        self.assertEqual(self.run_main(summary), 0)

    def test_own_warning_fails(self):
        summary = {"warnings": [block("Apery.Main"),
                                block("FormalConjectures.Foo")],
                   "errors": [], "warning_count": 2, "error_count": 0}
        self.assertEqual(self.run_main(summary), 1)

    def test_own_error_fails(self):
        summary = {"warnings": [], "errors": [block("FormalConjectures.Foo")],
                   "warning_count": 0, "error_count": 1}
        self.assertEqual(self.run_main(summary), 1)

    def test_unreadable_summary(self):
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(cbw.main(["/nonexistent/summary.json"]), 2)


if __name__ == "__main__":
    unittest.main()
