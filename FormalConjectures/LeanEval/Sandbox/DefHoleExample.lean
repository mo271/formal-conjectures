import FormalConjectures.Util.ProblemImports

/-!
Minimal example exercising the def-hole / multi-hole eval-problem pipeline.

A `def` and a `theorem` referring to it, both `sorry`. A submission
defines `Submission.foo := 37` and proves `Submission.foo_def`; comparator
should accept it.
-/

@[category research solved, AMS 0]
def foo : Nat := sorry

@[category research solved, AMS 0]
theorem foo_def : foo = 37 := sorry
