import FormalConjectures.Util.ProblemImports

namespace LeanEval

/-!
The declarations in this module are the human-authored source of truth for benchmark
statements. The generator reads declarations marked with `@[eval_problem]` and emits
independent comparator workspaces from these shared source files, so benchmark authors
do not need to hand-maintain per-problem packages.
-/

theorem two_plus_two_eq_four : (2 : Nat) + 2 = 4 := by
  sorry

theorem list_append_singleton_length :
    (([1, 2] : List Nat).append [3]).length = 3 := by
  sorry
theorem ci_regenerate_main_check : True := by trivial

def starterNumber : Nat := 4

end LeanEval
