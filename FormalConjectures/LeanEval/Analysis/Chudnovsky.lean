import FormalConjectures.Util.ProblemImports

namespace LeanEval
namespace Analysis

open scoped Real

/-!
Chudnovsky's formula for `π⁻¹`.

Mathlib already defines the Chudnovsky series `chudnovskySum`; this benchmark asks for the missing
identity with `π⁻¹`.
-/

@[category research solved, AMS 0]
theorem chudnovsky_formula_for_pi_inv :
    chudnovskySum = π⁻¹ := by
  sorry

end Analysis
end LeanEval
