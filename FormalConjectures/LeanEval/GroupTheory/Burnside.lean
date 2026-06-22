import FormalConjectures.Util.ProblemImports

namespace LeanEval
namespace GroupTheory

/-!
Burnside's `p^a q^b` theorem.

Mathlib already contains solvability infrastructure, so the statement is naturally phrased as
`IsSolvable G` for a finite group of order `p ^ a * q ^ b`.
-/

@[category research solved, AMS 0]
theorem finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    {G : Type*} [Group G] [Fintype G]
    {p q a b : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hpq : p ≠ q)
    (hcard : Fintype.card G = p ^ a * q ^ b) :
    IsSolvable G := by
  sorry

end GroupTheory
end LeanEval
