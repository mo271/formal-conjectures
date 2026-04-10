/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports
/-!
# Equidistributed Sequences

Corollary 4.2 of Chapter 1 states that the sequence $(x^n), n = 1, 2, ... ,$ is equidistributed modulo 1 for
almost all x > 1. And a little bit further down:
"one does not know whether sequences such as $(e^n)$, $(π^n)$, or even $((\frac 3 2)^n)$"
are equidistributed modulo 1 or not.

*References:*
  - [Uniform Distribution of Sequences](https://store.doverpublications.com/products/9780486149998)
by *L. Kuipers* and *H. Niederreiter*, 1974
  - [Wikipedia](https://en.wikipedia.org/wiki/Equidistributed_sequence)
-/

namespace Equidistribution

open scoped Topology
open Filter Set

/--
A sequence `(s_1, s_2, s_3, ...)` of real numbers is said to be equidistributed on
an interval `[a, b]` if for every subinterval `[c, d]` of `[a, b]` we have
`lim_{n→ ∞} |{s_1, ..., s_n} ∩ [c, d]| / n = (d - c)/(b-a)`
-/
def IsEquidistributed (a b : ℝ) (s : ℕ → ℝ) : Prop :=
  ∀ c d, c ≤ d → Set.Icc c d ⊆ Set.Icc a b →
  Filter.atTop.Tendsto (fun n => ((Finset.range n).filter
    fun m => s m ∈ Set.Icc c d).card / (n : ℝ)) (𝓝 <| (d - c) / (b - a))

/--
A sequence `(s_1, s_2, s_3, ...)` of real numbers is said to be equidistributed
modulo 1 or uniformly distributed modulo 1 if the sequence of the fractional parts of
`a_n`, denoted by `(a_n)` or by `a_n − ⌊a_n⌋`, is equidistributed in the interval `[0, 1]`.
-/
def IsEquidistributedModuloOne (s : ℕ → ℝ) : Prop :=
  IsEquidistributed 0 1 (fun n => Int.fract (s n))

/--
A point `x` is an accumulation point of a sequence `s_0, s_1, ...`
if any neighbourhood of `x` contains a point of the sequence distinct
from `x`.
-/
def IsAccumulationPoint (x : ℝ) (s : ℕ → ℝ) : Prop :=
  x ∈ closure (Set.range s \ {x})

/--
If a point `x` is an accumulation point of a sequence `s_0, s_1, ...` then
there is a subsequence of `s` that tends to `x`
-/
def isAccumulationPoint_iff_exists_subsequence_tendsto
    (x : ℝ) (s : ℕ → ℝ) (hx : IsAccumulationPoint x s) :
    ∃ (u : ℕ → ℕ), StrictMono u ∧ Filter.atTop.Tendsto (s ∘ u) (𝓝 x) := by
  sorry

/--
The sequence `(3/2)^n` is equidistributed modulo `1`.
-/
@[category research open, AMS 11]
theorem isEquidistributedModuloOne_three_halves_pow :
    IsEquidistributedModuloOne (fun n => (3 / 2 : ℝ)^n) := by
  sorry

/--
The sequence `(3/2)^n` has infinitely many accumulation points modulo `1`.
-/
@[category research solved, AMS 11]
theorem isAccumulationPoint_three_halves_pow_infinite :
    {x | IsAccumulationPoint x (fun n => Int.fract <| (3 / 2 : ℝ)^n)}.Infinite := by
  sorry

/--
Find an accumulation point of the sequence `(3/2)^n` modulo `1`.
-/
@[category research open, AMS 11]
theorem isAccumulationPoint_three_halves_pow :
    IsAccumulationPoint answer(sorry) (fun n => Int.fract <| (3 / 2 : ℝ)^n) := by
  sorry

/-- `AccPt x (𝓟 S)` is equivalent to `x ∈ closure (S \ {x})`, connecting Mathlib's
accumulation point filter definition with the set-theoretic one. -/
private lemma accPt_principal_iff {x : ℝ} {S : Set ℝ} :
    AccPt x (𝓟 S) ↔ x ∈ closure (S \ {x}) := by
  simp only [AccPt, mem_closure_iff_nhdsWithin_neBot, nhdsWithin, Set.diff_eq]
  constructor <;> intro h
  · rwa [show 𝓝 x ⊓ 𝓟 {x}ᶜ ⊓ 𝓟 S = 𝓝 x ⊓ 𝓟 (S ∩ {x}ᶜ) from by
      rw [← inf_principal, inf_assoc, inf_comm (𝓟 S), ← inf_assoc]] at h
  · rwa [show 𝓝 x ⊓ 𝓟 {x}ᶜ ⊓ 𝓟 S = 𝓝 x ⊓ 𝓟 (S ∩ {x}ᶜ) from by
      rw [← inf_principal, inf_assoc, inf_comm (𝓟 S), ← inf_assoc]]

/-- The fractional parts of `(3/2)^n` are all distinct. This follows from a 2-adic
valuation argument: `(3/2)^n = 3^n/2^n` has denominator exactly `2^n` (since `3^n` is odd),
so different values of `n` yield different fractional parts. -/
private lemma fract_three_halves_injective :
    Function.Injective (fun n => Int.fract ((3 / 2 : ℝ)^n)) := by
  intro m n hmn
  by_contra h
  wlog hmn' : m < n with H
  · exact H hmn.symm (Ne.symm h) (lt_of_le_of_ne (Nat.le_of_not_lt hmn') (Ne.symm h))
  have hle : m ≤ n := le_of_lt hmn'
  rw [Int.fract_eq_fract] at hmn
  obtain ⟨z, hz⟩ := hmn
  -- Convert to ℤ: 3^m * 2^n - 3^n * 2^m = z * (2^m * 2^n)
  have key : (3 : ℤ)^m * 2^n - 3^n * 2^m = z * (2^m * 2^n) := by
    have : (3 : ℝ)^m * 2^n - (3 : ℝ)^n * 2^m = (z : ℝ) * (2^m * 2^n) := by
      rw [div_pow, div_pow] at hz; field_simp at hz ⊢; linarith
    exact_mod_cast this
  -- Cancel 2^m to get: 3^m * 2^(n-m) - 3^n = z * 2^n
  have cancel : (3 : ℤ)^m * 2^(n - m) - 3^n = z * 2^n := by
    have h2split : (2 : ℤ)^n = 2^m * 2^(n - m) := by rw [← pow_add, Nat.add_sub_cancel' hle]
    have factored : (3 : ℤ)^m * 2^n - 3^n * 2^m = 2^m * ((3 : ℤ)^m * 2^(n - m) - 3^n) := by
      rw [h2split]; ring
    rw [factored] at key
    have : z * (2^m * 2^n) = 2^m * (z * 2^n) := by ring
    rw [this] at key
    exact mul_left_cancel₀ (by positivity : (2 : ℤ)^m ≠ 0) key
  -- Parity contradiction: LHS is odd but RHS is even
  -- 3^m * 2^(n-m) is even since 2 ∣ 2^(n-m) (as n-m ≥ 1)
  have h_term_even : Even ((3 : ℤ)^m * 2^(n - m)) := by
    have h2dvd : (2 : ℤ) ∣ 2^(n - m) := dvd_pow_self 2 (by omega : n - m ≠ 0)
    exact (even_iff_two_dvd.mpr h2dvd).mul_left _
  -- 3^n is odd
  have h_3n_odd : Odd ((3 : ℤ)^n) := Odd.pow (by decide)
  -- LHS = even - odd is odd (by Int.odd_sub)
  have h_lhs_odd : Odd ((3 : ℤ)^m * 2^(n - m) - 3^n) := by
    rw [Int.odd_sub]
    exact iff_of_false
      (fun ho => (Int.not_odd_iff_even.mpr h_term_even) ho)
      (fun he => (Int.not_even_iff_odd.mpr h_3n_odd) he)
  -- RHS = z * 2^n is even since 2 ∣ 2^n (as n ≥ 1)
  have h_rhs_even : Even (z * (2 : ℤ)^n) := by
    have h2dvd : (2 : ℤ) ∣ 2^n := dvd_pow_self 2 (by omega : n ≠ 0)
    exact (even_iff_two_dvd.mpr h2dvd).mul_left _
  -- Contradiction: LHS is odd, RHS is even, but they are equal
  rw [cancel] at h_lhs_odd
  exact absurd h_rhs_even (Int.not_even_iff_odd.mpr h_lhs_odd)

/--
There is an accumulation point of the sequence `(3/2)^n` modulo `1`.
-/
@[category test, AMS 11]
theorem isAccumulationPoint_three_halves_pow_exists :
    ∃ p, (IsAccumulationPoint p (fun n => Int.fract <| (3 / 2 : ℝ)^n)) := by
  set s := fun n => Int.fract ((3 / 2 : ℝ)^n)
  -- The range of s is infinite (since s is injective)
  have hinf : (Set.range s).Infinite :=
    Set.infinite_range_of_injective fract_three_halves_injective
  -- The range is contained in [0, 1]
  have hsub : Set.range s ⊆ Set.Icc 0 1 := by
    rintro _ ⟨n, rfl⟩
    exact ⟨Int.fract_nonneg _, le_of_lt (Int.fract_lt_one _)⟩
  -- An infinite subset of the compact set [0,1] has an accumulation point
  obtain ⟨p, _, hp⟩ := hinf.exists_accPt_of_subset_isCompact isCompact_Icc hsub
  exact ⟨p, accPt_principal_iff.mp hp⟩

end Equidistribution
