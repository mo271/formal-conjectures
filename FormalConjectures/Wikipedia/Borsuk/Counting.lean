/-
Copyright 2026 The Formal Conjectures Authors.

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

import FormalConjecturesUtil
import FormalConjectures.Wikipedia.Borsuk.Definitions

/-!
# The counting argument

All known counterexamples to Borsuk's conjecture are finite point sets in which every
subset of smaller diameter is small.  This file proves the elementary counting argument
that turns such a set into a counterexample:

* `HasBorsukCover.ncard_le_mul`: if every subset of `s` of smaller diameter has at most `m`
  points, then a Borsuk cover of `s` by `k` sets forces `s.ncard ≤ k * m`;
* `not_borsukConjecture_of_bad_set`: consequently, a finite set of `N` points with this
  property and `(n + 1) * m < N` refutes Borsuk's conjecture in dimension `n`.

For Bondarenko's counterexample, `n = 65`, `N = 416`, `m = 5` and `66 * 5 = 330 < 416`;
for the Jenrich–Brouwer counterexample, `n = 64`, `N = 352`, `m = 5` and
`65 * 5 = 325 < 352`.  See `FormalConjectures/Wikipedia/Borsuk/Counterexamples.lean`.
-/

namespace Borsuk

open Metric Bornology Set

variable {E : Type*} [PseudoEMetricSpace E]

/-- The counting argument: if every subset of `s` of smaller diameter has at most `m`
points, then a Borsuk cover of `s` by `k` sets forces `s` to have at most `k * m` points. -/
@[category API, AMS 52]
theorem HasBorsukCover.ncard_le_mul {s : Set E} {k m : ℕ}
    (hm : ∀ t ⊆ s, ediam t < ediam s → t.ncard ≤ m) (h : HasBorsukCover k s) :
    s.ncard ≤ k * m := by
  obtain ⟨c, hsub, hcov, hdiam⟩ := h.exists_subsets
  calc s.ncard = (⋃ i, c i).ncard := by rw [← hcov]
    _ ≤ ∑ _i : Fin k, m :=
      le_trans (ncard_iUnion_le_of_fintype c)
        (Finset.sum_le_sum fun i _ => hm _ (hsub i) (hdiam i))
    _ = k * m := by simp

/-- A finite set of `N > 1` points in `n`-dimensional Euclidean space in which every subset
of smaller diameter has at most `m` points refutes Borsuk's conjecture in dimension `n`,
provided `(n + 1) * m < N`. -/
@[category API, AMS 52]
theorem not_borsukConjecture_of_bad_set {n N m : ℕ} (T : Set (EuclideanSpace ℝ (Fin n)))
    (hfin : T.Finite) (hcard : T.ncard = N) (h1 : 1 < N)
    (hm : ∀ t ⊆ T, ediam t < ediam T → t.ncard ≤ m) (hN : (n + 1) * m < N) :
    ¬ BorsukConjecture n := by
  intro hB
  have hnt : T.Nontrivial := by
    obtain ⟨x, hx, y, hy, hxy⟩ := (Set.one_lt_ncard hfin).mp (hcard ▸ h1)
    exact ⟨x, hx, y, hy, hxy⟩
  have hcover := hB T hfin.isBounded hnt
  have hle := hcover.ncard_le_mul hm
  omega

end Borsuk
