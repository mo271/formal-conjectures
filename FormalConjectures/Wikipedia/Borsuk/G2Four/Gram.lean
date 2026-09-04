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
import FormalConjectures.Wikipedia.Borsuk.G2Four.Facts

/-!
# The Gram identity and the clique bound for the `G₂(4)` graph

Two consequences of the verified facts about the `G₂(4)` graph:

* `Nint_mul_self`: the integer matrix `N = 4·A + 16·I - J` (entries `15` on the
  diagonal, `3` for adjacent, `-1` for non-adjacent pairs) satisfies `N² = 96·N`
  — this single identity encodes the strong regularity `srg(416, 100, 36, 20)` and is
  the source of all inner-product computations for Bondarenko's configuration, whose
  Gram matrix is `6·N`;
* `clique_card_le_five`: every clique of the graph has at most `5` vertices, obtained
  from the ordered statement `no_six_clique` by sorting.
-/

namespace Borsuk

namespace G2Four

set_option linter.style.nativeDecide false

/-- The integer matrix `N = 4·A + 16·I - J`, four times Bondarenko's matrix
`M = A + 4·I - J/4`.  The Gram matrix of the 416 configuration vectors is `6·N`. -/
def Nint (i j : Fin 416) : ℤ :=
  if i = j then 15 else if adj i j then 3 else -1

@[category API, AMS 52]
theorem Nint_symm (i j : Fin 416) : Nint i j = Nint j i := by
  unfold Nint
  rcases eq_or_ne i j with rfl | hij
  · rfl
  · rw [if_neg hij, if_neg hij.symm, adj_symm i j]

/-- The strong regularity of the `G₂(4)` graph, in matrix form: `N² = 96·N`. -/
@[category test, AMS 52]
theorem Nint_mul_self :
    ∀ i j : Fin 416, (∑ k : Fin 416, Nint i k * Nint k j) = 96 * Nint i j := by
  native_decide

/-- Every clique of the `G₂(4)` graph has at most five vertices. -/
@[category API, AMS 52]
theorem clique_card_le_five (s : Finset (Fin 416))
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → adj i j) : s.card ≤ 5 := by
  by_contra hcard
  obtain ⟨t, hts, htcard⟩ := s.exists_subset_card_eq (show 6 ≤ s.card by omega)
  let g := t.orderIsoOfFin htcard
  have hmono : ∀ {i j : Fin 6}, i < j → (g i : Fin 416) < g j :=
    fun hij => g.strictMono hij
  have hmem : ∀ i : Fin 6, (g i : Fin 416) ∈ s := fun i => hts (g i).2
  have hadj : ∀ {i j : Fin 6}, i < j → adj (g i) (g j) :=
    fun {i j} hij => h _ (hmem i) _ (hmem j) (ne_of_lt (hmono hij))
  exact no_six_clique (g 0) (g 1) (g 2) (g 3) (g 4) (g 5)
    (hmono (by decide)) (hmono (by decide)) (hmono (by decide)) (hmono (by decide))
    (hmono (by decide))
    (hadj (by decide)) (hadj (by decide)) (hadj (by decide)) (hadj (by decide))
    (hadj (by decide)) (hadj (by decide)) (hadj (by decide)) (hadj (by decide))
    (hadj (by decide)) (hadj (by decide)) (hadj (by decide)) (hadj (by decide))
    (hadj (by decide)) (hadj (by decide)) (hadj (by decide))

end G2Four

end Borsuk
