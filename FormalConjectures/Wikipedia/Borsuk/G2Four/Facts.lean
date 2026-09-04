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
import FormalConjectures.Wikipedia.Borsuk.G2Four.Defs

/-!
# Verified facts about the `G₂(4)` graph

The combinatorial facts about the explicit `G₂(4)` graph of `FormalConjectures/Wikipedia/Borsuk/G2Four/Defs.lean`,
established by `native_decide` (the compiler is trusted
for these large finite computations):

* it has `416` vertices, is `100`-regular, and any two distinct vertices have `36` or
  `20` common neighbours according to adjacency — i.e. it is an `srg(416, 100, 36, 20)`;
* it contains no `6`-clique (`no_six_clique`);
* it contains at least one edge.
-/

namespace Borsuk

set_option linter.style.nativeDecide false

namespace G2Four

@[category test, AMS 52]
theorem vertexMasks_size : vertexMasks.size = 416 := by native_decide

@[category test, AMS 52]
theorem adj_symm : ∀ i j : Fin 416, adj i j = adj j i := by native_decide

@[category test, AMS 52]
theorem adj_irrefl : ∀ i : Fin 416, adj i i = false := by native_decide

@[category test, AMS 52]
theorem exists_edge : ∃ i j : Fin 416, adj i j := by native_decide

@[category test, AMS 52]
theorem degree_eq :
    ∀ i : Fin 416, ({j | adj i j} : Finset (Fin 416)).card = 100 := by native_decide

@[category test, AMS 52]
theorem lambda_eq : ∀ i j : Fin 416, adj i j →
    ({k | adj i k ∧ adj j k} : Finset (Fin 416)).card = 36 := by native_decide

@[category test, AMS 52]
theorem mu_eq : ∀ i j : Fin 416, i ≠ j → ¬ adj i j →
    ({k | adj i k ∧ adj j k} : Finset (Fin 416)).card = 20 := by native_decide

@[category test, AMS 52]
theorem sixCliqueFreeB_eq_true : sixCliqueFreeB = true := by native_decide

/-- The `G₂(4)` graph contains no `6`-clique of vertices listed in increasing order
(hence, by symmetry, no `6`-clique at all: see `no_six_clique'` below). -/
@[category API, AMS 52]
theorem no_six_clique : ∀ i j w x y z : Fin 416,
    i < j → j < w → w < x → x < y → y < z →
    adj i j → adj i w → adj j w → adj i x → adj j x → adj w x →
    adj i y → adj j y → adj w y → adj x y →
    adj i z → adj j z → adj w z → adj x z → adj y z → False := by
  intro i j w x y z hij hjw hwx hxy hyz a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
  have h := sixCliqueFreeB_eq_true
  rw [sixCliqueFreeB] at h
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
  have h1 := h i j
  rw [if_pos ⟨hij, a1⟩] at h1
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h1
  have h2 := h1 w
  rw [if_pos ⟨hjw, a2, a3⟩] at h2
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h2
  have h3 := h2 x
  rw [if_pos ⟨hwx, a4, a5, a6⟩] at h3
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h3
  have h4 := h3 y
  rw [if_pos ⟨hxy, a7, a8, a9, a10⟩] at h4
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h4
  have h5 := h4 z
  rw [if_pos ⟨hyz, a11, a12, a13, a14, a15⟩] at h5
  exact absurd h5 (by simp)

end G2Four

end Borsuk
