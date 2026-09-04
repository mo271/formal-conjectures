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
import FormalConjectures.Wikipedia.Borsuk.G2Four.Representation

/-!
# The Jenrich–Brouwer partition and the 64-dimensional configuration

The 96 vertices of the `G₂(4)` graph whose isotropic set contains the isotropic point `0`
split into three mutually non-adjacent 32-sets `B₁, B₂, B₃` (the connected components of
the induced subgraph).  With `u = ∑_{y ∈ B₂} v̄_y - ∑_{y ∈ B₃} v̄_y` one has
`⟪u, u⟫ = 36864 ≠ 0`, while `⟪u, v̄ₓ⟫ = 0` for each of the `352` vertices
`x ∉ B₂ ∪ B₃` — so those 352 configuration vectors lie in the hyperplane `uᗮ`.  This is
Jenrich–Brouwer's counterexample configuration; the verified balance facts below are
exactly the equitable-partition counts from their paper.

The main result `exists_jenrichBrouwer` is the statement
`exists_jenrichBrouwer_vectors_in_hyperplane` of `FormalConjectures/Wikipedia/Borsuk/Counterexamples.lean`.
-/

namespace Borsuk

namespace G2Four

open Module Set Finset

open scoped RealInnerProductSpace

set_option linter.style.nativeDecide false

/-- The first 32-component of the Jenrich–Brouwer partition. -/
def B1 : Finset (Fin 416) :=
  {0, 1, 6, 7, 16, 17, 22, 23, 28, 29, 34, 35, 40, 41, 46, 47, 48, 49, 58, 59, 60, 61,
   70, 71, 72, 73, 82, 83, 88, 89, 90, 91}

/-- The second 32-component of the Jenrich–Brouwer partition. -/
def B2 : Finset (Fin 416) :=
  {2, 3, 10, 11, 14, 15, 20, 21, 24, 25, 30, 31, 36, 37, 44, 45, 52, 53, 54, 55, 64, 65,
   68, 69, 76, 77, 80, 81, 84, 85, 94, 95}

/-- The third 32-component of the Jenrich–Brouwer partition. -/
def B3 : Finset (Fin 416) :=
  {4, 5, 8, 9, 12, 13, 18, 19, 26, 27, 32, 33, 38, 39, 42, 43, 50, 51, 56, 57, 62, 63,
   66, 67, 74, 75, 78, 79, 86, 87, 92, 93}

/-- The 352-element index set of the Jenrich–Brouwer configuration: all vertices outside
`B₂ ∪ B₃`. -/
def jbIndex : Finset (Fin 416) := Finset.univ \ (B2 ∪ B3)

@[category test, AMS 52]
theorem jbIndex_card : jbIndex.card = 352 := by native_decide

/-- The balance fact making `u ⟂ v̄ₓ` for `x ∉ B₂ ∪ B₃`: such an `x` has equal
`Nint`-sums over `B₂` and `B₃` (each vertex of `B₁` has no neighbour in `B₂` or `B₃`,
and each vertex of `C` has exactly `8` in either). -/
@[category test, AMS 52]
theorem sum_Nint_B2_eq_B3 : ∀ x : Fin 416, x ∉ B2 → x ∉ B3 →
    (∑ y ∈ B2, Nint y x) = ∑ y ∈ B3, Nint y x := by native_decide

@[category test, AMS 52]
theorem sum_Nint_B2_B2 : (∑ y ∈ B2, ∑ z ∈ B2, Nint y z) = 2048 := by native_decide

@[category test, AMS 52]
theorem sum_Nint_B2_B3 : (∑ y ∈ B2, ∑ z ∈ B3, Nint y z) = -1024 := by native_decide

@[category test, AMS 52]
theorem sum_Nint_B3_B2 : (∑ y ∈ B3, ∑ z ∈ B2, Nint y z) = -1024 := by native_decide

@[category test, AMS 52]
theorem sum_Nint_B3_B3 : (∑ y ∈ B3, ∑ z ∈ B3, Nint y z) = 2048 := by native_decide

/-- There is an edge inside the Jenrich–Brouwer index set. -/
@[category test, AMS 52]
theorem exists_edge_jb : ∃ i ∈ jbIndex, ∃ j ∈ jbIndex, adj i j = true := by native_decide

/-- **The Jenrich–Brouwer configuration exists**: 352 of Bondarenko's vectors, orthogonal
to a common nonzero vector `u`, with the two-distance and clique properties. -/
@[category API, AMS 52]
theorem exists_jenrichBrouwer :
    ∃ (v : Fin 352 → EuclideanSpace ℝ (Fin 65)) (u : EuclideanSpace ℝ (Fin 65)),
      u ≠ 0 ∧ (∀ k, ⟪u, v k⟫ = 0) ∧
      Function.Injective v ∧
      (∀ i j, i ≠ j → dist (v i) (v j) = 12 ∨ dist (v i) (v j) = Real.sqrt 192) ∧
      (∃ i j, i ≠ j ∧ dist (v i) (v j) = 12) ∧
      ∀ s : Finset (Fin 352),
        (∀ i ∈ s, ∀ j ∈ s, i ≠ j → dist (v i) (v j) = 12) → s.card ≤ 5 := by
  obtain ⟨w, hw⟩ := exists_inner_preserving_of_mem vRow vRow_mem_Wspan finrank_Wspan
  have hdist : ∀ i j, dist (w i) (w j) = dist (vRow i) (vRow j) := dist_eq_of_inner_eq hw
  have hinner : ∀ i j, ⟪w i, w j⟫ = 6 * (Nint i j : ℝ) := fun i j => by
    rw [hw, inner_vRow]
  -- inner products of sums against the Gram data
  have hsum : ∀ A B : Finset (Fin 416),
      ⟪∑ y ∈ A, w y, ∑ z ∈ B, w z⟫ = 6 * ((∑ y ∈ A, ∑ z ∈ B, Nint y z : ℤ) : ℝ) := by
    intro A B
    rw [sum_inner]
    have h1 : ∀ y ∈ A, ⟪w y, ∑ z ∈ B, w z⟫ = ∑ z ∈ B, 6 * (Nint y z : ℝ) := fun y _ => by
      rw [inner_sum]
      exact Finset.sum_congr rfl fun z _ => hinner y z
    rw [Finset.sum_congr rfl h1]
    push_cast [Finset.mul_sum]
    rfl
  set u : EuclideanSpace ℝ (Fin 65) := (∑ y ∈ B2, w y) - ∑ y ∈ B3, w y with hu
  -- u is nonzero
  have huu : ⟪u, u⟫ = 36864 := by
    rw [hu, inner_sub_left, inner_sub_right, inner_sub_right, hsum B2 B2, hsum B2 B3,
      hsum B3 B2, hsum B3 B3, sum_Nint_B2_B2, sum_Nint_B2_B3, sum_Nint_B3_B2,
      sum_Nint_B3_B3]
    norm_num
  have hune : u ≠ 0 := by
    intro h
    rw [h, inner_zero_left] at huu
    norm_num at huu
  -- u is orthogonal to the configuration vectors outside B₂ ∪ B₃
  have hux : ∀ x : Fin 416, x ∈ jbIndex → ⟪u, w x⟫ = 0 := by
    intro x hx
    rw [jbIndex, Finset.mem_sdiff, Finset.mem_union] at hx
    push Not at hx
    rw [hu, inner_sub_left, sum_inner, sum_inner]
    rw [Finset.sum_congr rfl fun y (_ : y ∈ B2) => hinner y x,
      Finset.sum_congr rfl fun y (_ : y ∈ B3) => hinner y x,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Int.cast_sum, ← Int.cast_sum,
      sum_Nint_B2_eq_B3 x hx.2.1 hx.2.2]
    ring
  -- w is injective
  have hwinj : ∀ i j : Fin 416, i ≠ j → w i ≠ w j := by
    intro i j hij heq
    have hd : dist (w i) (w j) = 0 := by rw [heq, dist_self]
    rw [hdist] at hd
    by_cases h : adj i j = true
    · rw [dist_vRow_of_adj h] at hd; norm_num at hd
    · rw [dist_vRow_of_not_adj hij h] at hd
      have hpos := Real.sqrt_pos.mpr (show (0 : ℝ) < 192 by norm_num)
      rw [hd] at hpos
      exact lt_irrefl 0 hpos
  -- the enumeration of the 352 indices
  let e := jbIndex.orderIsoOfFin jbIndex_card
  have hene : ∀ k k' : Fin 352, k ≠ k' → ((e k : Fin 416) ≠ (e k' : Fin 416)) :=
    fun k k' hk h => hk (e.injective (Subtype.coe_injective h))
  refine ⟨fun k => w (e k), u, hune, fun k => hux _ (e k).2, ?_, ?_, ?_, ?_⟩
  · intro k k' h
    by_contra hk
    exact hwinj _ _ (hene k k' hk) h
  · intro i j hij
    rw [hdist]
    by_cases h : adj (e i : Fin 416) (e j : Fin 416) = true
    · exact Or.inl (dist_vRow_of_adj h)
    · exact Or.inr (dist_vRow_of_not_adj (hene i j hij) h)
  · obtain ⟨i, hi, j, hj, hadj⟩ := exists_edge_jb
    refine ⟨e.symm ⟨i, hi⟩, e.symm ⟨j, hj⟩, ?_, ?_⟩
    · intro h
      have h2 := congrArg e h
      rw [OrderIso.apply_symm_apply, OrderIso.apply_symm_apply] at h2
      exact adj_ne hadj (congrArg Subtype.val h2)
    · rw [hdist]
      have h1 : (e (e.symm ⟨i, hi⟩) : Fin 416) = i := by
        rw [OrderIso.apply_symm_apply]
      have h2 : (e (e.symm ⟨j, hj⟩) : Fin 416) = j := by
        rw [OrderIso.apply_symm_apply]
      rw [h1, h2]
      exact dist_vRow_of_adj hadj
  · intro s hs
    have himg : (s.image fun k => (e k : Fin 416)).card = s.card :=
      Finset.card_image_of_injective s fun k k' h => by
        by_contra hk
        exact hene k k' hk h
    rw [← himg]
    refine clique_card_le_five _ ?_
    intro i hi j hj hij
    obtain ⟨ki, hki, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨kj, hkj, rfl⟩ := Finset.mem_image.mp hj
    have hkij : ki ≠ kj := fun h => hij (by rw [h])
    have hd := hs ki hki kj hkj hkij
    rw [hdist] at hd
    by_contra h
    rw [dist_vRow_of_not_adj hij h] at hd
    exact sqrt192_ne_twelve hd

end G2Four

end Borsuk
