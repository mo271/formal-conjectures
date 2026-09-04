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
import FormalConjectures.Wikipedia.Borsuk.G2Four.Gram
import FormalConjectures.Wikipedia.Borsuk.DimensionReduction

/-!
# The Euclidean representation of the `G₂(4)` graph

Bondarenko's point configuration, constructed: the rows of the matrix
`M = N/4 = A + 4·I - J/4` are 416 vectors of `ℝ⁴¹⁶` whose Gram matrix is
`M·Mᵀ = M² = 24·M = 6·N` (by `Nint_mul_self`), so

* `⟪v̄ₓ, v̄ₓ⟫ = 90`, `⟪v̄ₓ, v̄ᵧ⟫ = 18` for adjacent and `-6` for non-adjacent pairs, hence
  `‖v̄ₓ - v̄ᵧ‖² = 144` (adjacent) or `192` (non-adjacent);
* the vectors lie in the range of the projection `P = M/24` (`P² = P`), which has
  dimension `trace P = 65`;
* by `exists_dist_preserving_of_mem` the configuration therefore lives isometrically in
  `EuclideanSpace ℝ (Fin 65)`, and every subset of 12-distance pairs is a clique of the
  graph, so has at most 5 points (`clique_card_le_five`).

The final result `exists_bondarenko` is exactly the statement
`exists_bondarenko_vectors` of `FormalConjectures/Wikipedia/Borsuk/Counterexamples.lean`.
-/

namespace Borsuk

namespace G2Four

open Matrix Module Submodule Set

open scoped RealInnerProductSpace

/-- If two vertices are adjacent they are distinct. -/
@[category API, AMS 52]
theorem adj_ne {x y : Fin 416} (h : adj x y = true) : x ≠ y := by
  rintro rfl
  rw [adj_irrefl] at h
  exact Bool.false_ne_true h

@[category API, AMS 52]
theorem Nint_diag (x : Fin 416) : Nint x x = 15 := if_pos rfl

@[category API, AMS 52]
theorem Nint_of_adj {x y : Fin 416} (h : adj x y = true) : Nint x y = 3 := by
  rw [Nint, if_neg (adj_ne h), if_pos h]

@[category API, AMS 52]
theorem Nint_of_not_adj {x y : Fin 416} (hxy : x ≠ y) (h : ¬ adj x y = true) :
    Nint x y = -1 := by
  rw [Nint, if_neg hxy, if_neg h]

/-- Bondarenko's matrix `M = A + 4·I - J/4 = N/4`, over `ℝ`. -/
noncomputable def Mreal : Matrix (Fin 416) (Fin 416) ℝ :=
  Matrix.of fun i j => (Nint i j : ℝ) / 4

@[category API, AMS 52]
theorem Mreal_apply (i j : Fin 416) : Mreal i j = (Nint i j : ℝ) / 4 := rfl

@[category API, AMS 52]
theorem Mreal_symm (i j : Fin 416) : Mreal i j = Mreal j i := by
  rw [Mreal_apply, Mreal_apply, Nint_symm]

/-- The matrix identity `M² = 6·N` (entrywise), i.e. `M² = 24·M`. -/
@[category API, AMS 52]
theorem Mreal_mul_self_apply (i j : Fin 416) :
    (Mreal * Mreal) i j = 6 * (Nint i j : ℝ) := by
  rw [Matrix.mul_apply]
  have h : ∀ k : Fin 416, Mreal i k * Mreal k j = ((Nint i k * Nint k j : ℤ) : ℝ) / 16 :=
    fun k => by rw [Mreal_apply, Mreal_apply]; push_cast; ring
  rw [Finset.sum_congr rfl fun k _ => h k, ← Finset.sum_div, ← Int.cast_sum,
    Nint_mul_self i j]
  push_cast
  ring

/-- The 416 configuration vectors: the rows of `M`, as elements of `ℝ⁴¹⁶`. -/
noncomputable def vRow (x : Fin 416) : EuclideanSpace ℝ (Fin 416) :=
  WithLp.toLp 2 (Mreal x)

/-- The Gram matrix of the configuration is `6·N`: inner products are `90`, `18`, `-6`. -/
@[category API, AMS 52]
theorem inner_vRow (x y : Fin 416) : ⟪vRow x, vRow y⟫ = 6 * (Nint x y : ℝ) := by
  have h1 : ⟪vRow x, vRow y⟫ = ∑ k : Fin 416, Mreal x k * Mreal y k := by
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun k _ => by simp [vRow, RCLike.inner_apply, mul_comm]
  rw [h1, ← Mreal_mul_self_apply x y, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [Mreal_symm y k]

/-- Squared distances: `‖v̄ₓ - v̄ᵧ‖² = 180 - 12·N x y`. -/
@[category API, AMS 52]
theorem inner_sub_vRow (x y : Fin 416) :
    ⟪vRow x - vRow y, vRow x - vRow y⟫ = 180 - 12 * (Nint x y : ℝ) := by
  rw [real_inner_sub_sub_self, inner_vRow, inner_vRow, inner_vRow, Nint_diag,
    Nint_diag]
  push_cast
  ring

@[category API, AMS 52]
theorem dist_vRow_of_adj {x y : Fin 416} (h : adj x y = true) :
    dist (vRow x) (vRow y) = 12 := by
  rw [dist_eq_norm, norm_eq_sqrt_real_inner, inner_sub_vRow, Nint_of_adj h]
  rw [show (180 : ℝ) - 12 * ((3 : ℤ) : ℝ) = 12 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

@[category API, AMS 52]
theorem dist_vRow_of_not_adj {x y : Fin 416} (hxy : x ≠ y) (h : ¬ adj x y = true) :
    dist (vRow x) (vRow y) = Real.sqrt 192 := by
  rw [dist_eq_norm, norm_eq_sqrt_real_inner, inner_sub_vRow, Nint_of_not_adj hxy h]
  norm_num

/-- The projection matrix `P = M/24`. -/
noncomputable def Preal : Matrix (Fin 416) (Fin 416) ℝ := (24 : ℝ)⁻¹ • Mreal

@[category API, AMS 52]
theorem Preal_mul_self : Preal * Preal = Preal := by
  ext i j
  rw [Preal, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, Matrix.smul_apply,
    Matrix.smul_apply, Mreal_mul_self_apply, Mreal_apply]
  ring

@[category API, AMS 52]
theorem isIdempotent_toLin'_Preal : IsIdempotentElem (Matrix.toLin' Preal) := by
  change Matrix.toLin' Preal * Matrix.toLin' Preal = Matrix.toLin' Preal
  rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, Preal_mul_self]

@[category API, AMS 52]
theorem trace_Preal : Preal.trace = 65 := by
  have h : ∀ i : Fin 416, Preal i i = 5 / 32 := fun i => by
    rw [Preal, Matrix.smul_apply, Mreal_apply, Nint_diag]
    norm_num
  rw [Matrix.trace]
  rw [Finset.sum_congr rfl fun i _ => (by rw [Matrix.diag_apply, h i] :
    Matrix.diag Preal i = 5 / 32)]
  simp
  norm_num

@[category API, AMS 52]
theorem finrank_range_Preal :
    finrank ℝ (LinearMap.range (Matrix.toLin' Preal)) = 65 := by
  have htr := (LinearMap.isProj_range_iff_isIdempotentElem _).mpr
    isIdempotent_toLin'_Preal |>.trace
  rw [Matrix.trace_toLin'_eq, trace_Preal] at htr
  exact_mod_cast htr.symm

/-- Each configuration vector lies in the range of the projection `P`. -/
@[category API, AMS 52]
theorem ofLp_vRow_mem_range (x : Fin 416) :
    WithLp.ofLp (vRow x) ∈ LinearMap.range (Matrix.toLin' Preal) := by
  refine ⟨Pi.single x 24, ?_⟩
  rw [Matrix.toLin'_apply]
  funext k
  have h : Preal.mulVec (Pi.single x 24) k = Preal k x * 24 := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [h]
  change Preal k x * 24 = Mreal x k
  rw [Preal, Matrix.smul_apply, Mreal_symm x k]
  ring

/-- The 65-dimensional subspace of `ℝ⁴¹⁶` containing the configuration. -/
noncomputable def Wspan : Submodule ℝ (EuclideanSpace ℝ (Fin 416)) :=
  (LinearMap.range (Matrix.toLin' Preal)).map
    ((WithLp.linearEquiv 2 ℝ (Fin 416 → ℝ)).symm :
      (Fin 416 → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 416))

@[category API, AMS 52]
theorem finrank_Wspan : finrank ℝ Wspan = 65 := by
  rw [Wspan, LinearEquiv.finrank_map_eq, finrank_range_Preal]

@[category API, AMS 52]
theorem vRow_mem_Wspan (x : Fin 416) : vRow x ∈ Wspan := by
  rw [Wspan, Submodule.mem_map_equiv]
  exact ofLp_vRow_mem_range x

@[category API, AMS 52]
theorem sqrt192_ne_twelve : Real.sqrt 192 ≠ 12 := by
  have h : (12 : ℝ) = Real.sqrt 144 := by
    rw [show (144 : ℝ) = 12 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h]
  exact ne_of_gt (Real.sqrt_lt_sqrt (by norm_num) (by norm_num))

/-- **Bondarenko's configuration exists**: 416 vectors in `ℝ⁶⁵` with distances `12`
(adjacent) and `√192` (non-adjacent), in which every `12`-clique has at most five
elements. -/
@[category API, AMS 52]
theorem exists_bondarenko :
    ∃ v : Fin 416 → EuclideanSpace ℝ (Fin 65),
      Function.Injective v ∧
      (∀ i j, i ≠ j → dist (v i) (v j) = 12 ∨ dist (v i) (v j) = Real.sqrt 192) ∧
      (∃ i j, i ≠ j ∧ dist (v i) (v j) = 12) ∧
      ∀ s : Finset (Fin 416),
        (∀ i ∈ s, ∀ j ∈ s, i ≠ j → dist (v i) (v j) = 12) → s.card ≤ 5 := by
  obtain ⟨w, hw⟩ := exists_dist_preserving_of_mem vRow vRow_mem_Wspan finrank_Wspan
  have hdichot : ∀ i j : Fin 416, i ≠ j →
      dist (w i) (w j) = 12 ∨ dist (w i) (w j) = Real.sqrt 192 := by
    intro i j hij
    rw [hw]
    by_cases h : adj i j = true
    · exact Or.inl (dist_vRow_of_adj h)
    · exact Or.inr (dist_vRow_of_not_adj hij h)
  have hadj_of_dist : ∀ i j : Fin 416, i ≠ j → dist (w i) (w j) = 12 → adj i j = true := by
    intro i j hij hd
    by_contra h
    rw [hw, dist_vRow_of_not_adj hij h] at hd
    exact sqrt192_ne_twelve hd
  refine ⟨w, ?_, hdichot, ?_, ?_⟩
  · intro i j hvij
    by_contra hij
    have hd : dist (w i) (w j) = 0 := by rw [hvij, dist_self]
    rcases hdichot i j hij with h | h
    · rw [hd] at h; norm_num at h
    · rw [hd] at h
      have hpos := Real.sqrt_pos.mpr (show (0 : ℝ) < 192 by norm_num)
      rw [← h] at hpos
      exact lt_irrefl 0 hpos
  · obtain ⟨i, j, hij⟩ := exists_edge
    exact ⟨i, j, adj_ne hij, by rw [hw]; exact dist_vRow_of_adj hij⟩
  · intro s hs
    exact clique_card_le_five s fun i hi j hj hij => hadj_of_dist i j hij (hs i hi j hj hij)

end G2Four

end Borsuk
