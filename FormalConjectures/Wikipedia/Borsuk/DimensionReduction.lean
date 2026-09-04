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

/-!
# Dimension reduction for finite point configurations

A family of vectors in a real inner product space whose span has dimension `d` can be
realised in `EuclideanSpace ℝ (Fin d)` with the same inner products (hence the same
distances): map everything through the coordinates of an orthonormal basis of the span.

This is the tool that turns Bondarenko's 416 vectors — constructed as rows of a
`416 × 416` matrix of rank `65` — into an honest point configuration in `ℝ⁶⁵`.
-/

namespace Borsuk

open Module Set Submodule

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A family of vectors lying in a subspace of dimension `d` can be realised in
`EuclideanSpace ℝ (Fin d)` with the same inner products: map everything through the
coordinates of an orthonormal basis of the subspace. -/
@[category API, AMS 52]
theorem exists_inner_preserving_of_mem {W : Submodule ℝ E} [FiniteDimensional ℝ W]
    {d : ℕ} {ι : Type*} (v : ι → E) (hv : ∀ i, v i ∈ W) (h : finrank ℝ W = d) :
    ∃ w : ι → EuclideanSpace ℝ (Fin d), ∀ i j, ⟪w i, w j⟫ = ⟪v i, v j⟫ := by
  let b : OrthonormalBasis (Fin d) ℝ W := (stdOrthonormalBasis ℝ W).reindex (finCongr h)
  refine ⟨fun i => b.repr ⟨v i, hv i⟩, fun i j => ?_⟩
  rw [b.repr.inner_map_map]
  rfl

/-- A family of vectors whose span has dimension exactly `d` can be realised in
`EuclideanSpace ℝ (Fin d)` with the same inner products. -/
@[category API, AMS 52]
theorem exists_inner_preserving_of_finrank_span_eq [FiniteDimensional ℝ E] {d : ℕ}
    {ι : Type*} (v : ι → E) (h : finrank ℝ (span ℝ (range v)) = d) :
    ∃ w : ι → EuclideanSpace ℝ (Fin d), ∀ i j, ⟪w i, w j⟫ = ⟪v i, v j⟫ :=
  exists_inner_preserving_of_mem v (fun i => subset_span (mem_range_self i)) h

/-- Two families of vectors with identical pairwise inner products have identical
pairwise distances. -/
@[category API, AMS 52]
theorem dist_eq_of_inner_eq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {ι : Type*} {v : ι → E} {w : ι → F} (h : ∀ i j, ⟪w i, w j⟫ = ⟪v i, v j⟫) (i j : ι) :
    dist (w i) (w j) = dist (v i) (v j) := by
  rw [dist_eq_norm, dist_eq_norm, ← Real.sqrt_sq (norm_nonneg (w i - w j)),
    ← Real.sqrt_sq (norm_nonneg (v i - v j))]
  congr 1
  rw [norm_sub_sq_real, norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, h i i, h i j, h j j]

/-- A family of vectors lying in a subspace of dimension `d` can be realised in
`EuclideanSpace ℝ (Fin d)` with the same distances. -/
@[category API, AMS 52]
theorem exists_dist_preserving_of_mem {W : Submodule ℝ E} [FiniteDimensional ℝ W]
    {d : ℕ} {ι : Type*} (v : ι → E) (hv : ∀ i, v i ∈ W) (h : finrank ℝ W = d) :
    ∃ w : ι → EuclideanSpace ℝ (Fin d), ∀ i j, dist (w i) (w j) = dist (v i) (v j) := by
  obtain ⟨w, hw⟩ := exists_inner_preserving_of_mem v hv h
  exact ⟨w, dist_eq_of_inner_eq hw⟩

/-- A family of vectors whose span has dimension exactly `d` can be realised in
`EuclideanSpace ℝ (Fin d)` with the same distances. -/
@[category API, AMS 52]
theorem exists_dist_preserving_of_finrank_span_eq [FiniteDimensional ℝ E] {d : ℕ}
    {ι : Type*} (v : ι → E) (h : finrank ℝ (span ℝ (range v)) = d) :
    ∃ w : ι → EuclideanSpace ℝ (Fin d), ∀ i j, dist (w i) (w j) = dist (v i) (v j) := by
  obtain ⟨w, hw⟩ := exists_inner_preserving_of_finrank_span_eq v h
  exact ⟨w, dist_eq_of_inner_eq hw⟩

end Borsuk
