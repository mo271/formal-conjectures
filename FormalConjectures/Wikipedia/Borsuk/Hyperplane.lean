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
# The hyperplane reduction

Jenrich and Brouwer obtain their 64-dimensional counterexample by exhibiting 352 of
Bondarenko's 416 vectors that are orthogonal to a common nonzero vector `u ∈ ℝ⁶⁵`, i.e.
lie in a hyperplane through the origin.  This file proves the geometric step of that
argument: a family of vectors in `ℝ^(n+1)` orthogonal to a nonzero vector can be realised
isometrically in `ℝⁿ` (`exists_isometric_map_of_inner_eq_zero`), via an orthonormal basis
of the orthogonal complement `(ℝ ∙ u)ᗮ`.
-/

namespace Borsuk

open Metric Set Module

open scoped RealInnerProductSpace

/-- A family of vectors of `ℝ^(n+1)` orthogonal to a nonzero vector `u` — that is, lying
in the hyperplane `u ᗮ` — can be realised isometrically in `ℝⁿ`. -/
@[category API, AMS 52]
theorem exists_isometric_map_of_inner_eq_zero {n : ℕ} {ι : Type*}
    (v : ι → EuclideanSpace ℝ (Fin (n + 1))) {u : EuclideanSpace ℝ (Fin (n + 1))}
    (hu : u ≠ 0) (hvu : ∀ i, ⟪u, v i⟫ = 0) :
    ∃ v' : ι → EuclideanSpace ℝ (Fin n),
      ∀ i j, dist (v' i) (v' j) = dist (v i) (v j) := by
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hmem : ∀ i, v i ∈ (ℝ ∙ u)ᗮ := fun i =>
    Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hvu i)
  let b := OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n hu
  refine ⟨fun i => b.repr ⟨v i, hmem i⟩, fun i j => ?_⟩
  rw [b.repr.dist_map]
  exact Subtype.dist_eq _ _

end Borsuk
