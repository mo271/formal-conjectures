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
import FormalConjectures.Wikipedia.Borsuk.Space.Dissect

/-!
# Borsuk's conjecture in dimension three

`borsukConjecture_three`: every bounded subset of `ℝ³` with at least two points can be
divided into four parts of strictly smaller diameter (Eggleston 1955; the proof
formalised here follows the Gale–Grünbaum–Heppes cover method).

The pipeline: rescale to diameter `√3`; move the set into the regular octahedron of
width `√3` (`FormalConjectures/Wikipedia/Borsuk/Space/OctCover.lean`); reflect it into the truncated octahedron
(`FormalConjectures/Wikipedia/Borsuk/Space/Truncate.lean`); intersect with the four-piece dissection whose pieces
have diameter at most `173/100 < √3` (`FormalConjectures/Wikipedia/Borsuk/Space/Dissect.lean`).
-/

namespace Borsuk

open Metric Bornology Set Real
open scoped Pointwise ENNReal

namespace Space

/-- The truncated octahedron admits a four-piece Borsuk cover of anything inside it:
any set `K` inside `TruncOct` of diameter exactly `√3` has a Borsuk cover by four sets. -/
@[category API, AMS 52]
theorem hasBorsukCover_of_subset_truncOct {K : Set E3} (hKT : K ⊆ TruncOct)
    (hdiam : ediam K = ENNReal.ofReal (Real.sqrt 3)) : HasBorsukCover 4 K := by
  have hlt : ENNReal.ofReal (173 / 100) < ediam K := by
    rw [hdiam]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr bound_lt_sqrt3
  have hpiece : ∀ (P : Set E3), (∀ x ∈ P, ∀ y ∈ P, dist x y ≤ 173 / 100) →
      ediam (P ∩ K) < ediam K := by
    intro P hP
    refine lt_of_le_of_lt ?_ hlt
    apply Metric.ediam_le
    intro x hx y hy
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (hP x hx.1 y hy.1)
  refine ⟨![pieceA ∩ K, pieceB0 ∩ K, pieceB1 ∩ K, pieceB2 ∩ K], ?_, ?_⟩
  · intro y hy
    rcases truncOct_subset_union (hKT hy) with ((hA | hB0) | hB1) | hB2
    · exact mem_iUnion.mpr ⟨0, hA, hy⟩
    · exact mem_iUnion.mpr ⟨1, hB0, hy⟩
    · exact mem_iUnion.mpr ⟨2, hB1, hy⟩
    · exact mem_iUnion.mpr ⟨3, hB2, hy⟩
  · intro i
    fin_cases i
    · exact hpiece pieceA (fun x hx y hy => dist_le_pieceA hx hy)
    · exact hpiece pieceB0 (fun x hx y hy => dist_le_pieceB0 hx hy)
    · exact hpiece pieceB1 (fun x hx y hy => dist_le_pieceB1 hx hy)
    · exact hpiece pieceB2 (fun x hx y hy => dist_le_pieceB2 hx hy)

/-- **Borsuk's conjecture in dimension `3`** (Eggleston 1955, here via the
Gale–Grünbaum cover method): every bounded set in `ℝ³` with at least two points can be
divided into four parts of strictly smaller diameter. -/
@[category API, AMS 52]
theorem _root_.Borsuk.borsukConjecture_three : BorsukConjecture 3 := by
  intro s hbs hs
  -- the diameter is positive
  have hDpos : 0 < diam s := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hs
    have h1 : 0 < dist x y := dist_pos.mpr hxy
    have h2 : dist x y ≤ diam s := dist_le_diam_of_mem hbs hx hy
    linarith
  -- rescale to diameter √3
  set r : ℝ := Real.sqrt 3 / diam s with hrdef
  have hr : 0 < r := by positivity
  set s' : Set E3 := r • s with hs'def
  have hbs' : IsBounded s' := by
    obtain ⟨R, hR⟩ := hbs.subset_closedBall (0 : E3)
    apply (isBounded_closedBall (x := (0 : E3)) (r := r * R)).subset
    rintro y ⟨x, hx, rfl⟩
    have h1 := hR hx
    rw [mem_closedBall, dist_zero_right] at h1 ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left h1 hr.le
  have hnt' : s'.Nontrivial := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hs
    exact ⟨r • x, smul_mem_smul_set hx, r • y, smul_mem_smul_set hy,
      fun h => hxy (smul_right_injective E3 hr.ne' h)⟩
  have hdiam' : diam s' = Real.sqrt 3 := by
    rw [hs'def, diam_smul₀, Real.norm_eq_abs, abs_of_pos hr, hrdef]
    field_simp
  -- position inside the truncated octahedron
  obtain ⟨e, he⟩ :=
    exists_truncated_position hbs' hnt'.nonempty (le_of_eq hdiam')
  set K : Set E3 := ⇑e '' s' with hKdef
  have hKT : K ⊆ TruncOct := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hl1, ht0, ht1, ht2⟩ := he x hx
    exact ⟨hl1, ht0, ht1, ht2⟩
  have hediamK : ediam K = ENNReal.ofReal (Real.sqrt 3) := by
    rw [hKdef, e.isometry.ediam_image, ← hdiam', diam,
      ENNReal.ofReal_toReal hbs'.ediam_ne_top]
  -- the four-piece cover, transported back
  have hK := hasBorsukCover_of_subset_truncOct hKT hediamK
  have hs'cov : HasBorsukCover 4 s' := by
    have h2 := hK.image e.symm
    have h3 : ⇑e.symm '' K = s' := by
      rw [hKdef, Set.image_image]
      simp
    rwa [h3] at h2
  have hcov := HasBorsukCover.smul (r := r⁻¹) (by positivity) hs'cov
  have hss : r⁻¹ • s' = s := by
    rw [hs'def, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  rwa [hss] at hcov

end Space

end Borsuk
