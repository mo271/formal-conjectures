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
import FormalConjectures.Wikipedia.Borsuk.Space.OctCover

/-!
# Truncating the octahedron at three corners

Grünbaum's refinement of Gale's cover: a set of diameter at most `√3` inside the
regular octahedron `{‖x‖₁ ≤ 3/2}` misses, for each coordinate axis, one of the two
corner caps cut off at height `13/15` — two points in opposite caps would be at
distance `26/15 > √3` apart.  Reflecting coordinates accordingly places the set inside
the truncated body `T = {‖x‖₁ ≤ 3/2, x₁ ≤ 13/15, x₂ ≤ 13/15, x₃ ≤ 13/15}`.  (The cut
`13/15 = 0.8667` is a rational hair above the deepest admissible depth `√3/2`, keeping
all later dissection data rational.)

Main result: `Space.exists_truncated_position`.
-/

namespace Borsuk

open Metric Bornology Set Real

namespace Space

/-- Coordinate distances are bounded by the Euclidean distance. -/
@[category API, AMS 52]
theorem abs_coord_sub_le_dist (j : Fin 3) (y z : E3) : |y j - z j| ≤ dist y z := by
  rw [dist_eq_sqrt, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  fin_cases j
  · change (y 0 - z 0) ^ 2 ≤ _
    nlinarith [sq_nonneg (y 1 - z 1), sq_nonneg (y 2 - z 2)]
  · change (y 1 - z 1) ^ 2 ≤ _
    nlinarith [sq_nonneg (y 0 - z 0), sq_nonneg (y 2 - z 2)]
  · change (y 2 - z 2) ^ 2 ≤ _
    nlinarith [sq_nonneg (y 0 - z 0), sq_nonneg (y 1 - z 1)]

/-- The rotation `rot t` as an isometric equivalence. -/
noncomputable def rotIso (t : ℝ) : E3 ≃ᵢ E3 where
  toFun := rot t
  invFun := rot (-t)
  left_inv x := by rw [rot_rot, neg_add_cancel, rot_zero]
  right_inv x := by rw [rot_rot, add_neg_cancel, rot_zero]
  isometry_toFun := Isometry.of_dist_eq fun x y => dist_rot t x y

@[simp, category API, AMS 52] theorem rotIso_apply (t : ℝ) (x : E3) : rotIso t x = rot t x := rfl

/-- Reflection of coordinates by a sign vector, as an isometric equivalence. -/
def reflectIso (σ : Fin 3 → ℝ) (hσ : ∀ j, σ j = 1 ∨ σ j = -1) : E3 ≃ᵢ E3 where
  toFun x := !₂[σ 0 * x 0, σ 1 * x 1, σ 2 * x 2]
  invFun x := !₂[σ 0 * x 0, σ 1 * x 1, σ 2 * x 2]
  left_inv x := by
    refine PiLp.ext fun i => ?_
    fin_cases i
    · change σ 0 * (σ 0 * x 0) = x 0
      rcases hσ 0 with h | h <;> rw [h] <;> ring
    · change σ 1 * (σ 1 * x 1) = x 1
      rcases hσ 1 with h | h <;> rw [h] <;> ring
    · change σ 2 * (σ 2 * x 2) = x 2
      rcases hσ 2 with h | h <;> rw [h] <;> ring
  right_inv x := by
    refine PiLp.ext fun i => ?_
    fin_cases i
    · change σ 0 * (σ 0 * x 0) = x 0
      rcases hσ 0 with h | h <;> rw [h] <;> ring
    · change σ 1 * (σ 1 * x 1) = x 1
      rcases hσ 1 with h | h <;> rw [h] <;> ring
    · change σ 2 * (σ 2 * x 2) = x 2
      rcases hσ 2 with h | h <;> rw [h] <;> ring
  isometry_toFun := Isometry.of_dist_eq fun x y => by
    have hsq : ∀ j, σ j ^ 2 = 1 := fun j => by
      rcases hσ j with h | h <;> rw [h] <;> norm_num
    rw [dist_eq_sqrt, dist_eq_sqrt]
    congr 1
    change (σ 0 * x 0 - σ 0 * y 0) ^ 2 + (σ 1 * x 1 - σ 1 * y 1) ^ 2 +
      (σ 2 * x 2 - σ 2 * y 2) ^ 2 = _
    linear_combination (x 0 - y 0) ^ 2 * hsq 0 + (x 1 - y 1) ^ 2 * hsq 1 +
      (x 2 - y 2) ^ 2 * hsq 2

/-- **Truncated cover.**  A nonempty bounded set of diameter at most `√3` can be moved
by an isometric equivalence into the truncated octahedron: the `ℓ¹`-ball of radius
`3/2` with the three corner caps above height `13/15` removed. -/
@[category API, AMS 52]
theorem exists_truncated_position {K : Set E3} (hb : IsBounded K) (hne : K.Nonempty)
    (hd : diam K ≤ Real.sqrt 3) :
    ∃ e : E3 ≃ᵢ E3, ∀ x ∈ K,
      (|e x 0| + |e x 1| + |e x 2| ≤ 3 / 2) ∧
      e x 0 ≤ 13 / 15 ∧ e x 1 ≤ 13 / 15 ∧ e x 2 ≤ 13 / 15 := by
  have h26 : Real.sqrt 3 ≤ 26 / 15 := by
    rw [show (26 : ℝ) / 15 = Real.sqrt ((26 / 15) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_le_sqrt
    norm_num
  obtain ⟨t, c, hpos⟩ := exists_oct_position hb hne hd
  -- for each axis, either all points stay below the upper cut, or all stay above the
  -- lower cut (two points in opposite caps would be more than `√3` apart)
  have hlow : ∀ j : Fin 3, ¬(∀ x ∈ K, (rot t x - c) j ≤ 13 / 15) →
      ∀ x ∈ K, -(13 / 15) ≤ (rot t x - c) j := by
    intro j hj x hx
    push Not at hj
    obtain ⟨x₀, hx₀K, hx₀⟩ := hj
    have h1 : |(rot t x₀ - c) j - (rot t x - c) j| ≤ dist (rot t x₀ - c) (rot t x - c) :=
      abs_coord_sub_le_dist j _ _
    have h2 : dist (rot t x₀ - c) (rot t x - c) = dist x₀ x := by
      rw [dist_sub_right]
      exact dist_rot t x₀ x
    have h3 : dist x₀ x ≤ diam K := dist_le_diam_of_mem hb hx₀K hx
    have h4 : dist (rot t x₀ - c) (rot t x - c) ≤ Real.sqrt 3 := by
      rw [h2]
      exact h3.trans hd
    have h5 := (abs_le.mp (h1.trans h4)).2
    linarith
  -- choose the reflection signs axis by axis
  classical
  set σ : Fin 3 → ℝ :=
    fun j => if ∀ x ∈ K, (rot t x - c) j ≤ 13 / 15 then 1 else -1 with hσdef
  have hσ : ∀ j, σ j = 1 ∨ σ j = -1 := fun j => by
    simp only [hσdef]
    split <;> simp
  have hσbound : ∀ j : Fin 3, ∀ x ∈ K, σ j * (rot t x - c) j ≤ 13 / 15 := by
    intro j x hx
    simp only [hσdef]
    split
    · rename_i h
      have := h x hx
      linarith
    · rename_i h
      have := hlow j h x hx
      linarith
  -- assemble the isometric equivalence
  refine ⟨((rotIso t).trans (IsometryEquiv.addRight (-c))).trans (reflectIso σ hσ),
    fun x hx => ?_⟩
  have hex : ∀ j : Fin 3,
      (((rotIso t).trans (IsometryEquiv.addRight (-c))).trans (reflectIso σ hσ)) x j =
      σ j * (rot t x - c) j := by
    intro j
    have h1 : (((rotIso t).trans (IsometryEquiv.addRight (-c))).trans
        (reflectIso σ hσ)) x = (reflectIso σ hσ) (rot t x - c) := by
      simp only [IsometryEquiv.trans_apply, rotIso_apply, IsometryEquiv.addRight_apply]
      rw [sub_eq_add_neg]
    rw [h1]
    fin_cases j
    · rfl
    · rfl
    · rfl
  have habs : ∀ j : Fin 3, |σ j * (rot t x - c) j| = |(rot t x - c) j| := by
    intro j
    rw [abs_mul]
    rcases hσ j with h | h <;> rw [h] <;> norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hex 0, hex 1, hex 2, habs 0, habs 1, habs 2]
    exact hpos x hx
  · rw [hex 0]
    exact hσbound 0 x hx
  · rw [hex 1]
    exact hσbound 1 x hx
  · rw [hex 2]
    exact hσbound 2 x hx

end Space

end Borsuk
