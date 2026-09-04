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
# Gale's octahedron cover in dimension three

Every compact set of diameter at most `√3` in `ℝ³` can be rotated and translated into
the regular octahedron `{x : |x₁| + |x₂| + |x₃| ≤ 3/2}` (whose opposite faces are at
distance `√3`).

The proof follows Gale.  The four functionals `L₁ = x₁+x₂+x₃`, `L₂ = x₁-x₂-x₃`,
`L₃ = -x₁+x₂-x₃`, `L₄ = -x₁-x₂+x₃` (the unnormalised outer normals of four pairwise
non-opposite faces) sum to zero, and rotating by `π/2` about the third axis carries the
frame to its negation: `Lᵢ (rot (t+π/2) x) = -L_{τ i} (rot t x)` for the 4-cycle
`τ = (1 3 4 2)`.  Consequently the sum `F(t)` of all slab midpoints
`(sup + inf) Lᵢ (rot t ·)` over `K` satisfies `F(t + π/2) = -F(t)`, so the
intermediate value theorem provides `t*` with `F(t*) = 0`; at such an angle a single
translation centres all four slabs simultaneously (solvable because `ΣLᵢ = 0`), and
each centred slab has half-width `≤ 3/2` since `sup Lᵢ - inf Lᵢ ≤ ‖nᵢ‖ · diam K = 3`.
Finally `max (±L₁, ±L₂, ±L₃, ±L₄) = |x₁| + |x₂| + |x₃|`.

Main result: `Space.exists_oct_position`.
-/

namespace Borsuk

open Metric Bornology Set Real

namespace Space

/-- Three-dimensional Euclidean space. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/- ### The four octahedral functionals -/

/-- First octahedral functional, `x₁ + x₂ + x₃`. -/
def L1 (y : E3) : ℝ := y 0 + y 1 + y 2

/-- Second octahedral functional, `x₁ - x₂ - x₃`. -/
def L2 (y : E3) : ℝ := y 0 - y 1 - y 2

/-- Third octahedral functional, `-x₁ + x₂ - x₃`. -/
def L3 (y : E3) : ℝ := -y 0 + y 1 - y 2

/-- Fourth octahedral functional, `-x₁ - x₂ + x₃`. -/
def L4 (y : E3) : ℝ := -y 0 - y 1 + y 2

/-- The four functionals sum to zero. -/
@[category API, AMS 52]
theorem L_sum (y : E3) : L1 y + L2 y + L3 y + L4 y = 0 := by
  simp only [L1, L2, L3, L4]; ring

/- ### Rotation about the third axis -/

/-- Rotation by angle `t` about the third coordinate axis. -/
noncomputable def rot (t : ℝ) (x : E3) : E3 :=
  !₂[cos t * x 0 - sin t * x 1, sin t * x 0 + cos t * x 1, x 2]

@[simp, category API, AMS 52] theorem rot_apply_zero (t : ℝ) (x : E3) :
    rot t x 0 = cos t * x 0 - sin t * x 1 := rfl

@[simp, category API, AMS 52] theorem rot_apply_one (t : ℝ) (x : E3) :
    rot t x 1 = sin t * x 0 + cos t * x 1 := rfl

@[simp, category API, AMS 52] theorem rot_apply_two (t : ℝ) (x : E3) : rot t x 2 = x 2 := rfl

/-- The rotation preserves distances. -/
@[category API, AMS 52]
theorem dist_rot (t : ℝ) (x y : E3) : dist (rot t x) (rot t y) = dist x y := by
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  congr 1
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [rot_apply_zero, rot_apply_one, rot_apply_two, Real.dist_eq, sq_abs]
  have h := sin_sq_add_cos_sq t
  linear_combination ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) * h

/-- Rotations compose additively in the angle. -/
@[category API, AMS 52]
theorem rot_rot (s t : ℝ) (x : E3) : rot s (rot t x) = rot (s + t) x := by
  refine PiLp.ext fun i => ?_
  fin_cases i
  · change rot s (rot t x) 0 = rot (s + t) x 0
    simp only [rot_apply_zero, rot_apply_one, cos_add, sin_add]; ring
  · change rot s (rot t x) 1 = rot (s + t) x 1
    simp only [rot_apply_zero, rot_apply_one, cos_add, sin_add]; ring
  · rfl

/-- Rotation by `0` is the identity. -/
@[category API, AMS 52]
theorem rot_zero (x : E3) : rot 0 x = x := by
  refine PiLp.ext fun i => ?_
  fin_cases i
  · change rot 0 x 0 = x 0
    simp
  · change rot 0 x 1 = x 1
    simp
  · rfl

/- ### The frame-swap identities

Rotating by an extra `π/2` carries each functional to the negation of another:
the 4-cycle `L₁ ↦ -L₃ ↦ -(-L₄) …`, recorded functional-by-functional. -/

@[category API, AMS 52]
theorem L1_rot_add (t : ℝ) (x : E3) : L1 (rot (t + π / 2) x) = -L3 (rot t x) := by
  simp only [L1, L3, rot_apply_zero, rot_apply_one, rot_apply_two,
    Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  ring

@[category API, AMS 52]
theorem L2_rot_add (t : ℝ) (x : E3) : L2 (rot (t + π / 2) x) = -L1 (rot t x) := by
  simp only [L1, L2, rot_apply_zero, rot_apply_one, rot_apply_two,
    Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  ring

@[category API, AMS 52]
theorem L3_rot_add (t : ℝ) (x : E3) : L3 (rot (t + π / 2) x) = -L4 (rot t x) := by
  simp only [L3, L4, rot_apply_zero, rot_apply_one, rot_apply_two,
    Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  ring

@[category API, AMS 52]
theorem L4_rot_add (t : ℝ) (x : E3) : L4 (rot (t + π / 2) x) = -L2 (rot t x) := by
  simp only [L2, L4, rot_apply_zero, rot_apply_one, rot_apply_two,
    Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  ring

/- ### Lipschitz estimates -/

/-- Distance in `E3`, written out in coordinates. -/
@[category API, AMS 52]
theorem dist_eq_sqrt (y z : E3) :
    dist y z = Real.sqrt ((y 0 - z 0) ^ 2 + (y 1 - z 1) ^ 2 + (y 2 - z 2) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_three]
  simp only [Real.dist_eq, sq_abs]

/-- From `u² ≤ 3v²` with `v ≥ 0` conclude `u ≤ √3 v`. -/
@[category API, AMS 52]
private theorem le_sqrt3_mul_of_sq_le {u v : ℝ} (hv : 0 ≤ v) (h : u ^ 2 ≤ 3 * v ^ 2) :
    u ≤ Real.sqrt 3 * v := by
  have h1 : u ≤ |u| := le_abs_self u
  have h2 : |u| = Real.sqrt (u ^ 2) := (Real.sqrt_sq_eq_abs u).symm
  have h3 : Real.sqrt (u ^ 2) ≤ Real.sqrt (3 * v ^ 2) := Real.sqrt_le_sqrt h
  have h4 : Real.sqrt (3 * v ^ 2) = Real.sqrt 3 * v := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hv]
  linarith

/-- Each octahedral functional is `√3`-Lipschitz (Cauchy–Schwarz, `‖nᵢ‖ = √3`). -/
@[category API, AMS 52]
theorem L1_lip (y z : E3) : L1 y - L1 z ≤ Real.sqrt 3 * dist y z := by
  refine le_sqrt3_mul_of_sq_le dist_nonneg ?_
  rw [dist_eq_sqrt, Real.sq_sqrt (by positivity)]
  simp only [L1]
  nlinarith [sq_nonneg ((y 0 - z 0) - (y 1 - z 1)), sq_nonneg ((y 0 - z 0) - (y 2 - z 2)),
    sq_nonneg ((y 1 - z 1) - (y 2 - z 2)), sq_nonneg ((y 0 - z 0) + (y 1 - z 1)),
    sq_nonneg ((y 0 - z 0) + (y 2 - z 2)), sq_nonneg ((y 1 - z 1) + (y 2 - z 2))]

@[category API, AMS 52]
theorem L2_lip (y z : E3) : L2 y - L2 z ≤ Real.sqrt 3 * dist y z := by
  refine le_sqrt3_mul_of_sq_le dist_nonneg ?_
  rw [dist_eq_sqrt, Real.sq_sqrt (by positivity)]
  simp only [L2]
  nlinarith [sq_nonneg ((y 0 - z 0) - (y 1 - z 1)), sq_nonneg ((y 0 - z 0) - (y 2 - z 2)),
    sq_nonneg ((y 1 - z 1) - (y 2 - z 2)), sq_nonneg ((y 0 - z 0) + (y 1 - z 1)),
    sq_nonneg ((y 0 - z 0) + (y 2 - z 2)), sq_nonneg ((y 1 - z 1) + (y 2 - z 2))]

@[category API, AMS 52]
theorem L3_lip (y z : E3) : L3 y - L3 z ≤ Real.sqrt 3 * dist y z := by
  refine le_sqrt3_mul_of_sq_le dist_nonneg ?_
  rw [dist_eq_sqrt, Real.sq_sqrt (by positivity)]
  simp only [L3]
  nlinarith [sq_nonneg ((y 0 - z 0) - (y 1 - z 1)), sq_nonneg ((y 0 - z 0) - (y 2 - z 2)),
    sq_nonneg ((y 1 - z 1) - (y 2 - z 2)), sq_nonneg ((y 0 - z 0) + (y 1 - z 1)),
    sq_nonneg ((y 0 - z 0) + (y 2 - z 2)), sq_nonneg ((y 1 - z 1) + (y 2 - z 2))]

@[category API, AMS 52]
theorem L4_lip (y z : E3) : L4 y - L4 z ≤ Real.sqrt 3 * dist y z := by
  refine le_sqrt3_mul_of_sq_le dist_nonneg ?_
  rw [dist_eq_sqrt, Real.sq_sqrt (by positivity)]
  simp only [L4]
  nlinarith [sq_nonneg ((y 0 - z 0) - (y 1 - z 1)), sq_nonneg ((y 0 - z 0) - (y 2 - z 2)),
    sq_nonneg ((y 1 - z 1) - (y 2 - z 2)), sq_nonneg ((y 0 - z 0) + (y 1 - z 1)),
    sq_nonneg ((y 0 - z 0) + (y 2 - z 2)), sq_nonneg ((y 1 - z 1) + (y 2 - z 2))]

/-- The squared norm is the sum of squared coordinates. -/
@[category API, AMS 52]
theorem norm_sq_eq (x : E3) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three,
    Real.sq_sqrt (by positivity)]
  simp only [Real.norm_eq_abs, sq_abs]

/-- Rotating a point through nearby angles moves it at most proportionally to the
angle difference. -/
@[category API, AMS 52]
theorem dist_rot_rot (t s : ℝ) (x : E3) :
    dist (rot t x) (rot s x) ≤ 2 * |t - s| * ‖x‖ := by
  have hB : (0 : ℝ) ≤ 2 * |t - s| * ‖x‖ := by positivity
  have hc2 : (cos t - cos s) ^ 2 ≤ (t - s) ^ 2 := by
    have h := abs_le.mp (Real.abs_cos_sub_cos_le t s)
    have h2 := sq_le_sq' h.1 h.2
    rwa [sq_abs] at h2
  have hs2 : (sin t - sin s) ^ 2 ≤ (t - s) ^ 2 := by
    have h := abs_le.mp (Real.abs_sin_sub_sin_le t s)
    have h2 := sq_le_sq' h.1 h.2
    rwa [sq_abs] at h2
  have hx01 : x 0 ^ 2 + x 1 ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_sq_eq]
    nlinarith [sq_nonneg (x 2)]
  rw [dist_eq_sqrt]
  have hA : (rot t x 0 - rot s x 0) ^ 2 + (rot t x 1 - rot s x 1) ^ 2 +
      (rot t x 2 - rot s x 2) ^ 2 ≤ (2 * |t - s| * ‖x‖) ^ 2 := by
    simp only [rot_apply_zero, rot_apply_one, rot_apply_two]
    have hid : (cos t * x 0 - sin t * x 1 - (cos s * x 0 - sin s * x 1)) ^ 2 +
        (sin t * x 0 + cos t * x 1 - (sin s * x 0 + cos s * x 1)) ^ 2 +
        (x 2 - x 2) ^ 2 =
        ((cos t - cos s) ^ 2 + (sin t - sin s) ^ 2) * (x 0 ^ 2 + x 1 ^ 2) := by ring
    rw [hid]
    have hsq : (2 * |t - s| * ‖x‖) ^ 2 = 4 * (t - s) ^ 2 * ‖x‖ ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]
      ring
    rw [hsq]
    have h1 : (cos t - cos s) ^ 2 + (sin t - sin s) ^ 2 ≤ 2 * (t - s) ^ 2 := by linarith
    have h2 : ((cos t - cos s) ^ 2 + (sin t - sin s) ^ 2) * (x 0 ^ 2 + x 1 ^ 2) ≤
        2 * (t - s) ^ 2 * (x 0 ^ 2 + x 1 ^ 2) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : 2 * (t - s) ^ 2 * (x 0 ^ 2 + x 1 ^ 2) ≤ 2 * (t - s) ^ 2 * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hx01 (by positivity)
    nlinarith [sq_nonneg (t - s), sq_nonneg ‖x‖]
  calc Real.sqrt ((rot t x 0 - rot s x 0) ^ 2 + (rot t x 1 - rot s x 1) ^ 2 +
        (rot t x 2 - rot s x 2) ^ 2)
      ≤ Real.sqrt ((2 * |t - s| * ‖x‖) ^ 2) := Real.sqrt_le_sqrt hA
    _ = 2 * |t - s| * ‖x‖ := Real.sqrt_sq hB

/- ### Support values along the rotation -/

/-- Supremum of a functional over the rotated set. -/
noncomputable def suppMax (f : E3 → ℝ) (K : Set E3) (t : ℝ) : ℝ :=
  sSup ((fun x => f (rot t x)) '' K)

/-- Infimum of a functional over the rotated set. -/
noncomputable def suppMin (f : E3 → ℝ) (K : Set E3) (t : ℝ) : ℝ :=
  sInf ((fun x => f (rot t x)) '' K)

section Support

variable {K : Set E3} {f g : E3 → ℝ}

@[category API, AMS 52]
theorem bddAbove_rotImage (hf : ∀ y z : E3, f y - f z ≤ Real.sqrt 3 * dist y z)
    (hb : IsBounded K) (hne : K.Nonempty) (t : ℝ) :
    BddAbove ((fun x => f (rot t x)) '' K) := by
  obtain ⟨x₀, hx₀⟩ := hne
  refine ⟨f (rot t x₀) + Real.sqrt 3 * diam K, ?_⟩
  rintro v ⟨x, hx, rfl⟩
  have h1 := hf (rot t x) (rot t x₀)
  rw [dist_rot] at h1
  have h2 : dist x x₀ ≤ diam K := dist_le_diam_of_mem hb hx hx₀
  have h3 : Real.sqrt 3 * dist x x₀ ≤ Real.sqrt 3 * diam K :=
    mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 3)
  linarith

@[category API, AMS 52]
theorem bddBelow_rotImage (hf : ∀ y z : E3, f y - f z ≤ Real.sqrt 3 * dist y z)
    (hb : IsBounded K) (hne : K.Nonempty) (t : ℝ) :
    BddBelow ((fun x => f (rot t x)) '' K) := by
  obtain ⟨x₀, hx₀⟩ := hne
  refine ⟨f (rot t x₀) - Real.sqrt 3 * diam K, ?_⟩
  rintro v ⟨x, hx, rfl⟩
  have h1 := hf (rot t x₀) (rot t x)
  rw [dist_rot] at h1
  have h2 : dist x₀ x ≤ diam K := dist_le_diam_of_mem hb hx₀ hx
  have h3 : Real.sqrt 3 * dist x₀ x ≤ Real.sqrt 3 * diam K :=
    mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 3)
  linarith

@[category API, AMS 52]
theorem le_suppMax (hf : ∀ y z : E3, f y - f z ≤ Real.sqrt 3 * dist y z)
    (hb : IsBounded K) (hne : K.Nonempty) {t : ℝ} {x : E3} (hx : x ∈ K) :
    f (rot t x) ≤ suppMax f K t :=
  le_csSup (bddAbove_rotImage hf hb hne t) ⟨x, hx, rfl⟩

@[category API, AMS 52]
theorem suppMin_le (hf : ∀ y z : E3, f y - f z ≤ Real.sqrt 3 * dist y z)
    (hb : IsBounded K) (hne : K.Nonempty) {t : ℝ} {x : E3} (hx : x ∈ K) :
    suppMin f K t ≤ f (rot t x) :=
  csInf_le (bddBelow_rotImage hf hb hne t) ⟨x, hx, rfl⟩

/-- The width bound: the slab has width at most `√3 · diam K`. -/
@[category API, AMS 52]
theorem suppMax_le (hf : ∀ y z : E3, f y - f z ≤ Real.sqrt 3 * dist y z)
    (hb : IsBounded K) (hne : K.Nonempty) (t : ℝ) :
    suppMax f K t ≤ suppMin f K t + Real.sqrt 3 * diam K := by
  apply csSup_le (hne.image _)
  rintro v ⟨x, hx, rfl⟩
  have h1 : f (rot t x) - Real.sqrt 3 * diam K ≤ suppMin f K t := by
    apply le_csInf (hne.image _)
    rintro w ⟨y, hy, rfl⟩
    have h2 := hf (rot t x) (rot t y)
    rw [dist_rot] at h2
    have h3 : dist x y ≤ diam K := dist_le_diam_of_mem hb hx hy
    have h4 : Real.sqrt 3 * dist x y ≤ Real.sqrt 3 * diam K :=
      mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg 3)
    linarith
  linarith

/-- One-sided Lipschitz estimate for the support values in the angle. -/
@[category API, AMS 52]
theorem suppMax_sub_le (hf : ∀ y z : E3, f y - f z ≤ Real.sqrt 3 * dist y z)
    (hb : IsBounded K) (hne : K.Nonempty) {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R)
    (t s : ℝ) : suppMax f K t ≤ suppMax f K s + 2 * Real.sqrt 3 * R * |t - s| := by
  apply csSup_le (hne.image _)
  rintro v ⟨x, hx, rfl⟩
  have h1 := hf (rot t x) (rot s x)
  have h2 := dist_rot_rot t s x
  have h3 : f (rot s x) ≤ suppMax f K s := le_suppMax hf hb hne hx
  have h4 : Real.sqrt 3 * dist (rot t x) (rot s x) ≤
      Real.sqrt 3 * (2 * |t - s| * ‖x‖) :=
    mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 3)
  have h5 : Real.sqrt 3 * (2 * |t - s| * ‖x‖) ≤ Real.sqrt 3 * (2 * |t - s| * R) := by
    have h6 : 2 * |t - s| * ‖x‖ ≤ 2 * |t - s| * R :=
      mul_le_mul_of_nonneg_left (hR x hx) (by positivity)
    exact mul_le_mul_of_nonneg_left h6 (Real.sqrt_nonneg 3)
  have h7 : Real.sqrt 3 * (2 * |t - s| * R) = 2 * Real.sqrt 3 * R * |t - s| := by ring
  linarith

@[category API, AMS 52]
theorem suppMin_sub_le (hf : ∀ y z : E3, f y - f z ≤ Real.sqrt 3 * dist y z)
    (hb : IsBounded K) (hne : K.Nonempty) {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R)
    (t s : ℝ) : suppMin f K t ≤ suppMin f K s + 2 * Real.sqrt 3 * R * |t - s| := by
  have h0 : suppMin f K t ≤ suppMin f K s + 2 * Real.sqrt 3 * R * |t - s| := by
    have h1 : suppMin f K s + 2 * Real.sqrt 3 * R * |t - s| ≥ suppMin f K t := by
      have h2 : ∀ x ∈ K, suppMin f K t - 2 * Real.sqrt 3 * R * |t - s| ≤ f (rot s x) := by
        intro x hx
        have h3 := suppMin_le hf hb hne (t := t) hx
        have h4 := hf (rot t x) (rot s x)
        have h5 := dist_rot_rot t s x
        have h6 : Real.sqrt 3 * dist (rot t x) (rot s x) ≤
            Real.sqrt 3 * (2 * |t - s| * R) := by
          have h7 : dist (rot t x) (rot s x) ≤ 2 * |t - s| * R :=
            h5.trans (mul_le_mul_of_nonneg_left (hR x hx) (by positivity))
          exact mul_le_mul_of_nonneg_left h7 (Real.sqrt_nonneg 3)
        have h8 : Real.sqrt 3 * (2 * |t - s| * R) = 2 * Real.sqrt 3 * R * |t - s| := by
          ring
        linarith
      have h9 : suppMin f K t - 2 * Real.sqrt 3 * R * |t - s| ≤ suppMin f K s := by
        apply le_csInf (hne.image _)
        rintro w ⟨y, hy, rfl⟩
        exact h2 y hy
      linarith
    linarith
  exact h0

/-- Transfer of the frame-swap identities to suprema. -/
@[category API, AMS 52]
private theorem suppMax_swap {t : ℝ}
    (hfg : ∀ x : E3, f (rot (t + π / 2) x) = -g (rot t x)) :
    suppMax f K (t + π / 2) = -suppMin g K t := by
  unfold suppMax suppMin
  have himg : (fun x => f (rot (t + π / 2) x)) '' K =
      -((fun x => g (rot t x)) '' K) := by
    rw [← Set.image_neg_eq_neg, Set.image_image]
    exact Set.image_congr fun x _ => hfg x
  rw [himg, Real.sSup_neg]

/-- Transfer of the frame-swap identities to infima. -/
@[category API, AMS 52]
private theorem suppMin_swap {t : ℝ}
    (hfg : ∀ x : E3, f (rot (t + π / 2) x) = -g (rot t x)) :
    suppMin f K (t + π / 2) = -suppMax g K t := by
  unfold suppMax suppMin
  have himg : (fun x => f (rot (t + π / 2) x)) '' K =
      -((fun x => g (rot t x)) '' K) := by
    rw [← Set.image_neg_eq_neg, Set.image_image]
    exact Set.image_congr fun x _ => hfg x
  rw [himg, Real.sInf_neg]

end Support

/- ### The midpoint sum and the intermediate value argument -/

/-- Twice the sum of the four slab midpoints of the rotated set. -/
noncomputable def Fmid (K : Set E3) (t : ℝ) : ℝ :=
  suppMax L1 K t + suppMin L1 K t + (suppMax L2 K t + suppMin L2 K t) +
    (suppMax L3 K t + suppMin L3 K t) + (suppMax L4 K t + suppMin L4 K t)

/-- The frame swap makes the midpoint sum anti-periodic with period `π/2`. -/
@[category API, AMS 52]
theorem Fmid_add (K : Set E3) (t : ℝ) : Fmid K (t + π / 2) = -Fmid K t := by
  unfold Fmid
  rw [suppMax_swap (fun x => L1_rot_add t x), suppMin_swap (fun x => L1_rot_add t x),
    suppMax_swap (fun x => L2_rot_add t x), suppMin_swap (fun x => L2_rot_add t x),
    suppMax_swap (fun x => L3_rot_add t x), suppMin_swap (fun x => L3_rot_add t x),
    suppMax_swap (fun x => L4_rot_add t x), suppMin_swap (fun x => L4_rot_add t x)]
  ring

section IVT

variable {K : Set E3}

/-- The midpoint sum is continuous in the angle. -/
@[category API, AMS 52]
theorem continuous_Fmid (hb : IsBounded K) (hne : K.Nonempty) {R : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) : Continuous (Fmid K) := by
  have hC : ∀ t s : ℝ, Fmid K t - Fmid K s ≤ 16 * Real.sqrt 3 * R * |t - s| := by
    intro t s
    have h1 := suppMax_sub_le L1_lip hb hne hR t s
    have h2 := suppMax_sub_le L2_lip hb hne hR t s
    have h3 := suppMax_sub_le L3_lip hb hne hR t s
    have h4 := suppMax_sub_le L4_lip hb hne hR t s
    have h5 := suppMin_sub_le L1_lip hb hne hR t s
    have h6 := suppMin_sub_le L2_lip hb hne hR t s
    have h7 := suppMin_sub_le L3_lip hb hne hR t s
    have h8 := suppMin_sub_le L4_lip hb hne hR t s
    unfold Fmid
    linarith
  have habs : ∀ t s : ℝ, |Fmid K t - Fmid K s| ≤ 16 * Real.sqrt 3 * R * |t - s| := by
    intro t s
    rw [abs_le]
    constructor
    · have h := hC s t
      rw [abs_sub_comm] at h
      linarith
    · exact hC t s
  have hlip : LipschitzWith (Real.toNNReal (16 * Real.sqrt 3 * R)) (Fmid K) := by
    apply LipschitzWith.of_dist_le_mul
    intro t s
    rw [Real.dist_eq, Real.dist_eq]
    calc |Fmid K t - Fmid K s| ≤ 16 * Real.sqrt 3 * R * |t - s| := habs t s
      _ ≤ Real.toNNReal (16 * Real.sqrt 3 * R) * |t - s| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          rw [Real.coe_toNNReal']
          exact le_max_left _ _
  exact hlip.continuous

/-- **Gale's octahedron cover**: a nonempty bounded subset of `ℝ³` of diameter at most
`√3` can be rotated and translated into the regular octahedron
`{y : |y₁| + |y₂| + |y₃| ≤ 3/2}`, whose opposite faces lie at distance `√3`. -/
@[category API, AMS 52]
theorem exists_oct_position (hb : IsBounded K) (hne : K.Nonempty)
    (hd : diam K ≤ Real.sqrt 3) :
    ∃ (t : ℝ) (c : E3), ∀ x ∈ K,
      |(rot t x - c) 0| + |(rot t x - c) 1| + |(rot t x - c) 2| ≤ 3 / 2 := by
  obtain ⟨R, hRsub⟩ := hb.subset_closedBall (0 : E3)
  have hR : ∀ x ∈ K, ‖x‖ ≤ R := fun x hx => by
    have h := hRsub hx
    rwa [mem_closedBall, dist_zero_right] at h
  -- the intermediate value theorem produces an angle with vanishing midpoint sum
  have hcont : Continuous (Fmid K) := continuous_Fmid hb hne hR
  have hanti : Fmid K (0 + π / 2) = -Fmid K 0 := Fmid_add K 0
  rw [zero_add] at hanti
  have h0mem : (0 : ℝ) ∈ Set.uIcc (Fmid K 0) (Fmid K (π / 2)) := by
    rw [hanti]
    rcases le_total 0 (Fmid K 0) with h | h
    · exact Set.mem_uIcc.mpr (Or.inr ⟨by linarith, h⟩)
    · exact Set.mem_uIcc.mpr (Or.inl ⟨h, by linarith⟩)
  obtain ⟨t₀, -, hF0⟩ := intermediate_value_uIcc hcont.continuousOn h0mem
  -- the four slab midpoints, which sum to zero at `t₀`
  set γ1 := (suppMax L1 K t₀ + suppMin L1 K t₀) / 2 with hγ1
  set γ2 := (suppMax L2 K t₀ + suppMin L2 K t₀) / 2 with hγ2
  set γ3 := (suppMax L3 K t₀ + suppMin L3 K t₀) / 2 with hγ3
  set γ4 := (suppMax L4 K t₀ + suppMin L4 K t₀) / 2 with hγ4
  have hγsum : γ1 + γ2 + γ3 + γ4 = 0 := by
    unfold Fmid at hF0
    rw [hγ1, hγ2, hγ3, hγ4]
    linarith
  -- the simultaneous centering translation
  set c : E3 := !₂[(γ1 + γ2) / 2, (γ1 + γ3) / 2, -(γ2 + γ3) / 2] with hc
  have hc0 : c 0 = (γ1 + γ2) / 2 := rfl
  have hc1 : c 1 = (γ1 + γ3) / 2 := rfl
  have hc2 : c 2 = -(γ2 + γ3) / 2 := rfl
  refine ⟨t₀, c, fun x hx => ?_⟩
  -- per-functional slab bounds around the midpoints
  have hwidth : ∀ f : E3 → ℝ, (∀ y z : E3, f y - f z ≤ Real.sqrt 3 * dist y z) →
      suppMax f K t₀ - suppMin f K t₀ ≤ 3 := by
    intro f hf
    have h := suppMax_le hf hb hne t₀
    have h2 : Real.sqrt 3 * diam K ≤ Real.sqrt 3 * Real.sqrt 3 :=
      mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg 3)
    rw [Real.mul_self_sqrt (by norm_num)] at h2
    linarith
  have hbound : ∀ f : E3 → ℝ, (∀ y z : E3, f y - f z ≤ Real.sqrt 3 * dist y z) →
      f (rot t₀ x) - (suppMax f K t₀ + suppMin f K t₀) / 2 ≤ 3 / 2 ∧
      (suppMax f K t₀ + suppMin f K t₀) / 2 - f (rot t₀ x) ≤ 3 / 2 := by
    intro f hf
    have h1 := le_suppMax hf hb hne (t := t₀) hx
    have h2 := suppMin_le hf hb hne (t := t₀) hx
    have h3 := hwidth f hf
    constructor <;> linarith
  obtain ⟨e1, e1'⟩ := hbound L1 L1_lip
  obtain ⟨e2, e2'⟩ := hbound L2 L2_lip
  obtain ⟨e3, e3'⟩ := hbound L3 L3_lip
  obtain ⟨e4, e4'⟩ := hbound L4 L4_lip
  rw [← hγ1] at e1 e1'
  rw [← hγ2] at e2 e2'
  rw [← hγ3] at e3 e3'
  rw [← hγ4] at e4 e4'
  -- rewrite everything in the coordinates of `rot t₀ x - c`
  have hsub0 : (rot t₀ x - c) 0 = rot t₀ x 0 - c 0 := rfl
  have hsub1 : (rot t₀ x - c) 1 = rot t₀ x 1 - c 1 := rfl
  have hsub2 : (rot t₀ x - c) 2 = rot t₀ x 2 - c 2 := rfl
  have hL1 : L1 (rot t₀ x) =
      (rot t₀ x - c) 0 + (rot t₀ x - c) 1 + (rot t₀ x - c) 2 + γ1 := by
    rw [hsub0, hsub1, hsub2, hc0, hc1, hc2]
    simp only [L1]
    ring
  have hL2 : L2 (rot t₀ x) =
      (rot t₀ x - c) 0 - (rot t₀ x - c) 1 - (rot t₀ x - c) 2 + γ2 := by
    rw [hsub0, hsub1, hsub2, hc0, hc1, hc2]
    simp only [L2]
    ring
  have hL3 : L3 (rot t₀ x) =
      -(rot t₀ x - c) 0 + (rot t₀ x - c) 1 - (rot t₀ x - c) 2 + γ3 := by
    rw [hsub0, hsub1, hsub2, hc0, hc1, hc2]
    simp only [L3]
    ring
  have hL4 : L4 (rot t₀ x) =
      -(rot t₀ x - c) 0 - (rot t₀ x - c) 1 + (rot t₀ x - c) 2 + γ4 := by
    rw [hsub0, hsub1, hsub2, hc0, hc1, hc2]
    simp only [L4]
    have h4 : γ4 = -γ1 - γ2 - γ3 := by linarith
    rw [h4]
    ring
  rw [hL1] at e1 e1'
  rw [hL2] at e2 e2'
  rw [hL3] at e3 e3'
  rw [hL4] at e4 e4'
  -- the eight sign patterns
  rcases abs_cases ((rot t₀ x - c) 0) with ⟨h₁, -⟩ | ⟨h₁, -⟩ <;>
    rcases abs_cases ((rot t₀ x - c) 1) with ⟨h₂, -⟩ | ⟨h₂, -⟩ <;>
      rcases abs_cases ((rot t₀ x - c) 2) with ⟨h₃, -⟩ | ⟨h₃, -⟩ <;>
        rw [h₁, h₂, h₃] <;> linarith

end IVT

end Space

end Borsuk
