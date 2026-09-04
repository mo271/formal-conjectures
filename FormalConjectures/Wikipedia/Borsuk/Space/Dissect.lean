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
import FormalConjectures.Wikipedia.Borsuk.Space.Truncate
import FormalConjectures.Wikipedia.Borsuk.Space.Certificates

/-!
# Dissecting the truncated octahedron into four small pieces

The truncated octahedron `T = {‖y‖₁ ≤ 3/2, yⱼ ≤ 13/15}` is covered by four pieces:

* the cap `A`: `y₀ + y₁ + y₂ ≥ 5/12` and all `yⱼ ≥ -7/24`;
* three sectors `Bⱼ`: `yⱼ` is a minimal coordinate, and (`y₀+y₁+y₂ ≤ 5/12` or
  `yⱼ ≤ -7/24`).

Covering is a pure case analysis.  Every piece has diameter at most
`173/100 < √3`: each sector splits into two convex cells, and all the required
squared-distance bounds are the machine-generated certificates of
`FormalConjectures/Wikipedia/Borsuk/Space/Certificates.lean` — the sectors `B₁, B₂` reuse the `B₀` certificates
with permuted coordinates, since all other constraints are symmetric.
-/

namespace Borsuk

open Metric Set Real

namespace Space

/-- The truncated octahedron. -/
def TruncOct : Set E3 :=
  {y | |y 0| + |y 1| + |y 2| ≤ 3 / 2 ∧ y 0 ≤ 13 / 15 ∧ y 1 ≤ 13 / 15 ∧ y 2 ≤ 13 / 15}

/-- The cap piece of the dissection. -/
def pieceA : Set E3 :=
  {y ∈ TruncOct | 5 / 12 ≤ y 0 + y 1 + y 2 ∧
    -(7 / 24) ≤ y 0 ∧ -(7 / 24) ≤ y 1 ∧ -(7 / 24) ≤ y 2}

/-- The sector piece around the first axis. -/
def pieceB0 : Set E3 :=
  {y ∈ TruncOct | y 0 ≤ y 1 ∧ y 0 ≤ y 2 ∧
    (y 0 + y 1 + y 2 ≤ 5 / 12 ∨ y 0 ≤ -(7 / 24))}

/-- The sector piece around the second axis. -/
def pieceB1 : Set E3 :=
  {y ∈ TruncOct | y 1 ≤ y 0 ∧ y 1 ≤ y 2 ∧
    (y 0 + y 1 + y 2 ≤ 5 / 12 ∨ y 1 ≤ -(7 / 24))}

/-- The sector piece around the third axis. -/
def pieceB2 : Set E3 :=
  {y ∈ TruncOct | y 2 ≤ y 0 ∧ y 2 ≤ y 1 ∧
    (y 0 + y 1 + y 2 ≤ 5 / 12 ∨ y 2 ≤ -(7 / 24))}

/-- The four pieces cover the truncated octahedron. -/
@[category API, AMS 52]
theorem truncOct_subset_union :
    TruncOct ⊆ pieceA ∪ pieceB0 ∪ pieceB1 ∪ pieceB2 := by
  intro y hy
  by_cases hw0 : y 0 ≤ -(7 / 24)
  · rcases le_total (y 0) (y 1) with h01 | h01
    · rcases le_total (y 0) (y 2) with h02 | h02
      · exact Or.inl (Or.inl (Or.inr ⟨hy, h01, h02, Or.inr hw0⟩))
      · exact Or.inr ⟨hy, by linarith, by linarith, Or.inr (by linarith)⟩
    · rcases le_total (y 1) (y 2) with h12 | h12
      · exact Or.inl (Or.inr ⟨hy, h01, h12, Or.inr (by linarith)⟩)
      · exact Or.inr ⟨hy, by linarith, h12, Or.inr (by linarith)⟩
  · by_cases hw1 : y 1 ≤ -(7 / 24)
    · rcases le_total (y 1) (y 2) with h12 | h12
      · exact Or.inl (Or.inr ⟨hy, by linarith, h12, Or.inr hw1⟩)
      · exact Or.inr ⟨hy, by linarith, h12, Or.inr (by linarith)⟩
    · by_cases hw2 : y 2 ≤ -(7 / 24)
      · exact Or.inr ⟨hy, by linarith, by linarith, Or.inr hw2⟩
      · by_cases hs : 5 / 12 ≤ y 0 + y 1 + y 2
        · exact Or.inl (Or.inl (Or.inl ⟨hy, hs, by linarith, by linarith, by linarith⟩))
        · rcases le_total (y 0) (y 1) with h01 | h01
          · rcases le_total (y 0) (y 2) with h02 | h02
            · exact Or.inl (Or.inl (Or.inr ⟨hy, h01, h02, Or.inl (by linarith)⟩))
            · exact Or.inr ⟨hy, by linarith, by linarith, Or.inl (by linarith)⟩
          · rcases le_total (y 1) (y 2) with h12 | h12
            · exact Or.inl (Or.inr ⟨hy, h01, h12, Or.inl (by linarith)⟩)
            · exact Or.inr ⟨hy, by linarith, h12, Or.inl (by linarith)⟩

/-- Convert a certified squared-distance bound into a distance bound. -/
@[category API, AMS 52]
private theorem dist_le_of_sq {x y : E3}
    (h : (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 ≤ 149 / 50) :
    dist x y ≤ 173 / 100 := by
  have hd2 : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 := by
    rw [dist_eq_sqrt, Real.sq_sqrt (by positivity)]
  nlinarith [dist_nonneg (x := x) (y := y)]

/-- The cap piece has diameter at most `173/100`. -/
@[category API, AMS 52]
theorem dist_le_pieceA {x y : E3} (hx : x ∈ pieceA) (hy : y ∈ pieceA) :
    dist x y ≤ 173 / 100 := by
  obtain ⟨⟨hxl, hxt0, hxt1, hxt2⟩, hxs, hxw0, hxw1, hxw2⟩ := hx
  obtain ⟨⟨hyl, hyt0, hyt1, hyt2⟩, hys, hyw0, hyw1, hyw2⟩ := hy
  have ax0 := le_abs_self (x 0); have ax0' := neg_abs_le (x 0)
  have ax1 := le_abs_self (x 1); have ax1' := neg_abs_le (x 1)
  have ax2 := le_abs_self (x 2); have ax2' := neg_abs_le (x 2)
  have ay0 := le_abs_self (y 0); have ay0' := neg_abs_le (y 0)
  have ay1 := le_abs_self (y 1); have ay1' := neg_abs_le (y 1)
  have ay2 := le_abs_self (y 2); have ay2' := neg_abs_le (y 2)
  exact dist_le_of_sq (Cert.certAA (x 0) (x 1) (x 2) (y 0) (y 1) (y 2)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith))

section SectorBounds

set_option maxHeartbeats 800000 in
-- the certificate applications carry 28 linarith side goals each
/-- Distance bound between points of the two cells of a sector, stated for permuted
coordinates `(a, b, c)` of `x` and `(d, e, f)` of `y` in which the sector axis comes
first.  The four cell combinations reduce to the three generated certificates. -/
@[category API, AMS 52]
private theorem sector_sq_bound (a b c d e f : ℝ)
    (hxl1 : a + b + c ≤ 3 / 2) (hxl2 : a + b - c ≤ 3 / 2) (hxl3 : a - b + c ≤ 3 / 2)
    (hxl4 : a - b - c ≤ 3 / 2) (hxl5 : -a + b + c ≤ 3 / 2) (hxl6 : -a + b - c ≤ 3 / 2)
    (hxl7 : -a - b + c ≤ 3 / 2) (hxl8 : -a - b - c ≤ 3 / 2)
    (_hxt0 : a ≤ 13 / 15) (hxt1 : b ≤ 13 / 15) (hxt2 : c ≤ 13 / 15)
    (hxm1 : a ≤ b) (hxm2 : a ≤ c) (hxor : a + b + c ≤ 5 / 12 ∨ a ≤ -(7 / 24))
    (hyl1 : d + e + f ≤ 3 / 2) (hyl2 : d + e - f ≤ 3 / 2) (hyl3 : d - e + f ≤ 3 / 2)
    (hyl4 : d - e - f ≤ 3 / 2) (hyl5 : -d + e + f ≤ 3 / 2) (hyl6 : -d + e - f ≤ 3 / 2)
    (hyl7 : -d - e + f ≤ 3 / 2) (hyl8 : -d - e - f ≤ 3 / 2)
    (_hyt0 : d ≤ 13 / 15) (hyt1 : e ≤ 13 / 15) (hyt2 : f ≤ 13 / 15)
    (hym1 : d ≤ e) (hym2 : d ≤ f) (hyor : d + e + f ≤ 5 / 12 ∨ d ≤ -(7 / 24)) :
    (a - d) ^ 2 + (b - e) ^ 2 + (c - f) ^ 2 ≤ 149 / 50 := by
  rcases hxor with hxc | hxc
  · rcases hyor with hyc | hyc
    · exact Cert.certC11 a b c d e f
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)
    · exact Cert.certC12 a b c d e f
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)
  · rcases hyor with hyc | hyc
    · have h := Cert.certC12 d e f a b c
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)
      have e1 : (a - d) ^ 2 = (d - a) ^ 2 := by ring
      have e2 : (b - e) ^ 2 = (e - b) ^ 2 := by ring
      have e3 : (c - f) ^ 2 = (f - c) ^ 2 := by ring
      linarith [h]
    · exact Cert.certC22 a b c d e f
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)

/-- The first sector piece has diameter at most `173/100`. -/
@[category API, AMS 52]
theorem dist_le_pieceB0 {x y : E3} (hx : x ∈ pieceB0) (hy : y ∈ pieceB0) :
    dist x y ≤ 173 / 100 := by
  obtain ⟨⟨hxl, hxt0, hxt1, hxt2⟩, hxm1, hxm2, hxor⟩ := hx
  obtain ⟨⟨hyl, hyt0, hyt1, hyt2⟩, hym1, hym2, hyor⟩ := hy
  have ax0 := le_abs_self (x 0); have ax0' := neg_abs_le (x 0)
  have ax1 := le_abs_self (x 1); have ax1' := neg_abs_le (x 1)
  have ax2 := le_abs_self (x 2); have ax2' := neg_abs_le (x 2)
  have ay0 := le_abs_self (y 0); have ay0' := neg_abs_le (y 0)
  have ay1 := le_abs_self (y 1); have ay1' := neg_abs_le (y 1)
  have ay2 := le_abs_self (y 2); have ay2' := neg_abs_le (y 2)
  have h := sector_sq_bound (x 0) (x 1) (x 2) (y 0) (y 1) (y 2)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) hxt0 hxt1 hxt2 hxm1 hxm2 hxor
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) hyt0 hyt1 hyt2 hym1 hym2 hyor
  exact dist_le_of_sq h

/-- The second sector piece has diameter at most `173/100`. -/
@[category API, AMS 52]
theorem dist_le_pieceB1 {x y : E3} (hx : x ∈ pieceB1) (hy : y ∈ pieceB1) :
    dist x y ≤ 173 / 100 := by
  obtain ⟨⟨hxl, hxt0, hxt1, hxt2⟩, hxm1, hxm2, hxor⟩ := hx
  obtain ⟨⟨hyl, hyt0, hyt1, hyt2⟩, hym1, hym2, hyor⟩ := hy
  have ax0 := le_abs_self (x 0); have ax0' := neg_abs_le (x 0)
  have ax1 := le_abs_self (x 1); have ax1' := neg_abs_le (x 1)
  have ax2 := le_abs_self (x 2); have ax2' := neg_abs_le (x 2)
  have ay0 := le_abs_self (y 0); have ay0' := neg_abs_le (y 0)
  have ay1 := le_abs_self (y 1); have ay1' := neg_abs_le (y 1)
  have ay2 := le_abs_self (y 2); have ay2' := neg_abs_le (y 2)
  have h := sector_sq_bound (x 1) (x 0) (x 2) (y 1) (y 0) (y 2)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) hxt1 hxt0 hxt2 hxm1 hxm2
    (hxor.imp (fun h => by linarith) (fun h => h))
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) hyt1 hyt0 hyt2 hym1 hym2
    (hyor.imp (fun h => by linarith) (fun h => h))
  apply dist_le_of_sq
  linarith [h]

/-- The third sector piece has diameter at most `173/100`. -/
@[category API, AMS 52]
theorem dist_le_pieceB2 {x y : E3} (hx : x ∈ pieceB2) (hy : y ∈ pieceB2) :
    dist x y ≤ 173 / 100 := by
  obtain ⟨⟨hxl, hxt0, hxt1, hxt2⟩, hxm1, hxm2, hxor⟩ := hx
  obtain ⟨⟨hyl, hyt0, hyt1, hyt2⟩, hym1, hym2, hyor⟩ := hy
  have ax0 := le_abs_self (x 0); have ax0' := neg_abs_le (x 0)
  have ax1 := le_abs_self (x 1); have ax1' := neg_abs_le (x 1)
  have ax2 := le_abs_self (x 2); have ax2' := neg_abs_le (x 2)
  have ay0 := le_abs_self (y 0); have ay0' := neg_abs_le (y 0)
  have ay1 := le_abs_self (y 1); have ay1' := neg_abs_le (y 1)
  have ay2 := le_abs_self (y 2); have ay2' := neg_abs_le (y 2)
  have h := sector_sq_bound (x 2) (x 0) (x 1) (y 2) (y 0) (y 1)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) hxt2 hxt0 hxt1 hxm1 hxm2
    (hxor.imp (fun h => by linarith) (fun h => h))
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) hyt2 hyt0 hyt1 hym1 hym2
    (hyor.imp (fun h => by linarith) (fun h => h))
  apply dist_le_of_sq
  linarith [h]

end SectorBounds

/-- The bound `173/100` is strictly below `√3`. -/
@[category API, AMS 52]
theorem bound_lt_sqrt3 : (173 : ℝ) / 100 < Real.sqrt 3 := by
  have h : (173 : ℝ) / 100 = Real.sqrt ((173 / 100) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
  rw [h]
  apply Real.sqrt_lt_sqrt (by positivity)
  norm_num

end Space

end Borsuk
