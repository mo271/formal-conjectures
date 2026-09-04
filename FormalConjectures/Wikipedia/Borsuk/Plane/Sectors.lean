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
import FormalConjectures.Wikipedia.Borsuk.Plane.Jung

/-!
# The sector decomposition of the plane

The combinatorial half of the planar Borsuk theorem, entirely angle-free: all
"120°-geometry" is expressed through the primitive cube root of unity
`ζ = (-1 + √3 i)/2` and polynomial identities in `ℂ`.

* `mem_sector_cover`: for any unit `w`, every `u : ℂ` satisfies
  `(u * conj (w ζᵏ)).re ≥ ‖u‖/2` for some `k ∈ {0, 1, 2}` — three closed 120°-sectors
  cover the plane;
* `sector_pair_eq`: if two points of a closed sector at distances `≤ r` from the apex
  are "far" (`(p * conj q).re ≤ -r²/2`), then everything degenerates: `q = conj p`,
  both radii equal `r`, and `p.re = r/2` — the pair sits at the two edges of the sector;
* `ratio_of_far_pair`: two contact-circle points at inner product `-r²/2` differ by a
  factor `ζ` or `ζ²`;
* `cube_root_trap`: a unit `w` with `w.re, (ζw).re, (ζ²w).re ≥ -1/2` is a cube root of
  unity — the source of the rigidity of "bad" cutting directions.
-/

namespace Borsuk

open Complex ComplexConjugate Metric Set

namespace Plane

noncomputable section

/-- The primitive cube root of unity `(-1 + √3 i)/2`. -/
def ζ : ℂ := ⟨-(1 / 2), Real.sqrt 3 / 2⟩

@[category API, AMS 52]
theorem s3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

@[category API, AMS 52]
theorem s3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

@[simp, category API, AMS 52] theorem ζ_re : ζ.re = -(1 / 2) := rfl

@[simp, category API, AMS 52] theorem ζ_im : ζ.im = Real.sqrt 3 / 2 := rfl

@[category API, AMS 52]
theorem ζ_sq : ζ ^ 2 = ⟨-(1 / 2), -(Real.sqrt 3 / 2)⟩ := by
  rw [sq]
  apply Complex.ext
  · simp only [Complex.mul_re, ζ_re, ζ_im]
    nlinarith [s3_sq]
  · simp only [Complex.mul_im, ζ_re, ζ_im]
    ring

@[simp, category API, AMS 52] theorem ζ_sq_re : (ζ ^ 2).re = -(1 / 2) := by rw [ζ_sq]

@[simp, category API, AMS 52] theorem ζ_sq_im : (ζ ^ 2).im = -(Real.sqrt 3 / 2) := by rw [ζ_sq]

@[category API, AMS 52]
theorem ζ_pow3 : ζ ^ 3 = 1 := by
  have h : ζ ^ 3 = ζ ^ 2 * ζ := by ring
  rw [h, ζ_sq]
  apply Complex.ext
  · simp only [Complex.mul_re, ζ_re, ζ_im, Complex.one_re]
    nlinarith [s3_sq]
  · simp only [Complex.mul_im, ζ_re, ζ_im, Complex.one_im]
    ring

@[category API, AMS 52]
theorem normSq_ζ : normSq ζ = 1 := by
  rw [normSq_apply]
  simp only [ζ_re, ζ_im]
  nlinarith [s3_sq]

@[category API, AMS 52]
theorem norm_ζ : ‖ζ‖ = 1 := by
  have h := Complex.sq_norm ζ
  rw [normSq_ζ] at h
  nlinarith [norm_nonneg ζ]

@[category API, AMS 52]
theorem conj_ζ : (starRingEnd ℂ) ζ = ζ ^ 2 := by
  rw [ζ_sq]
  apply Complex.ext <;> simp

/-- ‖z‖² decomposed into real and imaginary parts. -/
@[category API, AMS 52]
theorem sq_norm_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, normSq_apply]
  ring

/-- **Sector cover**: the three closed 120°-sectors around directions `w, wζ, wζ²` cover
the plane. -/
@[category API, AMS 52]
theorem mem_sector_cover (u : ℂ) {w : ℂ} (hw : ‖w‖ = 1) :
    ‖u‖ / 2 ≤ (u * conj w).re ∨ ‖u‖ / 2 ≤ (u * conj (w * ζ)).re ∨
      ‖u‖ / 2 ≤ (u * conj (w * ζ ^ 2)).re := by
  by_contra hno
  push Not at hno
  obtain ⟨h0, h1, h2⟩ := hno
  set p := u * conj w with hp
  have hnp : ‖p‖ = ‖u‖ := by
    rw [hp, norm_mul, RCLike.norm_conj, hw, mul_one]
  set a := p.re with ha
  set b := p.im with hb
  set m := ‖u‖ with hm
  have hm2 : m ^ 2 = a ^ 2 + b ^ 2 := by rw [← hnp, sq_norm_eq, ha, hb]
  have hm0 : 0 ≤ m := hm ▸ norm_nonneg u
  -- expand the three sector values
  have e1 : (u * conj (w * ζ)).re = -(1 / 2) * a + Real.sqrt 3 / 2 * b := by
    rw [map_mul, ← mul_assoc, ← hp, Complex.mul_re, conj_ζ, ζ_sq_re, ζ_sq_im, ha, hb]
    ring
  have e2 : (u * conj (w * ζ ^ 2)).re = -(1 / 2) * a - Real.sqrt 3 / 2 * b := by
    have hcc : (starRingEnd ℂ) (ζ ^ 2) = ζ := by
      have h3 := ζ_pow3
      calc (starRingEnd ℂ) (ζ ^ 2) = ((starRingEnd ℂ) ζ) ^ 2 := by rw [map_pow]
        _ = ζ ^ 4 := by rw [conj_ζ]; ring
        _ = ζ ^ 3 * ζ := by ring
        _ = ζ := by rw [h3, one_mul]
    rw [map_mul, ← mul_assoc, ← hp, Complex.mul_re, hcc, ζ_re, ζ_im, ha, hb]
    ring
  rw [e1] at h1
  rw [e2] at h2
  -- now a < m/2, -a/2 + √3 b/2 < m/2, -a/2 - √3 b/2 < m/2, m² = a² + b², m ≥ 0
  have k1 : 0 < m + a + Real.sqrt 3 * b := by nlinarith
  have k2 : 0 < m + a - Real.sqrt 3 * b := by nlinarith
  nlinarith [mul_pos k1 k2, s3_sq, hm2, hm0]

set_option maxHeartbeats 800000 in
-- the chain of `nlinarith` calls below needs more than the default budget
/-- **Rigidity of far pairs in a sector**: two points of a closed sector at distance at
most `r` from the apex whose mutual inner product is at most `-r²/2` are conjugate,
lie on the circle of radius `r`, and sit on the two edges of the sector. -/
@[category API, AMS 52]
theorem sector_pair_eq {p q : ℂ} {r : ℝ} (hr : 0 < r) (hpr : ‖p‖ ≤ r) (hqr : ‖q‖ ≤ r)
    (hpsec : ‖p‖ / 2 ≤ p.re) (hqsec : ‖q‖ / 2 ≤ q.re)
    (hfar : (p * conj q).re ≤ -(r ^ 2 / 2)) :
    q = conj p ∧ ‖p‖ = r ∧ p.re = r / 2 := by
  set ap := p.re with hap
  set bp := p.im with hbp
  set aq := q.re with haq
  set bq := q.im with hbq
  set np := ‖p‖ with hnp
  set nq := ‖q‖ with hnq
  have hp2 : np ^ 2 = ap ^ 2 + bp ^ 2 := by rw [hnp, sq_norm_eq, hap, hbp]
  have hq2 : nq ^ 2 = aq ^ 2 + bq ^ 2 := by rw [hnq, sq_norm_eq, haq, hbq]
  have hnp0 : 0 ≤ np := hnp ▸ norm_nonneg p
  have hnq0 : 0 ≤ nq := hnq ▸ norm_nonneg q
  have hre : (p * conj q).re = ap * aq + bp * bq := by
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [hre] at hfar
  have hap0 : 0 ≤ ap := le_trans (by positivity) hpsec
  have haq0 : 0 ≤ aq := le_trans (by positivity) hqsec
  have haa : np * nq / 4 ≤ ap * aq := by nlinarith
  have hbsq : (bp * bq) ^ 2 = (np ^ 2 - ap ^ 2) * (nq ^ 2 - aq ^ 2) := by
    rw [hp2, hq2]
    ring
  -- Stage A: the radii are forced to equal r
  have hXneg : bp * bq ≤ -(r ^ 2 / 2 + np * nq / 4) := by linarith
  have hX0 : 0 ≤ r ^ 2 / 2 + np * nq / 4 := by nlinarith [mul_nonneg hnp0 hnq0]
  have hsq1 : (r ^ 2 / 2 + np * nq / 4) ^ 2 ≤ (bp * bq) ^ 2 := by
    have h := sq_le_sq' (a := r ^ 2 / 2 + np * nq / 4) (b := -(bp * bq))
      (by linarith) (by linarith)
    rwa [neg_sq] at h
  have hsq2 : (bp * bq) ^ 2 ≤ 9 / 16 * (np * nq) ^ 2 := by
    have h1 : np ^ 2 - ap ^ 2 ≤ 3 / 4 * np ^ 2 := by nlinarith
    have h2 : nq ^ 2 - aq ^ 2 ≤ 3 / 4 * nq ^ 2 := by nlinarith
    have h3 : 0 ≤ nq ^ 2 - aq ^ 2 := by nlinarith [sq_nonneg bq]
    have h4 : 0 ≤ np ^ 2 - ap ^ 2 := by nlinarith [sq_nonneg bp]
    calc (bp * bq) ^ 2 = (np ^ 2 - ap ^ 2) * (nq ^ 2 - aq ^ 2) := hbsq
      _ ≤ (3 / 4 * np ^ 2) * (3 / 4 * nq ^ 2) := by
          exact mul_le_mul h1 h2 h3 (by positivity)
      _ = 9 / 16 * (np * nq) ^ 2 := by ring
  have hprod_ge : r ^ 2 ≤ np * nq := by
    have hX0' : 0 ≤ np * nq := mul_nonneg hnp0 hnq0
    nlinarith [hsq1, hsq2, hX0, hX0']
  have hnq_ge : r ≤ nq := by
    nlinarith [mul_le_mul_of_nonneg_right hpr hnq0]
  have hnqr : nq = r := le_antisymm hqr hnq_ge
  have hnp_ge : r ≤ np := by
    nlinarith [mul_le_mul_of_nonneg_left hqr hnp0]
  have hnpr : np = r := le_antisymm hpr hnp_ge
  -- Stage B: the sector conditions now read r/2 ≤ ap, aq
  have hap2 : r / 2 ≤ ap := by rw [← hnpr]; exact hpsec
  have haq2 : r / 2 ≤ aq := by rw [← hnqr]; exact hqsec
  have hb2 : (r ^ 2 / 2 + ap * aq) ^ 2 ≤ (r ^ 2 - ap ^ 2) * (r ^ 2 - aq ^ 2) := by
    have hXneg' : bp * bq ≤ -(r ^ 2 / 2 + ap * aq) := by linarith
    have hX0' : 0 ≤ r ^ 2 / 2 + ap * aq := by nlinarith [mul_nonneg hap0 haq0]
    have hsq' : (r ^ 2 / 2 + ap * aq) ^ 2 ≤ (bp * bq) ^ 2 := by
      have h := sq_le_sq' (a := r ^ 2 / 2 + ap * aq) (b := -(bp * bq))
        (by linarith) (by linarith)
      rwa [neg_sq] at h
    calc (r ^ 2 / 2 + ap * aq) ^ 2 ≤ (bp * bq) ^ 2 := hsq'
      _ = (np ^ 2 - ap ^ 2) * (nq ^ 2 - aq ^ 2) := hbsq
      _ = (r ^ 2 - ap ^ 2) * (r ^ 2 - aq ^ 2) := by rw [hnpr, hnqr]
  -- expanding: the (ap·aq)² terms cancel, leaving a linear bound
  have hsum : ap * aq + ap ^ 2 + aq ^ 2 ≤ 3 / 4 * r ^ 2 := by
    have h5 : r ^ 2 * (ap * aq + ap ^ 2 + aq ^ 2) ≤ r ^ 2 * (3 / 4 * r ^ 2) := by
      nlinarith [hb2]
    exact le_of_mul_le_mul_left h5 (by positivity)
  have hap_le : ap ≤ r / 2 := by nlinarith [hsum, hap2, haq2]
  have hapr : ap = r / 2 := le_antisymm hap_le hap2
  have haq_le : aq ≤ r / 2 := by nlinarith [hsum, hap2, haq2]
  have haqr : aq = r / 2 := le_antisymm haq_le haq2
  -- Stage C: the imaginary parts are opposite
  have hbps : bp ^ 2 = 3 / 4 * r ^ 2 := by nlinarith [hp2]
  have hbqs : bq ^ 2 = 3 / 4 * r ^ 2 := by nlinarith [hq2]
  have hbpbq : bp * bq = -(3 / 4 * r ^ 2) := by
    have hup : bp * bq ≤ -(3 / 4 * r ^ 2) := by nlinarith
    have hdn : -(3 / 4 * r ^ 2) ≤ bp * bq := by nlinarith [sq_nonneg (bp + bq)]
    linarith
  have hbsum : (bp + bq) ^ 2 = 0 := by
    have h0 : (bp + bq) ^ 2 ≤ 0 := by nlinarith
    exact le_antisymm h0 (sq_nonneg _)
  have hbqe : bq = -bp := by
    have h1 : bp + bq = 0 := by
      exact pow_eq_zero_iff two_ne_zero |>.mp hbsum
    linarith
  refine ⟨?_, hnpr, hapr⟩
  apply Complex.ext
  · rw [Complex.conj_re, ← haq, ← hap, haqr, hapr]
  · rw [Complex.conj_im, ← hbq, ← hbp, hbqe]

/-- Two contact-circle points at mutual inner product exactly `-r²/2` differ by `ζ`
or `ζ²`. -/
@[category API, AMS 52]
theorem ratio_of_far_pair {u v : ℂ} {r : ℝ} (hr : 0 < r) (hu : ‖u‖ = r) (hv : ‖v‖ = r)
    (hre : (v * conj u).re = -(r ^ 2 / 2)) : v = ζ * u ∨ v = ζ ^ 2 * u := by
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    exact absurd hu.symm hr.ne'
  set w := v / u with hw
  have hvw : v = w * u := by rw [hw, div_mul_cancel₀ _ hu0]
  have hnw : ‖w‖ = 1 := by
    rw [hw, norm_div, hu, hv, div_self hr.ne']
  have hwre : w.re = -(1 / 2) := by
    have h1 : v * conj u = w * ((normSq u : ℝ) : ℂ) := by
      calc v * conj u = w * (u * conj u) := by rw [hvw]; ring
        _ = w * ((normSq u : ℝ) : ℂ) := by rw [Complex.mul_conj]
    have h2 : normSq u = r ^ 2 := by rw [normSq_eq_norm_sq, hu]
    rw [h1, h2] at hre
    have h3 : (w * ((r ^ 2 : ℝ) : ℂ)).re = w.re * r ^ 2 := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [h3] at hre
    have h4 : w.re * r ^ 2 = -(1 / 2) * r ^ 2 := by linarith
    exact mul_right_cancel₀ (by positivity : (r : ℝ) ^ 2 ≠ 0) h4
  have hwim : w.im ^ 2 = 3 / 4 := by
    have h1 : w.re ^ 2 + w.im ^ 2 = 1 := by
      rw [← sq_norm_eq, hnw]
      norm_num
    rw [hwre] at h1
    nlinarith
  have hfac : (w.im - Real.sqrt 3 / 2) * (w.im + Real.sqrt 3 / 2) = 0 := by
    nlinarith [s3_sq]
  rcases mul_eq_zero.mp hfac with h | h
  · left
    rw [hvw]
    congr 1
    apply Complex.ext
    · rw [hwre, ζ_re]
    · rw [ζ_im]
      linarith
  · right
    rw [hvw]
    congr 1
    apply Complex.ext
    · rw [hwre, ζ_sq_re]
    · rw [ζ_sq_im]
      linarith

/-- **The cube-root trap**: a unit complex number `w` with
`w.re, (ζw).re, (ζ²w).re ≥ -1/2` is a cube root of unity. -/
@[category API, AMS 52]
theorem cube_root_trap {w : ℂ} (hw : ‖w‖ = 1) (h0 : -(1 / 2) ≤ w.re)
    (h1 : -(1 / 2) ≤ (ζ * w).re) (h2 : -(1 / 2) ≤ (ζ ^ 2 * w).re) :
    w = 1 ∨ w = ζ ∨ w = ζ ^ 2 := by
  set x := w.re with hx
  set y := w.im with hy
  have hxy : x ^ 2 + y ^ 2 = 1 := by
    rw [hx, hy, ← sq_norm_eq, hw]
    norm_num
  have e1 : (ζ * w).re = -(1 / 2) * x - Real.sqrt 3 / 2 * y := by
    rw [Complex.mul_re, ζ_re, ζ_im, ← hx, ← hy]
  have e2 : (ζ ^ 2 * w).re = -(1 / 2) * x + Real.sqrt 3 / 2 * y := by
    rw [Complex.mul_re, ζ_sq_re, ζ_sq_im, ← hx, ← hy]
    ring
  rw [e1] at h1
  rw [e2] at h2
  have hxle : x ≤ 1 := by nlinarith
  have hkey : (1 - x) * (2 + 4 * x) ≤ 0 := by
    have k1 : Real.sqrt 3 * y ≤ 1 - x := by nlinarith [s3_pos]
    have k2 : -(1 - x) ≤ Real.sqrt 3 * y := by nlinarith [s3_pos]
    nlinarith [s3_sq, sq_nonneg (Real.sqrt 3 * y)]
  have hx2 : -(1 / 2) ≤ x := h0
  rcases eq_or_lt_of_le hx2 with heq | hlt
  · have hyv : y ^ 2 = 3 / 4 := by nlinarith
    have hfac : (y - Real.sqrt 3 / 2) * (y + Real.sqrt 3 / 2) = 0 := by
      nlinarith [s3_sq]
    rcases mul_eq_zero.mp hfac with h | h
    · right; left
      apply Complex.ext
      · rw [← hx, ← heq, ζ_re]
      · rw [← hy, ζ_im]
        linarith
    · right; right
      apply Complex.ext
      · rw [← hx, ← heq, ζ_sq_re]
      · rw [← hy, ζ_sq_im]
        linarith
  · have hx1 : x = 1 := by nlinarith
    left
    apply Complex.ext
    · rw [← hx, hx1, Complex.one_re]
    · rw [← hy, Complex.one_im]
      have hy0 : y ^ 2 = 0 := by nlinarith
      exact pow_eq_zero_iff two_ne_zero |>.mp hy0

/-- Powers of `ζ` cycle with period three. -/
@[category API, AMS 52]
theorem ζ_pow4 : ζ ^ 4 = ζ := by
  have h : ζ ^ 4 = ζ ^ 3 * ζ := by ring
  rw [h, ζ_pow3, one_mul]

@[category API, AMS 52]
theorem ζ_pow5 : ζ ^ 5 = ζ ^ 2 := by
  have h : ζ ^ 5 = ζ ^ 3 * ζ ^ 2 := by ring
  rw [h, ζ_pow3, one_mul]

@[category API, AMS 52]
theorem ζ_pow6 : ζ ^ 6 = 1 := by
  have h : ζ ^ 6 = ζ ^ 3 * ζ ^ 3 := by ring
  rw [h, ζ_pow3, one_mul]

@[category API, AMS 52]
theorem ζ_ne_zero : ζ ≠ 0 := by
  intro h
  have h1 := norm_ζ
  rw [h, norm_zero] at h1
  norm_num at h1

@[category API, AMS 52]
theorem re_mul_conj_comm (z w : ℂ) : (z * conj w).re = (w * conj z).re := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Squared distance in `ℂ` via the real inner product. -/
@[category API, AMS 52]
theorem sq_dist_eq (A B : ℂ) : ‖A - B‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 - 2 * (A * conj B).re := by
  rw [sq_norm_eq, sq_norm_eq, sq_norm_eq, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Rewriting `(z * conj u).re` through the ratio `z / u` when `‖u‖ = r`. -/
@[category API, AMS 52]
theorem re_mul_conj_ratio {u : ℂ} {r : ℝ} (hu : ‖u‖ = r) (hu0 : u ≠ 0) (z : ℂ) :
    (z * conj u).re = (z / u).re * r ^ 2 := by
  have h1 : z * conj u = z / u * ((normSq u : ℝ) : ℂ) := by
    calc z * conj u = z / u * (u * conj u) := by
          field_simp
      _ = z / u * ((normSq u : ℝ) : ℂ) := by rw [Complex.mul_conj]
  rw [h1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, normSq_eq_norm_sq, hu]
  ring

set_option maxHeartbeats 1600000 in
-- twelve case leaves with `linear_combination` batteries need a large budget
/-- **Products of far pairs lie in a single `ζ`-orbit**: given two contact-circle pairs
at mutual inner product `-r²/2` whose four cross inner products are at least `-r²/2`,
the products `u·v` and `u₀·v₀` differ by a power of `ζ`. -/
@[category API, AMS 52]
theorem product_orbit {u₀ v₀ u v : ℂ} {r : ℝ} (hr : 0 < r)
    (h₀u : ‖u₀‖ = r) (h₀v : ‖v₀‖ = r) (hu : ‖u‖ = r) (hv : ‖v‖ = r)
    (hre₀ : (v₀ * conj u₀).re = -(r ^ 2 / 2)) (hre : (v * conj u).re = -(r ^ 2 / 2))
    (b1 : -(r ^ 2 / 2) ≤ (u * conj u₀).re) (b2 : -(r ^ 2 / 2) ≤ (v * conj u₀).re)
    (b3 : -(r ^ 2 / 2) ≤ (u * conj v₀).re) (b4 : -(r ^ 2 / 2) ≤ (v * conj v₀).re) :
    u * v = u₀ * v₀ ∨ u * v = ζ * (u₀ * v₀) ∨ u * v = ζ ^ 2 * (u₀ * v₀) := by
  have hu₀0 : u₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at h₀u
    exact absurd h₀u.symm hr.ne'
  have hv₀0 : v₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at h₀v
    exact absurd h₀v.symm hr.ne'
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have hζ0 : ζ ≠ 0 := ζ_ne_zero
  have ha := ratio_of_far_pair hr h₀u h₀v hre₀
  have hb := ratio_of_far_pair hr hu hv hre
  obtain ⟨w, hwdef, huw, hnw⟩ : ∃ w : ℂ, w = u / u₀ ∧ u = w * u₀ ∧ ‖w‖ = 1 :=
    ⟨u / u₀, rfl, (div_mul_cancel₀ u hu₀0).symm,
      by rw [norm_div, hu, h₀u, div_self hr.ne']⟩
  have htrans : ∀ z : ℂ, -(r ^ 2 / 2) ≤ (z * conj u₀).re → -(1 / 2) ≤ (z / u₀).re := by
    intro z hz
    rw [re_mul_conj_ratio h₀u hu₀0 z] at hz
    nlinarith
  have htrans' : ∀ z : ℂ, -(r ^ 2 / 2) ≤ (z * conj v₀).re → -(1 / 2) ≤ (z / v₀).re := by
    intro z hz
    rw [re_mul_conj_ratio h₀v hv₀0 z] at hz
    nlinarith
  have c1 : -(1 / 2) ≤ w.re := by
    have h := htrans u b1
    rwa [← hwdef] at h
  have key : w = 1 ∨ w = ζ ∨ w = ζ ^ 2 := by
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · -- v₀ = ζ u₀, v = ζ u
      refine cube_root_trap hnw c1 ?_ ?_
      · have h := htrans v b2
        have hid : v / u₀ = ζ * w := by
          rw [hb, huw]
          field_simp
        rwa [hid] at h
      · have h := htrans' u b3
        have hid : u / v₀ = ζ ^ 2 * w := by
          rw [ha, huw]
          field_simp
          all_goals ring_nf
          all_goals try simp only [ζ_pow3, mul_one]
        rwa [hid] at h
    · -- v₀ = ζ u₀, v = ζ² u
      refine cube_root_trap hnw c1 ?_ ?_
      · have h := htrans' v b4
        have hid : v / v₀ = ζ * w := by
          rw [hb, ha, huw]
          field_simp
        rwa [hid] at h
      · have h := htrans' u b3
        have hid : u / v₀ = ζ ^ 2 * w := by
          rw [ha, huw]
          field_simp
          all_goals ring_nf
          all_goals try simp only [ζ_pow3, mul_one]
        rwa [hid] at h
    · -- v₀ = ζ² u₀, v = ζ u
      refine cube_root_trap hnw c1 ?_ ?_
      · have h := htrans v b2
        have hid : v / u₀ = ζ * w := by
          rw [hb, huw]
          field_simp
        rwa [hid] at h
      · have h := htrans' v b4
        have hid : v / v₀ = ζ ^ 2 * w := by
          rw [hb, ha, huw]
          field_simp
          all_goals ring_nf
          all_goals try simp only [ζ_pow3, one_mul]
        rwa [hid] at h
    · -- v₀ = ζ² u₀, v = ζ² u
      refine cube_root_trap hnw c1 ?_ ?_
      · have h := htrans' u b3
        have hid : u / v₀ = ζ * w := by
          rw [ha, huw]
          field_simp
          all_goals ring_nf
          all_goals try simp only [ζ_pow3, mul_one]
        rwa [hid] at h
      · have h := htrans v b2
        have hid : v / u₀ = ζ ^ 2 * w := by
          rw [hb, huw]
          field_simp
        rwa [hid] at h
  -- assemble the product in each of the twelve leaves
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · rcases key with hk | hk | hk
    · refine Or.inl ?_
      rw [hb, huw, ha, hk]
      ring
    · refine Or.inr (Or.inr ?_)
      rw [hb, huw, ha, hk]
      ring
    · refine Or.inr (Or.inl ?_)
      rw [hb, huw, ha, hk]
      ring_nf
      simp only [ζ_pow5]
      try ring1
  · rcases key with hk | hk | hk
    · refine Or.inr (Or.inl ?_)
      rw [hb, huw, ha, hk]
      ring
    · refine Or.inl ?_
      rw [hb, huw, ha, hk]
      ring_nf
      simp only [ζ_pow4]
      try ring1
    · refine Or.inr (Or.inr ?_)
      rw [hb, huw, ha, hk]
      ring_nf
      simp only [ζ_pow3, ζ_pow6, one_mul]
      try ring1
  · rcases key with hk | hk | hk
    · refine Or.inr (Or.inr ?_)
      rw [hb, huw, ha, hk]
      ring_nf
      simp only [ζ_pow4]
      try ring1
    · refine Or.inr (Or.inl ?_)
      rw [hb, huw, ha, hk]
      ring
    · refine Or.inl ?_
      rw [hb, huw, ha, hk]
      ring_nf
      simp only [ζ_pow5]
      try ring1
  · rcases key with hk | hk | hk
    · refine Or.inl ?_
      rw [hb, huw, ha, hk]
      ring
    · refine Or.inr (Or.inr ?_)
      rw [hb, huw, ha, hk]
      ring
    · refine Or.inr (Or.inl ?_)
      rw [hb, huw, ha, hk]
      ring_nf
      simp only [ζ_pow3, ζ_pow6, one_mul]
      try ring1

end

end Plane

end Borsuk
