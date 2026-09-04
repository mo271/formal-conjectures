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
import FormalConjectures.Wikipedia.Borsuk.Plane.Sectors
import FormalConjectures.Wikipedia.Borsuk.Definitions

/-!
# Borsuk's conjecture in the plane

Assembly of the planar Borsuk theorem from Jung's inequality (`FormalConjectures/Wikipedia/Borsuk/Plane/Jung.lean`)
and the sector rigidity (`FormalConjectures/Wikipedia/Borsuk/Plane/Sectors.lean`):

every compact set `K ⊆ ℂ` with at least two points splits into three closed
120°-sectors around the Jung centre, each piece of strictly smaller diameter — provided
the sector frame `ω` is chosen so that no "bad" contact pair sits on a sector edge.  By
`product_orbit` the bad pairs have products in a single `ζ`-orbit, and among the four
frames `1, μ, μ², μ³` (`μ = e^{iπ/6}`), whose squares are pairwise distinct, at least
one avoids that three-element orbit.

The main results are `hasBorsukCover_three_of_isCompact` and, after transfer to
`EuclideanSpace ℝ (Fin 2)`, the planar case `borsukConjecture_two` of Borsuk's
conjecture.
-/

namespace Borsuk

open Complex ComplexConjugate Metric Set Module Bornology

namespace Plane

noncomputable section

/-- On a compact set the diameter is attained. -/
@[category API, AMS 52]
theorem exists_dist_eq_diam {α : Type*} [PseudoMetricSpace α] {K : Set α}
    (hK : IsCompact K) (hne : K.Nonempty) : ∃ x ∈ K, ∃ y ∈ K, dist x y = diam K := by
  obtain ⟨⟨x, y⟩, hxy, hmax⟩ := (hK.prod hK).exists_isMaxOn (hne.prod hne)
    continuous_dist.continuousOn
  rw [Set.mem_prod] at hxy
  refine ⟨x, hxy.1, y, hxy.2, le_antisymm
    (dist_le_diam_of_mem hK.isBounded hxy.1 hxy.2) ?_⟩
  refine diam_le_of_forall_dist_le dist_nonneg fun a ha b hb => ?_
  exact hmax (Set.mk_mem_prod ha hb)

/-- The primitive twelfth root of unity `e^{iπ/6}`; its powers `1, μ, μ², μ³` are the
four candidate sector frames. -/
def μ : ℂ := ⟨Real.sqrt 3 / 2, 1/2⟩

@[simp, category API, AMS 52] theorem μ_re : μ.re = Real.sqrt 3 / 2 := rfl

@[simp, category API, AMS 52] theorem μ_im : μ.im = 1/2 := rfl

@[category API, AMS 52]
theorem norm_μ : ‖μ‖ = 1 := by
  have h : ‖μ‖ ^ 2 = 1 := by
    rw [sq_norm_eq, μ_re, μ_im]
    nlinarith [s3_sq]
  nlinarith [norm_nonneg μ]

@[category API, AMS 52]
theorem μ_sq : μ ^ 2 = ⟨1/2, Real.sqrt 3 / 2⟩ := by
  rw [sq]
  apply Complex.ext
  · simp only [Complex.mul_re, μ_re, μ_im]
    nlinarith [s3_sq]
  · simp only [Complex.mul_im, μ_re, μ_im]
    ring

@[category API, AMS 52]
theorem μ_pow4 : (μ ^ 2) ^ 2 = ζ := by
  rw [μ_sq]
  apply Complex.ext
  · rw [ζ_re, sq]
    simp only [Complex.mul_re]
    nlinarith [s3_sq]
  · rw [ζ_im, sq]
    simp only [Complex.mul_im]
    ring

@[category API, AMS 52]
theorem μ_pow3 : μ ^ 3 = Complex.I := by
  have h : μ ^ 3 = μ ^ 2 * μ := by ring
  rw [h, μ_sq]
  apply Complex.ext
  · simp only [Complex.mul_re, μ_re, μ_im, Complex.I_re]
    nlinarith [s3_sq]
  · simp only [Complex.mul_im, μ_re, μ_im, Complex.I_im]
    nlinarith [s3_sq]

@[category API, AMS 52]
theorem μ_pow6 : (μ ^ 3) ^ 2 = -1 := by
  rw [μ_pow3, Complex.I_sq]

/-- **The three-sector decomposition**: every compact set with at least two points in
the plane is covered by three sets of strictly smaller diameter. -/
@[category API, AMS 52]
theorem hasBorsukCover_three_of_isCompact {K : Set ℂ} (hK : IsCompact K)
    (hnt : K.Nontrivial) : HasBorsukCover 3 K := by
  classical
  obtain ⟨c, r, hr, hjung, hsub⟩ := exists_jung_center hK hnt
    (le_of_eq Complex.finrank_real_complex)
  set D := diam K with hD_def
  have hD : 0 < D := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hnt
    exact lt_of_lt_of_le (dist_pos.mpr hxy) (dist_le_diam_of_mem hK.isBounded hx hy)
  have hrad : ∀ x ∈ K, ‖x - c‖ ≤ r := fun x hx => by
    have h := hsub hx
    rwa [mem_closedBall, dist_eq_norm] at h
  have hre_formula : ∀ x y : ℂ, ((x - c) * conj (y - c)).re =
      (‖x - c‖ ^ 2 + ‖y - c‖ ^ 2 - dist x y ^ 2) / 2 := by
    intro x y
    have h := sq_dist_eq (x - c) (y - c)
    have h2 : (x - c) - (y - c) = x - y := by ring
    rw [h2, ← dist_eq_norm] at h
    linarith
  have hr2C : ((r ^ 2 : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  -- choice of the sector frame
  obtain ⟨ω, hω1, hωblock⟩ : ∃ ω : ℂ, ‖ω‖ = 1 ∧
      ∀ x y : ℂ, x ∈ K → y ∈ K → ‖x - c‖ = r → ‖y - c‖ = r →
        ((y - c) * conj (x - c)).re = -(r ^ 2 / 2) → 3 * r ^ 2 = D ^ 2 →
        ∀ k : ℕ, k < 3 → (x - c) * (y - c) ≠ ((r ^ 2 : ℝ) : ℂ) * (ω * ζ ^ k) ^ 2 := by
    rcases em (3 * r ^ 2 = D ^ 2) with hDeq | hDne
    · rcases em (∃ x₀ y₀ : ℂ, x₀ ∈ K ∧ y₀ ∈ K ∧ ‖x₀ - c‖ = r ∧ ‖y₀ - c‖ = r ∧
        ((y₀ - c) * conj (x₀ - c)).re = -(r ^ 2 / 2)) with hbad | hnobad
      · obtain ⟨x₀, y₀, hx₀K, hy₀K, hx₀r, hy₀r, h₀re⟩ := hbad
        set P₀ := (x₀ - c) * (y₀ - c) with hP₀
        -- every bad pair has product in the ζ-orbit of P₀
        have hcross : ∀ z z' : ℂ, z ∈ K → z' ∈ K → ‖z - c‖ = r → ‖z' - c‖ = r →
            -(r ^ 2 / 2) ≤ ((z - c) * conj (z' - c)).re := by
          intro z z' hz hz' hzr hz'r
          rw [hre_formula z z', hzr, hz'r]
          have hd := dist_le_diam_of_mem hK.isBounded hz hz'
          have hd0 : (0 : ℝ) ≤ dist z z' := dist_nonneg
          nlinarith
        have horbit : ∀ x y : ℂ, x ∈ K → y ∈ K → ‖x - c‖ = r → ‖y - c‖ = r →
            ((y - c) * conj (x - c)).re = -(r ^ 2 / 2) →
            (x - c) * (y - c) = P₀ ∨ (x - c) * (y - c) = ζ * P₀ ∨
              (x - c) * (y - c) = ζ ^ 2 * P₀ := by
          intro x y hxK hyK hxr hyr hxyre
          exact product_orbit hr hx₀r hy₀r hxr hyr h₀re hxyre
            (hcross x x₀ hxK hx₀K hxr hx₀r) (hcross y x₀ hyK hx₀K hyr hx₀r)
            (hcross x y₀ hxK hy₀K hxr hy₀r) (hcross y y₀ hyK hy₀K hyr hy₀r)
        -- shifting the orbit by ζ
        have horb_shift : ∀ Q : ℂ, (Q = P₀ ∨ Q = ζ * P₀ ∨ Q = ζ ^ 2 * P₀) →
            (Q * ζ = P₀ ∨ Q * ζ = ζ * P₀ ∨ Q * ζ = ζ ^ 2 * P₀) := by
          rintro Q (rfl | rfl | rfl)
          · right; left; ring
          · right; right; ring
          · left; linear_combination P₀ * ζ_pow3
        -- a good frame: r²ω² avoids the orbit
        have hgood : ∃ ω : ℂ, ‖ω‖ = 1 ∧
            ¬(((r ^ 2 : ℝ) : ℂ) * ω ^ 2 = P₀ ∨ ((r ^ 2 : ℝ) : ℂ) * ω ^ 2 = ζ * P₀ ∨
              ((r ^ 2 : ℝ) : ℂ) * ω ^ 2 = ζ ^ 2 * P₀) := by
          by_cases g0 : ((r ^ 2 : ℝ) : ℂ) * 1 ^ 2 = P₀ ∨
              ((r ^ 2 : ℝ) : ℂ) * 1 ^ 2 = ζ * P₀ ∨ ((r ^ 2 : ℝ) : ℂ) * 1 ^ 2 = ζ ^ 2 * P₀
          swap
          · exact ⟨1, norm_one, g0⟩
          by_cases g1 : ((r ^ 2 : ℝ) : ℂ) * μ ^ 2 = P₀ ∨
              ((r ^ 2 : ℝ) : ℂ) * μ ^ 2 = ζ * P₀ ∨ ((r ^ 2 : ℝ) : ℂ) * μ ^ 2 = ζ ^ 2 * P₀
          swap
          · exact ⟨μ, norm_μ, g1⟩
          by_cases g2 : ((r ^ 2 : ℝ) : ℂ) * (μ ^ 2) ^ 2 = P₀ ∨
              ((r ^ 2 : ℝ) : ℂ) * (μ ^ 2) ^ 2 = ζ * P₀ ∨
              ((r ^ 2 : ℝ) : ℂ) * (μ ^ 2) ^ 2 = ζ ^ 2 * P₀
          swap
          · exact ⟨μ ^ 2, by rw [norm_pow, norm_μ, one_pow], g2⟩
          by_cases g3 : ((r ^ 2 : ℝ) : ℂ) * (μ ^ 3) ^ 2 = P₀ ∨
              ((r ^ 2 : ℝ) : ℂ) * (μ ^ 3) ^ 2 = ζ * P₀ ∨
              ((r ^ 2 : ℝ) : ℂ) * (μ ^ 3) ^ 2 = ζ ^ 2 * P₀
          swap
          · exact ⟨μ ^ 3, by rw [norm_pow, norm_μ, one_pow], g3⟩
          -- all four squares in a three-element set: contradiction by cardinality
          exfalso
          set S3 : Finset ℂ := {P₀, ζ * P₀, ζ ^ 2 * P₀} with hS3
          have hmem : ∀ Q : ℂ, (Q = P₀ ∨ Q = ζ * P₀ ∨ Q = ζ ^ 2 * P₀) → Q ∈ S3 := by
            rintro Q (rfl | rfl | rfl) <;> simp [hS3]
          -- the four squares, in explicit coordinates
          have e1 : ((r ^ 2 : ℝ) : ℂ) * 1 ^ 2 = ((r ^ 2 : ℝ) : ℂ) * 1 := by norm_num
          have e2 : ((r ^ 2 : ℝ) : ℂ) * (μ ^ 2) ^ 2 = ((r ^ 2 : ℝ) : ℂ) * ζ := by
            rw [μ_pow4]
          have e3 : ((r ^ 2 : ℝ) : ℂ) * (μ ^ 3) ^ 2 = ((r ^ 2 : ℝ) : ℂ) * (-1) := by
            rw [μ_pow6]
          have hd01 : (1 : ℂ) ≠ μ ^ 2 := by
            rw [μ_sq]
            intro h
            have h1 := congrArg Complex.re h
            simp only [Complex.one_re] at h1
            norm_num at h1
          have hd02 : (1 : ℂ) ≠ ζ := by
            intro h
            have h1 := congrArg Complex.re h
            rw [Complex.one_re, ζ_re] at h1
            norm_num at h1
          have hd03 : (1 : ℂ) ≠ -1 := by
            intro h
            have := congrArg Complex.re h
            simp at this
            norm_num at this
          have hd12 : μ ^ 2 ≠ ζ := by
            rw [μ_sq]
            intro h
            have h1 := congrArg Complex.re h
            rw [ζ_re] at h1
            norm_num at h1
          have hd13 : μ ^ 2 ≠ -1 := by
            rw [μ_sq]
            intro h
            have h1 := congrArg Complex.im h
            simp only [Complex.neg_im, Complex.one_im, neg_zero] at h1
            nlinarith [s3_pos]
          have hd23 : ζ ≠ -1 := by
            intro h
            have h1 := congrArg Complex.im h
            rw [ζ_im] at h1
            simp only [Complex.neg_im, Complex.one_im, neg_zero] at h1
            nlinarith [s3_pos]
          have hmul : ∀ a b : ℂ, a ≠ b →
              ((r ^ 2 : ℝ) : ℂ) * a ≠ ((r ^ 2 : ℝ) : ℂ) * b := fun a b hab h =>
            hab (mul_left_cancel₀ hr2C h)
          set S4 : Finset ℂ := {((r ^ 2 : ℝ) : ℂ) * 1, ((r ^ 2 : ℝ) : ℂ) * μ ^ 2,
            ((r ^ 2 : ℝ) : ℂ) * ζ, ((r ^ 2 : ℝ) : ℂ) * (-1)} with hS4
          have hsub4 : S4 ⊆ S3 := by
            intro q hq
            simp only [hS4, Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl | rfl | rfl
            · exact hmem _ (by rw [← e1] at *; exact e1 ▸ g0)
            · exact hmem _ g1
            · exact hmem _ (e2 ▸ g2)
            · exact hmem _ (e3 ▸ g3)
          have h3card : S3.card ≤ 3 := by
            refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
            refine le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ ?_)
            simp
          have h4card : S4.card = 4 := by
            rw [hS4]
            rw [Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              push Not
              exact ⟨hmul _ _ hd01, hmul _ _ hd02, hmul _ _ hd03⟩)]
            rw [Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              push Not
              exact ⟨hmul _ _ hd12, hmul _ _ hd13⟩)]
            rw [Finset.card_insert_of_notMem (by
              simp only [Finset.mem_singleton]
              exact hmul _ _ hd23)]
            simp
          have := Finset.card_le_card hsub4
          omega
        obtain ⟨ω, hω1, hωgood⟩ := hgood
        refine ⟨ω, hω1, fun x y hxK hyK hxr hyr hxyre _ k hk heq => ?_⟩
        have horb := horbit x y hxK hyK hxr hyr hxyre
        rw [heq] at horb
        -- reduce r²(ωζᵏ)² to r²ω² inside the orbit
        have hexp : ((r ^ 2 : ℝ) : ℂ) * (ω * ζ ^ k) ^ 2 =
            ((r ^ 2 : ℝ) : ℂ) * ω ^ 2 * (ζ ^ k) ^ 2 := by ring
        rw [hexp] at horb
        interval_cases k
        · rw [pow_zero, one_pow, mul_one] at horb
          exact hωgood horb
        · rw [pow_one] at horb
          have h1 := horb_shift _ horb
          have h2 : ((r ^ 2 : ℝ) : ℂ) * ω ^ 2 * ζ ^ 2 * ζ = ((r ^ 2 : ℝ) : ℂ) * ω ^ 2 := by
            linear_combination (((r ^ 2 : ℝ) : ℂ) * ω ^ 2) * ζ_pow3
          rw [h2] at h1
          exact hωgood h1
        · have h0 : ((r ^ 2 : ℝ) : ℂ) * ω ^ 2 * (ζ ^ 2) ^ 2 =
              ((r ^ 2 : ℝ) : ℂ) * ω ^ 2 * ζ ^ 2 * ζ ^ 2 := by ring
          rw [h0] at horb
          have h1 := horb_shift _ (horb_shift _ horb)
          have h2 : ((r ^ 2 : ℝ) : ℂ) * ω ^ 2 * ζ ^ 2 * ζ ^ 2 * ζ * ζ =
              ((r ^ 2 : ℝ) : ℂ) * ω ^ 2 * ζ ^ 3 * ζ ^ 3 := by ring
          rw [h2] at h1
          have h3 : ((r ^ 2 : ℝ) : ℂ) * ω ^ 2 * ζ ^ 3 * ζ ^ 3 =
              ((r ^ 2 : ℝ) : ℂ) * ω ^ 2 := by
            rw [ζ_pow3]
            ring
          rw [h3] at h1
          exact hωgood h1
      · exact ⟨1, norm_one, fun x y hxK hyK hxr hyr hxyre _ _ _ _ =>
          hnobad ⟨x, y, hxK, hyK, hxr, hyr, hxyre⟩⟩
    · exact ⟨1, norm_one, fun _ _ _ _ _ _ _ hDeq => absurd hDeq hDne⟩
  -- the three sector pieces
  refine ⟨fun k => K ∩ {z | ‖z - c‖ / 2 ≤ ((z - c) * conj (ω * ζ ^ (k : ℕ))).re}, ?_, ?_⟩
  · -- the pieces cover K
    intro z hz
    simp only [Set.mem_iUnion]
    rcases mem_sector_cover (z - c) hω1 with h | h | h
    · exact ⟨0, hz, by
        change ‖z - c‖ / 2 ≤ ((z - c) * conj (ω * ζ ^ ((0 : Fin 3) : ℕ))).re
        simpa [pow_zero, mul_one] using h⟩
    · exact ⟨1, hz, by
        change ‖z - c‖ / 2 ≤ ((z - c) * conj (ω * ζ ^ ((1 : Fin 3) : ℕ))).re
        simpa [pow_one] using h⟩
    · exact ⟨2, hz, h⟩
  · -- each piece has strictly smaller diameter
    intro k
    set W := ω * ζ ^ (k : ℕ) with hW
    have hWnorm : ‖W‖ = 1 := by
      rw [hW, norm_mul, hω1, norm_pow, norm_ζ, one_pow, mul_one]
    set P := K ∩ {z | ‖z - c‖ / 2 ≤ ((z - c) * conj W).re} with hP
    have hPc : IsCompact P := hK.inter_right (isClosed_le
      (((continuous_id.sub continuous_const).norm).div_const 2)
      (Complex.continuous_re.comp ((continuous_id.sub continuous_const).mul
        continuous_const)))
    have hPsub : P ⊆ K := inter_subset_left
    have hPbounded : IsBounded P := hK.isBounded.subset hPsub
    have hdiam_lt : diam P < D := by
      rcases eq_empty_or_nonempty P with hemp | hne'
      · rw [hemp, diam_empty]
        exact hD
      by_contra hge
      push Not at hge
      have hle : diam P ≤ D := diam_mono hPsub hK.isBounded
      obtain ⟨x, hx, y, hy, hxyd⟩ := exists_dist_eq_diam hPc hne'
      have hdxy : dist x y = D := le_antisymm
        (hxyd ▸ hle) (le_trans hge (le_of_eq hxyd.symm))
      -- the two sector coordinates
      set p := (x - c) * conj W with hp
      set q := (y - c) * conj W with hq
      have hnp : ‖p‖ = ‖x - c‖ := by rw [hp, norm_mul, RCLike.norm_conj, hWnorm, mul_one]
      have hnq : ‖q‖ = ‖y - c‖ := by rw [hq, norm_mul, RCLike.norm_conj, hWnorm, mul_one]
      have hWW : conj W * W = 1 := by
        have h := Complex.mul_conj W
        rw [normSq_eq_norm_sq, hWnorm] at h
        rw [mul_comm] at h
        rw [h]
        norm_num
      have hpq : p * conj q = (x - c) * conj (y - c) := by
        have hcq : conj ((y - c) * conj W) = conj (y - c) * W := by
          rw [map_mul, Complex.conj_conj]
        rw [hp, hq, hcq]
        calc (x - c) * conj W * (conj (y - c) * W)
            = (x - c) * conj (y - c) * (conj W * W) := by ring
          _ = (x - c) * conj (y - c) := by rw [hWW, mul_one]
      have hfar : (p * conj q).re ≤ -(r ^ 2 / 2) := by
        rw [hpq, hre_formula x y, hdxy]
        have h1 := hrad x hx.1
        have h2 := hrad y hy.1
        have h3 := norm_nonneg (x - c)
        have h4 := norm_nonneg (y - c)
        nlinarith [hjung]
      have hpsec : ‖p‖ / 2 ≤ p.re := by
        rw [hnp]
        exact hx.2
      have hqsec : ‖q‖ / 2 ≤ q.re := by
        rw [hnq]
        exact hy.2
      obtain ⟨hq_eq, hp_r, hp_re⟩ := sector_pair_eq hr (hnp ▸ hrad x hx.1)
        (hnq ▸ hrad y hy.1) hpsec hqsec hfar
      have hxr : ‖x - c‖ = r := by rw [← hnp]; exact hp_r
      have hyr : ‖y - c‖ = r := by
        rw [← hnq, hq_eq, RCLike.norm_conj]
        exact hp_r
      -- recover x - c and y - c from p and q
      have hxc : x - c = p * W := by
        rw [hp]
        calc x - c = (x - c) * (conj W * W) := by rw [hWW, mul_one]
          _ = (x - c) * conj W * W := by ring
      have hyc : y - c = conj p * W := by
        rw [← hq_eq, hq]
        calc y - c = (y - c) * (conj W * W) := by rw [hWW, mul_one]
          _ = (y - c) * conj W * W := by ring
      have hpim : p.im ^ 2 = 3 / 4 * r ^ 2 := by
        have h := sq_norm_eq p
        rw [hp_r, hp_re] at h
        nlinarith
      -- the pair (x, y) is a bad pair with product r²W²
      have hprod : (x - c) * (y - c) = ((r ^ 2 : ℝ) : ℂ) * W ^ 2 := by
        rw [hxc, hyc]
        have h1 : p * W * (conj p * W) = p * conj p * W ^ 2 := by ring
        rw [h1, Complex.mul_conj, normSq_eq_norm_sq, hp_r]
      have hre_bad : ((y - c) * conj (x - c)).re = -(r ^ 2 / 2) := by
        have hWW' : W * conj W = 1 := by rw [mul_comm]; exact hWW
        have h1 : (y - c) * conj (x - c) = conj p * conj p := by
          have hcx : conj (x - c) = conj p * conj W := by
            rw [hxc, map_mul]
          rw [hyc, hcx]
          calc conj p * W * (conj p * conj W)
              = conj p * conj p * (W * conj W) := by ring
            _ = conj p * conj p := by rw [hWW', mul_one]
        have h2 : conj p * conj p = conj (p * p) := (map_mul (starRingEnd ℂ) p p).symm
        rw [h1, h2, Complex.conj_re, Complex.mul_re, hp_re,
          show p.im * p.im = p.im ^ 2 from (sq p.im).symm, hpim]
        ring
      have hD3 : 3 * r ^ 2 = D ^ 2 := by
        have h1 := hre_formula y x
        rw [hyr, hxr, dist_comm, hdxy, hre_bad] at h1
        linarith
      rw [hW] at hprod
      exact hωblock x y hx.1 hy.1 hxr hyr hre_bad hD3 (k : ℕ) k.isLt hprod
    -- convert the strict diameter bound to `ediam`
    calc ediam P = ENNReal.ofReal (diam P) :=
          (ENNReal.ofReal_toReal hPbounded.ediam_ne_top).symm
      _ < ENNReal.ofReal D := (ENNReal.ofReal_lt_ofReal_iff hD).mpr hdiam_lt
      _ = ediam K := ENNReal.ofReal_toReal hK.isBounded.ediam_ne_top

/-- **Borsuk's conjecture holds in the plane** (Borsuk 1933): every bounded set of at
least two points in `ℝ²` can be divided into three parts of strictly smaller diameter.

The proof avoids Pál's hexagonal universal cover entirely: it combines Jung's
inequality (`exists_jung_center`) with the rigidity of 120°-sectors around the Jung
centre (`sector_pair_eq`, `product_orbit`) and an explicit choice of sector frame among
`1, e^{iπ/6}, e^{iπ/3}, i`. -/
@[category API, AMS 52]
theorem _root_.Borsuk.borsukConjecture_two : BorsukConjecture 2 := by
  intro s hbs hs
  let b : OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) :=
    (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 2))).reindex
      (finCongr finrank_euclideanSpace_fin)
  let e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.isometryOfOrthonormal b
  set K : Set ℂ := closure (⇑e.symm '' s) with hKdef
  have hbK : IsBounded (⇑e.symm '' s) := e.symm.isometry.lipschitz.isBounded_image hbs
  have hcomp : IsCompact K := hbK.isCompact_closure
  have hnt : K.Nontrivial := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hs
    exact ⟨e.symm x, subset_closure (mem_image_of_mem _ hx),
      e.symm y, subset_closure (mem_image_of_mem _ hy),
      fun h => hxy (e.symm.injective h)⟩
  have hK3 := hasBorsukCover_three_of_isCompact hcomp hnt
  have himg : HasBorsukCover 3 (⇑e.symm '' s) := by
    obtain ⟨cov, hcov, hdi⟩ := hK3
    refine ⟨cov, subset_trans subset_closure hcov, fun i => ?_⟩
    calc ediam (cov i) < ediam K := hdi i
      _ = ediam (⇑e.symm '' s) := by rw [hKdef, Metric.ediam_closure]
  have h2 := himg.image e.toIsometryEquiv
  have h3 : ⇑e.toIsometryEquiv '' (⇑e.symm '' s) = s := by
    rw [Set.image_image]
    simp
  rwa [h3] at h2

end

end Plane

end Borsuk
