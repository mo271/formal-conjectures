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
# The minimal enclosing ball and Jung's inequality in the plane

For a compact nonempty set `K` in a finite-dimensional real inner product space we
construct the minimal enclosing ball and prove the planar case of **Jung's theorem**:
if `finrank ℝ E ≤ 2`, the circumradius `r` satisfies `3 r² ≤ (diam K)²`.

The development is designed for formalisation and avoids angles entirely:

* `supRadius K c = sSup (dist c '' K)` is `1`-Lipschitz in `c` and attains a global
  minimum (`exists_min_supRadius`);
* the convex hull of a compact set is compact in finite dimensions
  (`IsCompact.convexHull_of_finiteDimensional`, via Carathéodory);
* at a minimiser `c` the centre lies in the convex hull of the *contact set*
  `K ∩ {x | dist c x = r}` (`center_mem_convexHull_contact`): otherwise a separating
  functional yields a direction along which moving `c` shrinks the radius;
* by Carathéodory, `c` is a convex combination of at most `finrank + 1 ≤ 3` contact
  points, and a quadratic identity produces two contact points with
  `⟪x - c, y - c⟫ ≤ -r²/2` (`exists_pair_of_center_mem`), whence
  `(diam K)² ≥ ‖x - y‖² ≥ 3r²` (`exists_jung_center`).

These are the inputs for the sector decomposition of `FormalConjectures/Wikipedia/Borsuk/Plane/Sectors.lean`.
-/

namespace Borsuk

open Metric Set Module

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E]

section SupRadius

/-- The radius of the smallest ball centred at `c` containing `K`. -/
noncomputable def supRadius (K : Set E) (c : E) : ℝ := sSup ((dist c) '' K)

variable {K : Set E}

@[category API, AMS 52]
theorem dist_le_supRadius (hK : IsCompact K) {x : E} (hx : x ∈ K) (c : E) :
    dist c x ≤ supRadius K c :=
  le_csSup (hK.image (continuous_const.dist continuous_id)).bddAbove ⟨x, hx, rfl⟩

@[category API, AMS 52]
theorem supRadius_le (hne : K.Nonempty) {c : E} {r : ℝ} (h : ∀ x ∈ K, dist c x ≤ r) :
    supRadius K c ≤ r :=
  csSup_le (hne.image _) (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

@[category API, AMS 52]
theorem supRadius_nonneg (hK : IsCompact K) (hne : K.Nonempty) (c : E) :
    0 ≤ supRadius K c := by
  obtain ⟨x, hx⟩ := hne
  exact dist_nonneg.trans (dist_le_supRadius hK hx c)

/-- The supremal distance is attained on a compact set. -/
@[category API, AMS 52]
theorem exists_supRadius_eq_dist (hK : IsCompact K) (hne : K.Nonempty) (c : E) :
    ∃ x ∈ K, dist c x = supRadius K c := by
  obtain ⟨x, hx, hmax⟩ :=
    hK.exists_isMaxOn hne (continuous_const.dist continuous_id).continuousOn
  exact ⟨x, hx, le_antisymm (dist_le_supRadius hK hx c)
    (supRadius_le ⟨x, hx⟩ fun y hy => hmax hy)⟩

@[category API, AMS 52]
theorem supRadius_le_add (hK : IsCompact K) (hne : K.Nonempty) (c c' : E) :
    supRadius K c ≤ supRadius K c' + dist c c' :=
  supRadius_le hne fun x hx =>
    (dist_triangle c c' x).trans (by have := dist_le_supRadius hK hx c'; linarith)

@[category API, AMS 52]
theorem continuous_supRadius (hK : IsCompact K) (hne : K.Nonempty) :
    Continuous (supRadius K) := by
  refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun c c' => ?_)
  rw [Real.dist_eq, NNReal.coe_one, one_mul, abs_sub_le_iff]
  constructor
  · have := supRadius_le_add hK hne c c'
    linarith
  · have := supRadius_le_add hK hne c' c
    rw [dist_comm] at this
    linarith

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The minimal enclosing ball: a global minimiser of `supRadius K` exists. -/
@[category API, AMS 52]
theorem exists_min_supRadius (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ c : E, ∀ c' : E, supRadius K c ≤ supRadius K c' := by
  obtain ⟨x₀, hx₀⟩ := id hne
  set R := supRadius K x₀ with hR
  have hR0 : 0 ≤ R := supRadius_nonneg hK hne x₀
  obtain ⟨c, hcball, hcmin⟩ := (isCompact_closedBall x₀ (2 * R + 1)).exists_isMinOn
    ⟨x₀, mem_closedBall_self (by linarith)⟩ (continuous_supRadius hK hne).continuousOn
  refine ⟨c, fun c' => ?_⟩
  by_cases h : c' ∈ closedBall x₀ (2 * R + 1)
  · exact hcmin h
  · have h1 : supRadius K c ≤ R := hcmin (mem_closedBall_self (by linarith))
    rw [mem_closedBall, not_le] at h
    have h3 : dist c' x₀ ≤ supRadius K c' := dist_le_supRadius hK hx₀ c'
    linarith

end SupRadius

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section DitePad

/-- Summing a `Fin k`-indexed family padded by zeros over `Fin n` (`k ≤ n`). -/
@[category API, AMS 52]
theorem sum_dite_fin {M : Type*} [AddCommMonoid M] {n k : ℕ} (hkn : k ≤ n)
    (f : Fin k → M) :
    (∑ i : Fin n, if h : (i : ℕ) < k then f ⟨(i : ℕ), h⟩ else 0) = ∑ i : Fin k, f i := by
  have hfilter : (Finset.range n).filter (· < k) = Finset.range k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hzero : ∑ i ∈ (Finset.range n).filter (¬ · < k),
      (if h : i < k then f ⟨i, h⟩ else 0) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_filter] at hi
    exact dif_neg hi.2
  rw [Fin.sum_univ_eq_sum_range (fun i => if h : i < k then f ⟨i, h⟩ else 0) n,
    ← Finset.sum_filter_add_sum_filter_not (Finset.range n) (· < k), hfilter, hzero,
    add_zero, ← Fin.sum_univ_eq_sum_range (fun i => if h : i < k then f ⟨i, h⟩ else 0) k]
  exact Finset.sum_congr rfl fun i _ => by rw [dif_pos i.isLt]

end DitePad

section CompactHull

/-- In a finite-dimensional real normed space, the convex hull of a compact set is
compact (Carathéodory). -/
@[category API, AMS 52]
theorem _root_.IsCompact.convexHull_of_finiteDimensional {s : Set E} (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  classical
  rcases eq_empty_or_nonempty s with rfl | ⟨z₀, hz₀⟩
  · simp
  set n := finrank ℝ E + 1 with hn
  have himg : convexHull ℝ s =
      (fun p : (Fin n → ℝ) × (Fin n → E) => ∑ i, p.1 i • p.2 i) ''
        (stdSimplex ℝ (Fin n) ×ˢ Set.univ.pi fun _ => s) := by
    apply Set.Subset.antisymm
    · intro x hx
      rw [convexHull_eq_union] at hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨t, hts, hai, hxt⟩ := hx
      have hcard : t.card ≤ n := by
        have h1 := hai.card_le_finrank_succ
        have h2 : finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → E))) ≤ finrank ℝ E :=
          Submodule.finrank_le _
        rw [Fintype.card_coe] at h1
        omega
      rw [Finset.convexHull_eq] at hxt
      obtain ⟨w, hw0, hw1, hcw⟩ := hxt
      set e : ↥t ≃ Fin t.card := Fintype.equivFinOfCardEq (Fintype.card_coe t) with he
      set q : Fin t.card → E := fun i => ((e.symm i : ↥t) : E) with hq
      have hqmem : ∀ i, q i ∈ t := fun i => (e.symm i).2
      have hsum_tR : ∀ F : E → ℝ, ∑ i : Fin t.card, F (q i) = ∑ y ∈ t, F y := by
        intro F
        rw [← Finset.sum_attach t F]
        exact Fintype.sum_equiv e (fun a => F ((a : ↥t) : E)) (fun i => F (q i))
          (fun a => by rw [hq]; simp) |>.symm
      have hsum_tE : ∀ F : E → E, ∑ i : Fin t.card, F (q i) = ∑ y ∈ t, F y := by
        intro F
        rw [← Finset.sum_attach t F]
        exact Fintype.sum_equiv e (fun a => F ((a : ↥t) : E)) (fun i => F (q i))
          (fun a => by rw [hq]; simp) |>.symm
      refine ⟨(fun i : Fin n => if h : (i : ℕ) < t.card then w (q ⟨(i : ℕ), h⟩) else 0,
               fun i : Fin n => if h : (i : ℕ) < t.card then q ⟨(i : ℕ), h⟩ else z₀),
              ⟨⟨fun i => ?_, ?_⟩, ?_⟩, ?_⟩
      · dsimp only
        split
        · exact hw0 _ (hqmem _)
        · exact le_rfl
      · rw [sum_dite_fin hcard (fun i => w (q i)), hsum_tR (fun y => w y)]
        exact hw1
      · rw [Set.mem_pi]
        intro i _
        dsimp only
        split
        · exact hts (hqmem _)
        · exact hz₀
      · dsimp only
        have hsummand : ∀ i : Fin n,
            (if h : (i : ℕ) < t.card then w (q ⟨(i : ℕ), h⟩) else 0) •
              (if h : (i : ℕ) < t.card then q ⟨(i : ℕ), h⟩ else z₀) =
            (if h : (i : ℕ) < t.card then w (q ⟨(i : ℕ), h⟩) • q ⟨(i : ℕ), h⟩ else 0) := by
          intro i
          by_cases h : (i : ℕ) < t.card
          · rw [dif_pos h, dif_pos h, dif_pos h]
          · rw [dif_neg h, dif_neg h, dif_neg h, zero_smul]
        rw [Finset.sum_congr rfl fun i _ => hsummand i,
          sum_dite_fin hcard (fun i => w (q i) • q i), hsum_tE (fun y => w y • y)]
        rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hcw
        simpa using hcw
    · rintro x ⟨⟨wv, xv⟩, ⟨hwv, hxv⟩, rfl⟩
      rw [Set.mem_pi] at hxv
      have h1 : Finset.univ.centerMass wv xv ∈ convexHull ℝ s :=
        Finset.centerMass_mem_convexHull _ (fun i _ => hwv.1 i)
          (by rw [hwv.2]; norm_num) (fun i _ => hxv i (Set.mem_univ i))
      rwa [Finset.centerMass_eq_of_sum_1 _ _ hwv.2] at h1
  rw [himg]
  exact ((isCompact_stdSimplex ℝ (Fin n)).prod (isCompact_univ_pi fun _ => hs)).image
    (by fun_prop)

end CompactHull

section Contact

variable {K : Set E}

/-- At a minimiser of `supRadius`, the centre lies in the convex hull of the contact
set. -/
@[category API, AMS 52]
theorem center_mem_convexHull_contact (hK : IsCompact K) (hne : K.Nonempty) {c : E}
    (hmin : ∀ c', supRadius K c ≤ supRadius K c') (hr : 0 < supRadius K c) :
    c ∈ convexHull ℝ (K ∩ {x | dist c x = supRadius K c}) := by
  classical
  set r := supRadius K c with hrdef
  set T := K ∩ {x | dist c x = r} with hT
  by_contra hc
  have hTsub : T ⊆ K := fun x hx => hx.1
  have hTc : IsCompact T := hK.of_isClosed_subset
    (hK.isClosed.inter (isClosed_eq (continuous_const.dist continuous_id)
      continuous_const)) hTsub
  obtain ⟨x₁, hx₁K, hx₁⟩ := exists_supRadius_eq_dist hK hne c
  have hx₁T : x₁ ∈ T := ⟨hx₁K, hx₁⟩
  -- separate `c` from the compact convex hull of `T`
  obtain ⟨f, u, hfc, hfT⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ T)
    hTc.convexHull_of_finiteDimensional.isClosed hc
  set v := (InnerProductSpace.toDual ℝ E).symm f with hv
  have hfv : ∀ z, ⟪v, z⟫ = f z := fun z => InnerProductSpace.toDual_symm_apply
  set δ := u - f c with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hvT : ∀ x ∈ T, δ ≤ ⟪v, x - c⟫ := by
    intro x hx
    rw [inner_sub_right, hfv, hfv]
    have := hfT x (subset_convexHull ℝ T hx)
    rw [hδ]
    linarith
  have hvne : v ≠ 0 := by
    intro h0
    have := hvT x₁ hx₁T
    rw [h0, inner_zero_left] at this
    linarith
  -- the low-progress part of `K` stays strictly inside radius `r`
  set K' := K ∩ {x | ⟪v, x - c⟫ ≤ δ / 2} with hK'
  have hK'c : IsCompact K' := hK.of_isClosed_subset
    (hK.isClosed.inter (isClosed_le
      (continuous_const.inner (continuous_id.sub continuous_const)) continuous_const))
    (fun x hx => hx.1)
  obtain ⟨s', hs'r, hs'le⟩ : ∃ s' : ℝ, s' < r ∧ ∀ x ∈ K', dist c x ≤ s' := by
    rcases eq_empty_or_nonempty K' with hemp | hne'
    · exact ⟨0, hr, fun x hx => absurd (hemp ▸ hx) (Set.notMem_empty x)⟩
    · obtain ⟨y, hyK', hy⟩ := exists_supRadius_eq_dist hK'c hne' c
      refine ⟨supRadius K' c, lt_of_le_of_ne
        (supRadius_le hne' fun x hx => dist_le_supRadius hK hx.1 c) ?_,
        fun x hx => dist_le_supRadius hK'c hx c⟩
      intro heq
      have hyT : y ∈ T := ⟨hyK'.1, by rw [Set.mem_ofPred_eq, hy, heq]⟩
      have h1 := hvT y hyT
      have h2 := hyK'.2
      rw [Set.mem_ofPred_eq] at h2
      linarith
  -- move the centre by `ε • v`
  set nv := ‖v‖ with hnv
  have hnv0 : 0 < nv := norm_pos_iff.mpr hvne
  set ε := min (δ / (2 * nv ^ 2)) ((r - s') / (2 * nv)) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  have hε1 : ε ≤ δ / (2 * nv ^ 2) := min_le_left _ _
  have hε2 : ε ≤ (r - s') / (2 * nv) := min_le_right _ _
  set c₁ := c + ε • v with hc₁
  have hδnv : δ ≤ nv * (2 * r) := by
    have h2 := hvT x₁ hx₁T
    have h3 : ⟪v, x₁ - c⟫ ≤ nv * ‖x₁ - c‖ := real_inner_le_norm v (x₁ - c)
    have h4 : ‖x₁ - c‖ = r := by rw [← dist_eq_norm', hx₁]
    nlinarith
  have hεδ : ε * δ ≤ 2 * r ^ 2 := by
    have h1 : ε * (2 * nv ^ 2) ≤ δ := (le_div_iff₀ (by positivity)).mp hε1
    have h2 : δ ^ 2 ≤ (nv * (2 * r)) ^ 2 := by nlinarith
    nlinarith [mul_pos hnv0 hnv0, hε0, hδ0]
  have hbound : ∀ x ∈ K, dist c₁ x ≤ max (s' + ε * nv) (r - ε * δ / (4 * r)) := by
    intro x hx
    by_cases hxK' : x ∈ K'
    · refine le_trans ?_ (le_max_left _ _)
      have h1 : dist c₁ c = ε * nv := by
        rw [hc₁, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos hε0, hnv]
      calc dist c₁ x ≤ dist c₁ c + dist c x := dist_triangle _ _ _
        _ ≤ ε * nv + s' := by have := hs'le x hxK'; linarith
        _ = s' + ε * nv := by ring
    · refine le_trans ?_ (le_max_right _ _)
      have hvx : δ / 2 < ⟪v, x - c⟫ := by
        rw [hK'] at hxK'
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, not_and, not_le] at hxK'
        exact hxK' hx
      have hsq : dist c₁ x ^ 2 = dist c x ^ 2 - 2 * ε * ⟪v, x - c⟫ + ε ^ 2 * nv ^ 2 := by
        have h0 : c₁ - x = -((x - c) - ε • v) := by rw [hc₁]; abel
        rw [dist_eq_norm, h0, norm_neg, norm_sub_sq_real, real_inner_smul_right,
          norm_smul, Real.norm_eq_abs, abs_of_pos hε0, real_inner_comm, dist_eq_norm',
          ← hnv]
        ring
      have hd : dist c x ≤ r := dist_le_supRadius hK hx c
      have hεnv : ε ^ 2 * nv ^ 2 ≤ ε * δ / 2 := by
        have h1 : ε * nv ^ 2 ≤ δ / 2 := by
          calc ε * nv ^ 2 ≤ δ / (2 * nv ^ 2) * nv ^ 2 :=
              mul_le_mul_of_nonneg_right hε1 (by positivity)
            _ = δ / 2 := by field_simp
        calc ε ^ 2 * nv ^ 2 = ε * (ε * nv ^ 2) := by ring
          _ ≤ ε * (δ / 2) := mul_le_mul_of_nonneg_left h1 hε0.le
          _ = ε * δ / 2 := by ring
      have hsqle : dist c₁ x ^ 2 ≤ r ^ 2 - ε * δ / 2 := by
        rw [hsq]
        have h2 : 0 ≤ ε * (⟪v, x - c⟫ - δ / 2) :=
          mul_nonneg hε0.le (by linarith)
        nlinarith [hd, dist_nonneg (x := c) (y := x)]
      have htnn : 0 ≤ r - ε * δ / (4 * r) := by
        rw [sub_nonneg, div_le_iff₀ (by positivity)]
        nlinarith
      have htarget : r ^ 2 - ε * δ / 2 ≤ (r - ε * δ / (4 * r)) ^ 2 := by
        have hexpand : (r - ε * δ / (4 * r)) ^ 2 =
            r ^ 2 - ε * δ / 2 + (ε * δ / (4 * r)) ^ 2 := by
          field_simp
          ring
        nlinarith [sq_nonneg (ε * δ / (4 * r))]
      calc dist c₁ x = Real.sqrt (dist c₁ x ^ 2) := (Real.sqrt_sq dist_nonneg).symm
        _ ≤ Real.sqrt ((r - ε * δ / (4 * r)) ^ 2) := Real.sqrt_le_sqrt (by linarith)
        _ = r - ε * δ / (4 * r) := Real.sqrt_sq htnn
  have hlt : max (s' + ε * nv) (r - ε * δ / (4 * r)) < r := by
    rw [max_lt_iff]
    refine ⟨?_, ?_⟩
    · have h1 : ε * nv ≤ (r - s') / 2 := by
        calc ε * nv ≤ (r - s') / (2 * nv) * nv := mul_le_mul_of_nonneg_right hε2 hnv0.le
          _ = (r - s') / 2 := by field_simp
      linarith
    · have h2 : 0 < ε * δ / (4 * r) := by positivity
      linarith
  have hcontra := hmin c₁
  have hle : supRadius K c₁ ≤ max (s' + ε * nv) (r - ε * δ / (4 * r)) :=
    supRadius_le hne hbound
  linarith

end Contact

section Pair

/-- The quadratic pair lemma in arbitrary dimension: if `c` is a convex combination of
points of `T`, all at distance `r > 0` from `c`, and `finrank ℝ E ≤ n`, then two points
of `T` have inner product at most `-r²/n` at `c`. -/
@[category API, AMS 52]
theorem exists_pair_of_center_mem {T : Set E} {c : E} {r : ℝ} {n : ℕ} (hn : 0 < n)
    (hr : 0 < r) (hT : ∀ x ∈ T, dist c x = r) (hc : c ∈ convexHull ℝ T)
    (hrank : finrank ℝ E ≤ n) :
    ∃ x ∈ T, ∃ y ∈ T, ⟪x - c, y - c⟫ ≤ -(r ^ 2 / (n : ℝ)) := by
  classical
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [convexHull_eq_union] at hc
  simp only [Set.mem_iUnion] at hc
  obtain ⟨t, hts, hai, hct⟩ := hc
  have hcard : t.card ≤ n + 1 := by
    have h1 := hai.card_le_finrank_succ
    have h2 : finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → E))) ≤ finrank ℝ E :=
      Submodule.finrank_le _
    rw [Fintype.card_coe] at h1
    omega
  rw [Finset.convexHull_eq] at hct
  obtain ⟨w, hw0, hw1, hcw⟩ := hct
  rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hcw
  simp only [id] at hcw
  have hzero : ∑ i ∈ t, w i • (i - c) = 0 := by
    have h2 : ∑ i ∈ t, w i • (i - c) = (∑ i ∈ t, w i • i) - (∑ i ∈ t, w i) • c := by
      rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => smul_sub _ _ _
    rw [h2, hcw, hw1, one_smul, sub_self]
  have hexp : (0 : ℝ) = ∑ i ∈ t, ∑ j ∈ t, w i * w j * ⟪i - c, j - c⟫ := by
    have h1 : (0 : ℝ) = ⟪∑ i ∈ t, w i • (i - c), ∑ j ∈ t, w j • (j - c)⟫ := by
      rw [hzero, inner_zero_left]
    rw [h1, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_right]
    ring
  have hnorm : ∀ i ∈ t, ⟪i - c, i - c⟫ = r ^ 2 := by
    intro i hi
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm', hT i (hts hi)]
  by_contra hno
  push Not at hno
  have hgt : ∀ x ∈ t, ∀ y ∈ t, -(r ^ 2 / (n : ℝ)) < ⟪x - c, y - c⟫ := fun x hx y hy =>
    hno x (hts hx) y (hts hy)
  set S := ∑ i ∈ t, w i ^ 2 with hS
  have hScard : 1 ≤ ((n : ℝ) + 1) * S := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := t) (f := w)
    rw [hw1] at h1
    have h2 : (t.card : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hcard
    have h3 : (0 : ℝ) ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith
  by_cases hpair : ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ 0 < w i ∧ 0 < w j
  · -- strict comparison of the double sum against its quadratic lower bound
    obtain ⟨i₀, hi₀, j₀, hj₀, hij₀, hwi₀, hwj₀⟩ := hpair
    have hFle : ∀ p ∈ t ×ˢ t,
        -(r ^ 2 / (n : ℝ)) * (w p.1 * w p.2) +
          (if p.1 = p.2 then w p.1 ^ 2 * (((n : ℝ) + 1) / (n : ℝ) * r ^ 2) else 0) ≤
        w p.1 * w p.2 * ⟪p.1 - c, p.2 - c⟫ := by
      rintro ⟨i, j⟩ hp
      rw [Finset.mem_product] at hp
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, hnorm i hp.1]
        refine le_of_eq ?_
        field_simp
        ring
      · rw [if_neg hij]
        have h1 := hgt i hp.1 j hp.2
        have h2 : 0 ≤ w i * w j := mul_nonneg (hw0 i hp.1) (hw0 j hp.2)
        nlinarith
    have hFlt : ∃ p ∈ t ×ˢ t,
        -(r ^ 2 / (n : ℝ)) * (w p.1 * w p.2) +
          (if p.1 = p.2 then w p.1 ^ 2 * (((n : ℝ) + 1) / (n : ℝ) * r ^ 2) else 0) <
        w p.1 * w p.2 * ⟪p.1 - c, p.2 - c⟫ := by
      refine ⟨(i₀, j₀), Finset.mem_product.mpr ⟨hi₀, hj₀⟩, ?_⟩
      rw [if_neg hij₀]
      have h1 := hgt i₀ hi₀ j₀ hj₀
      have h2 : 0 < w i₀ * w j₀ := mul_pos hwi₀ hwj₀
      nlinarith
    have hsum := Finset.sum_lt_sum hFle hFlt
    have hGsum : ∑ p ∈ t ×ˢ t, w p.1 * w p.2 * ⟪p.1 - c, p.2 - c⟫ = 0 := by
      rw [Finset.sum_product]
      exact hexp.symm
    have hL : ∑ p ∈ t ×ˢ t,
        (-(r ^ 2 / (n : ℝ)) * (w p.1 * w p.2) +
          (if p.1 = p.2 then w p.1 ^ 2 * (((n : ℝ) + 1) / (n : ℝ) * r ^ 2) else 0)) =
        r ^ 2 / (n : ℝ) * (((n : ℝ) + 1) * S - 1) := by
      rw [Finset.sum_add_distrib]
      have h1 : ∑ p ∈ t ×ˢ t, -(r ^ 2 / (n : ℝ)) * (w p.1 * w p.2) =
          -(r ^ 2 / (n : ℝ)) := by
        rw [Finset.sum_product]
        have h2 : ∀ i ∈ t, ∑ j ∈ t, -(r ^ 2 / (n : ℝ)) * (w i * w j) =
            -(r ^ 2 / (n : ℝ)) * w i := by
          intro i _
          calc ∑ j ∈ t, -(r ^ 2 / (n : ℝ)) * (w i * w j)
              = (-(r ^ 2 / (n : ℝ)) * w i) * ∑ j ∈ t, w j := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun j _ => by ring
            _ = -(r ^ 2 / (n : ℝ)) * w i := by rw [hw1, mul_one]
        rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, hw1, mul_one]
      have h3 : ∑ p ∈ t ×ˢ t,
          (if p.1 = p.2 then w p.1 ^ 2 * (((n : ℝ) + 1) / (n : ℝ) * r ^ 2) else 0) =
          S * (((n : ℝ) + 1) / (n : ℝ) * r ^ 2) := by
        rw [Finset.sum_product]
        have h4 : ∀ i ∈ t,
            ∑ j ∈ t, (if i = j then w i ^ 2 * (((n : ℝ) + 1) / (n : ℝ) * r ^ 2) else 0) =
            w i ^ 2 * (((n : ℝ) + 1) / (n : ℝ) * r ^ 2) := by
          intro i hi
          rw [Finset.sum_ite_eq t i
            (fun _ => w i ^ 2 * (((n : ℝ) + 1) / (n : ℝ) * r ^ 2)), if_pos hi]
        rw [Finset.sum_congr rfl h4, hS, Finset.sum_mul]
      rw [h1, h3]
      field_simp
      ring
    rw [hGsum, hL] at hsum
    have hpos : 0 ≤ r ^ 2 / (n : ℝ) * (((n : ℝ) + 1) * S - 1) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  · -- all off-diagonal weight products vanish, so `r = 0`: contradiction
    push Not at hpair
    have hoff : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → w i * w j = 0 := by
      intro i hi j hj hij
      rcases eq_or_lt_of_le (hw0 i hi) with h | h
      · rw [← h, zero_mul]
      · have h2 := hpair i hi j hj hij h
        have hj0 : w j = 0 := le_antisymm h2 (hw0 j hj)
        rw [hj0, mul_zero]
    have hP : (0 : ℝ) = S * r ^ 2 := by
      have hterm : ∀ i ∈ t, ∀ j ∈ t, w i * w j * ⟪i - c, j - c⟫ =
          if i = j then w i ^ 2 * r ^ 2 else 0 := by
        intro i hi j hj
        by_cases hij : i = j
        · subst hij
          rw [if_pos rfl, hnorm i hi]
          ring
        · rw [if_neg hij, hoff i hi j hj hij, zero_mul]
      calc (0 : ℝ) = ∑ i ∈ t, ∑ j ∈ t, w i * w j * ⟪i - c, j - c⟫ := hexp
        _ = ∑ i ∈ t, ∑ j ∈ t, (if i = j then w i ^ 2 * r ^ 2 else 0) :=
            Finset.sum_congr rfl fun i hi =>
              Finset.sum_congr rfl fun j hj => hterm i hi j hj
        _ = ∑ i ∈ t, w i ^ 2 * r ^ 2 := Finset.sum_congr rfl fun i hi => by
            rw [Finset.sum_ite_eq t i (fun _ => w i ^ 2 * r ^ 2), if_pos hi]
        _ = S * r ^ 2 := by rw [hS, Finset.sum_mul]
    have hS0 : S = 0 := by
      rcases mul_eq_zero.mp hP.symm with h | h
      · exact h
      · nlinarith
    have hw00 : ∀ i ∈ t, w i = 0 := by
      intro i hi
      have h1 : w i ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (w j)).mp
          (hS ▸ hS0) i hi
      exact pow_eq_zero_iff (two_ne_zero) |>.mp h1
    rw [Finset.sum_eq_zero hw00] at hw1
    norm_num at hw1

end Pair

section Jung

variable {K : Set E}

/-- **Jung's inequality** in arbitrary dimension: a compact set with at least two
points in a space of dimension at most `n` is contained in a closed ball whose radius
`r` satisfies `(2n+2) r² ≤ n (diam K)²`, i.e. `r ≤ diam K · √(n/(2n+2))`. -/
@[category API, AMS 52]
theorem exists_jung_center_of_finrank_le {n : ℕ} (hn : 0 < n) (hK : IsCompact K)
    (hnt : K.Nontrivial) (hrank : finrank ℝ E ≤ n) :
    ∃ (c : E) (r : ℝ), 0 < r ∧ (2 * (n : ℝ) + 2) * r ^ 2 ≤ (n : ℝ) * diam K ^ 2 ∧
      K ⊆ closedBall c r := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hne : K.Nonempty := hnt.nonempty
  obtain ⟨c, hmin⟩ := exists_min_supRadius hK hne
  set r := supRadius K c with hrdef
  have hr : 0 < r := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hnt
    have h1 := dist_le_supRadius hK hx c
    have h2 := dist_le_supRadius hK hy c
    have h3 : 0 < dist x y := dist_pos.mpr hxy
    have h4 := dist_triangle x c y
    have h5 : dist x c = dist c x := dist_comm x c
    linarith
  have hc := center_mem_convexHull_contact hK hne hmin hr
  obtain ⟨x, hxT, y, hyT, hxy⟩ :=
    exists_pair_of_center_mem hn hr (fun x hx => hx.2) hc hrank
  refine ⟨c, r, hr, ?_, fun z hz => mem_closedBall'.mpr (dist_le_supRadius hK hz c)⟩
  have h1 : dist x y ≤ diam K := dist_le_diam_of_mem hK.isBounded hxT.1 hyT.1
  have h2 : dist x y ^ 2 = ‖x - c‖ ^ 2 - 2 * ⟪x - c, y - c⟫ + ‖y - c‖ ^ 2 := by
    have h3 : x - y = (x - c) - (y - c) := by abel
    rw [dist_eq_norm, h3, norm_sub_sq_real]
  have hx2 : ‖x - c‖ = r := by rw [← dist_eq_norm', hxT.2]
  have hy2 : ‖y - c‖ = r := by rw [← dist_eq_norm', hyT.2]
  rw [hx2, hy2] at h2
  have h6 : 2 * r ^ 2 + 2 * (r ^ 2 / (n : ℝ)) ≤ dist x y ^ 2 := by
    rw [h2]
    linarith
  have h7 : dist x y ^ 2 ≤ diam K ^ 2 := by
    nlinarith [diam_nonneg (s := K), dist_nonneg (x := x) (y := y)]
  have h8 : (n : ℝ) * (2 * r ^ 2 + 2 * (r ^ 2 / (n : ℝ))) = (2 * (n : ℝ) + 2) * r ^ 2 := by
    field_simp
  nlinarith
end Jung

section JungTwo

variable {K : Set E}

/-- Jung's inequality in dimension at most `2`, in the form used by the planar Borsuk
development: `3 r² ≤ (diam K)²`. -/
@[category API, AMS 52]
theorem exists_jung_center (hK : IsCompact K) (hnt : K.Nontrivial)
    (hrank : finrank ℝ E ≤ 2) :
    ∃ (c : E) (r : ℝ), 0 < r ∧ 3 * r ^ 2 ≤ diam K ^ 2 ∧ K ⊆ closedBall c r := by
  obtain ⟨c, r, hr, hj, hs⟩ :=
    exists_jung_center_of_finrank_le (by norm_num) hK hnt hrank
  refine ⟨c, r, hr, ?_, hs⟩
  push_cast at hj
  linarith

end JungTwo

end Borsuk
