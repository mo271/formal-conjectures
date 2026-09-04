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
import FormalConjectures.Wikipedia.Borsuk.G2Four.Partition

/-!
# The 63-dimensional configuration

The 320 vertices of `C = V(Γ) \ (B₁ ∪ B₂ ∪ B₃)` have vanishing `Nint`-sums over each
`Bᵢ`, so their configuration vectors are orthogonal to both
`u₁₂ = ∑_{B₁} v̄ - ∑_{B₂} v̄` and `u₂₃ = ∑_{B₂} v̄ - ∑_{B₃} v̄`, which are linearly
independent (`⟪u₁₂, u₁₂⟫ = ⟪u₂₃, u₂₃⟫ = 36864`, `⟪u₁₂, u₂₃⟫ = -18432`).  Hence the
`C`-vectors lie in a subspace of dimension `65 - 2 = 63`.

Following the construction of Grinsztajn (2026, found with AI assistance and verified by
exact computation; see `FormalConjectures.Wikipedia.BorsukConjecture`), one more point
is added: the orthogonal projection `p = v̄₀ - u₁₂/48 - u₂₃/96` of the deleted
`B₁`-vertex `0` into that subspace (`⟪p, p⟫ = 78`, `⟪p, v̄ₓ⟫ = ⟪v̄₀, v̄ₓ⟫` for `x ∈ C`),
rescaled by `μ = (-1 + √222)/13`, the positive root of `13μ² + 2μ - 17 = 0`.  This makes
the distance from `μ·p` to the non-neighbours of `0` in `C` exactly `√192` (the diameter)
and to the neighbours `√(192 - 48μ) < √192`.  A subset of the resulting 321 points
avoiding the distance `√192` therefore consists of pairwise-adjacent `C`-vertices,
together possibly with `μ·p` — whose companions must be neighbours of `0`, so that
adjoining the vertex `0` again yields a clique.  Every such subset has at most 5 points
(`clique_card_le_five`), and `⌈321/5⌉ = 65 > 64`.

The main result `exists_borsuk63` is the statement `exists_borsuk63_vectors` of
`FormalConjectures/Wikipedia/Borsuk/Counterexamples.lean`.
-/

namespace Borsuk

namespace G2Four

open Module Set Finset Submodule

open scoped RealInnerProductSpace

set_option linter.style.nativeDecide false

/-- The 320 vertices outside `B₁ ∪ B₂ ∪ B₃`. -/
def Cset : Finset (Fin 416) := Finset.univ \ (B1 ∪ B2 ∪ B3)

@[category test, AMS 52]
theorem Cset_card : Cset.card = 320 := by native_decide

@[category test, AMS 52]
theorem bstar_notMem_Cset : (0 : Fin 416) ∉ Cset := by native_decide

@[category test, AMS 52]
theorem sum_Nint_B1_C : ∀ x ∈ Cset, (∑ y ∈ B1, Nint y x) = 0 := by native_decide

@[category test, AMS 52]
theorem sum_Nint_B2_C : ∀ x ∈ Cset, (∑ y ∈ B2, Nint y x) = 0 := by native_decide

@[category test, AMS 52]
theorem sum_Nint_B3_C : ∀ x ∈ Cset, (∑ y ∈ B3, Nint y x) = 0 := by native_decide

@[category test, AMS 52]
theorem sum_Nint_B1_B1 : (∑ y ∈ B1, ∑ z ∈ B1, Nint y z) = 2048 := by native_decide

@[category test, AMS 52]
theorem sum_Nint_B1_B2 : (∑ y ∈ B1, ∑ z ∈ B2, Nint y z) = -1024 := by native_decide

@[category test, AMS 52]
theorem sum_Nint_B2_B1 : (∑ y ∈ B2, ∑ z ∈ B1, Nint y z) = -1024 := by native_decide

@[category test, AMS 52]
theorem sum_Nint_B1_B3 : (∑ y ∈ B1, ∑ z ∈ B3, Nint y z) = -1024 := by native_decide

@[category test, AMS 52]
theorem sum_Nint_B1_bstar : (∑ y ∈ B1, Nint y 0) = 64 := by native_decide

@[category test, AMS 52]
theorem sum_Nint_B2_bstar : (∑ y ∈ B2, Nint y 0) = -32 := by native_decide

@[category test, AMS 52]
theorem sum_Nint_B3_bstar : (∑ y ∈ B3, Nint y 0) = -32 := by native_decide

@[category test, AMS 52]
theorem exists_nonadj_C : ∃ i ∈ Cset, ∃ j ∈ Cset, i ≠ j ∧ adj i j = false := by
  native_decide

@[category API, AMS 52]
theorem twelve_le_sqrt192 : (12 : ℝ) ≤ Real.sqrt 192 := by
  rw [show (12 : ℝ) = Real.sqrt 144 by
    rw [show (144 : ℝ) = 12 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by norm_num)

set_option maxHeartbeats 1000000 in
-- the single assembly proof below is long; the default heartbeat budget is not enough
/-- **The 63-dimensional configuration exists**: 321 points of diameter `√192` in `ℝ⁶³`
in which every subset avoiding the distance `√192` has at most 5 points. -/
@[category API, AMS 52]
theorem exists_borsuk63 :
    ∃ v : Fin 321 → EuclideanSpace ℝ (Fin 63),
      Function.Injective v ∧
      (∀ i j, dist (v i) (v j) ≤ Real.sqrt 192) ∧
      (∃ i j, dist (v i) (v j) = Real.sqrt 192) ∧
      ∀ s : Finset (Fin 321),
        (∀ i ∈ s, ∀ j ∈ s, dist (v i) (v j) < Real.sqrt 192) → s.card ≤ 5 := by
  classical
  -- the 65-dimensional model of the `G₂(4)` configuration
  obtain ⟨w, hw⟩ := exists_inner_preserving_of_mem vRow vRow_mem_Wspan finrank_Wspan
  have hdist : ∀ i j, dist (w i) (w j) = dist (vRow i) (vRow j) := dist_eq_of_inner_eq hw
  have hinner : ∀ i j, ⟪w i, w j⟫ = 6 * (Nint i j : ℝ) := fun i j => by rw [hw, inner_vRow]
  have hsum : ∀ (A : Finset (Fin 416)) (x : Fin 416),
      ⟪∑ y ∈ A, w y, w x⟫ = 6 * ((∑ y ∈ A, Nint y x : ℤ) : ℝ) := by
    intro A x
    rw [sum_inner, Finset.sum_congr rfl fun y (_ : y ∈ A) => hinner y x]
    push_cast [Finset.mul_sum]
    rfl
  have hsum2 : ∀ A B : Finset (Fin 416),
      ⟪∑ y ∈ A, w y, ∑ z ∈ B, w z⟫ = 6 * ((∑ y ∈ A, ∑ z ∈ B, Nint y z : ℤ) : ℝ) := by
    intro A B
    rw [sum_inner]
    have h1 : ∀ y ∈ A, ⟪w y, ∑ z ∈ B, w z⟫ = ∑ z ∈ B, 6 * (Nint y z : ℝ) := fun y _ => by
      rw [inner_sum]
      exact Finset.sum_congr rfl fun z _ => hinner y z
    rw [Finset.sum_congr rfl h1]
    push_cast [Finset.mul_sum]
    rfl
  set u12 : EuclideanSpace ℝ (Fin 65) := (∑ y ∈ B1, w y) - ∑ y ∈ B2, w y with hu12
  set u23 : EuclideanSpace ℝ (Fin 65) := (∑ y ∈ B2, w y) - ∑ y ∈ B3, w y with hu23
  have g11 : ⟪u12, u12⟫ = 36864 := by
    rw [hu12, inner_sub_left, inner_sub_right, inner_sub_right, hsum2, hsum2, hsum2, hsum2,
      sum_Nint_B1_B1, sum_Nint_B1_B2, sum_Nint_B2_B1, sum_Nint_B2_B2]
    norm_num
  have g12 : ⟪u12, u23⟫ = -18432 := by
    rw [hu12, hu23, inner_sub_left, inner_sub_right, inner_sub_right, hsum2, hsum2, hsum2,
      hsum2, sum_Nint_B1_B2, sum_Nint_B1_B3, sum_Nint_B2_B2, sum_Nint_B2_B3]
    norm_num
  have g21 : ⟪u23, u12⟫ = -18432 := by rw [real_inner_comm, g12]
  have g22 : ⟪u23, u23⟫ = 36864 := by
    rw [hu23, inner_sub_left, inner_sub_right, inner_sub_right, hsum2, hsum2, hsum2, hsum2,
      sum_Nint_B2_B2, sum_Nint_B2_B3, sum_Nint_B3_B2, sum_Nint_B3_B3]
    norm_num
  have hu12C : ∀ x ∈ Cset, ⟪u12, w x⟫ = 0 := by
    intro x hx
    rw [hu12, inner_sub_left, hsum, hsum, sum_Nint_B1_C x hx, sum_Nint_B2_C x hx]
    norm_num
  have hu23C : ∀ x ∈ Cset, ⟪u23, w x⟫ = 0 := by
    intro x hx
    rw [hu23, inner_sub_left, hsum, hsum, sum_Nint_B2_C x hx, sum_Nint_B3_C x hx]
    norm_num
  have hu12b : ⟪u12, w 0⟫ = 576 := by
    rw [hu12, inner_sub_left, hsum, hsum, sum_Nint_B1_bstar, sum_Nint_B2_bstar]
    norm_num
  have hu23b : ⟪u23, w 0⟫ = 0 := by
    rw [hu23, inner_sub_left, hsum, hsum, sum_Nint_B2_bstar, sum_Nint_B3_bstar]
    norm_num
  -- the projected point `p` and its rescaling `μ • p`
  set p : EuclideanSpace ℝ (Fin 65) := w 0 - (48⁻¹ : ℝ) • u12 - (96⁻¹ : ℝ) • u23 with hp
  have hpz : ∀ z, ⟪p, z⟫ = ⟪w 0, z⟫ - 48⁻¹ * ⟪u12, z⟫ - 96⁻¹ * ⟪u23, z⟫ := fun z => by
    rw [hp, inner_sub_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left]
  have hzp : ∀ z, ⟪z, p⟫ = ⟪z, w 0⟫ - 48⁻¹ * ⟪z, u12⟫ - 96⁻¹ * ⟪z, u23⟫ := fun z => by
    rw [hp, inner_sub_right, inner_sub_right, real_inner_smul_right, real_inner_smul_right]
  have hu12p : ⟪u12, p⟫ = 0 := by rw [hzp, hu12b, g11, g12]; norm_num
  have hu23p : ⟪u23, p⟫ = 0 := by rw [hzp, hu23b, g21, g22]; norm_num
  have hpp : ⟪p, p⟫ = 78 := by
    rw [hpz, hu12p, hu23p, hzp, real_inner_comm u12 (w 0), hu12b,
      real_inner_comm u23 (w 0), hu23b, hinner 0 0, Nint_diag]
    norm_num
  have hpC : ∀ x ∈ Cset, ⟪p, w x⟫ = 6 * (Nint 0 x : ℝ) := by
    intro x hx
    rw [hpz, hu12C x hx, hu23C x hx, hinner 0 x]
    ring
  set μ : ℝ := (-1 + Real.sqrt 222) / 13 with hμ
  have hs222 : Real.sqrt 222 ^ 2 = 222 := Real.sq_sqrt (by norm_num)
  have hμquad : 78 * μ ^ 2 = 102 - 12 * μ := by
    rw [hμ]
    field_simp
    nlinarith [hs222]
  have hμpos : 0 < μ := by
    rw [hμ]
    have h1 : (1 : ℝ) < Real.sqrt 222 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have hμlt4 : μ < 4 := by
    rw [hμ]
    have h1 : Real.sqrt 222 < 53 := by
      rw [show (53 : ℝ) = Real.sqrt (53 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  set pstar : EuclideanSpace ℝ (Fin 65) := μ • p with hpstar
  have hCne0 : ∀ x ∈ Cset, x ≠ 0 := fun x hx h => bstar_notMem_Cset (h ▸ hx)
  -- squared distances from `μ • p` to the `C`-vectors
  have hdps : ∀ x ∈ Cset, ⟪pstar - w x, pstar - w x⟫ =
      78 * μ ^ 2 - 12 * μ * (Nint 0 x : ℝ) + 90 := by
    intro x hx
    rw [real_inner_sub_sub_self, hpstar, real_inner_smul_left, real_inner_smul_right,
      real_inner_smul_left, hpp, hpC x hx, hinner x x, Nint_diag]
    push_cast
    ring
  have hdist_pstar_far : ∀ x ∈ Cset, ¬ adj 0 x = true →
      dist pstar (w x) = Real.sqrt 192 := by
    intro x hx hnadj
    have hval : ⟪pstar - w x, pstar - w x⟫ = 192 := by
      rw [hdps x hx, Nint_of_not_adj (Ne.symm (hCne0 x hx)) hnadj]
      push_cast
      linarith [hμquad]
    rw [dist_eq_norm, norm_eq_sqrt_real_inner, hval]
  have hdist_pstar_near : ∀ x ∈ Cset, adj 0 x = true →
      dist pstar (w x) = Real.sqrt (192 - 48 * μ) := by
    intro x hx hadj
    have hval : ⟪pstar - w x, pstar - w x⟫ = 192 - 48 * μ := by
      rw [hdps x hx, Nint_of_adj hadj]
      push_cast
      linarith [hμquad]
    rw [dist_eq_norm, norm_eq_sqrt_real_inner, hval]
  have hnear_lt : Real.sqrt (192 - 48 * μ) < Real.sqrt 192 :=
    Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have hnear_pos : 0 < Real.sqrt (192 - 48 * μ) :=
    Real.sqrt_pos.mpr (by linarith)
  -- the 63-dimensional subspace
  have hindep : LinearIndependent ℝ ![u12, u23] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : ⟪u12, s • u12 + t • u23⟫ = 0 := by rw [hst, inner_zero_right]
    have h2 : ⟪u23, s • u12 + t • u23⟫ = 0 := by rw [hst, inner_zero_right]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, g11, g12] at h1
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, g21, g22] at h2
    constructor <;> linarith
  have hrankS : finrank ℝ (span ℝ ({u12, u23} : Set (EuclideanSpace ℝ (Fin 65)))) = 2 := by
    have h := finrank_span_eq_card hindep
    have hr : Set.range ![u12, u23] = ({u12, u23} : Set (EuclideanSpace ℝ (Fin 65))) := by
      ext z
      simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro (rfl | rfl) <;> simp
      · rintro (rfl | rfl) <;> simp
    rw [hr] at h
    simpa using h
  have hrankV : finrank ℝ (span ℝ ({u12, u23} : Set (EuclideanSpace ℝ (Fin 65))))ᗮ = 63 := by
    have h := Submodule.finrank_add_finrank_orthogonal
      (K := span ℝ ({u12, u23} : Set (EuclideanSpace ℝ (Fin 65))))
    rw [hrankS, finrank_euclideanSpace_fin] at h
    omega
  have hmemV : ∀ z, ⟪u12, z⟫ = 0 → ⟪u23, z⟫ = 0 →
      z ∈ (span ℝ ({u12, u23} : Set (EuclideanSpace ℝ (Fin 65))))ᗮ := by
    intro z h1 h2
    rw [Submodule.mem_orthogonal]
    intro v hv
    induction hv using Submodule.span_induction with
    | mem a ha =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact h1
      · exact h2
    | zero => rw [inner_zero_left]
    | add a b _ _ iha ihb => rw [inner_add_left, iha, ihb, add_zero]
    | smul r a _ iha => rw [real_inner_smul_left, iha, mul_zero]
  -- the 321-point family
  let eC := Cset.orderIsoOfFin Cset_card
  set t : Fin 321 → EuclideanSpace ℝ (Fin 65) := fun k =>
    if h : (k : ℕ) < 320 then w (eC ⟨(k : ℕ), h⟩) else pstar with ht
  have htC : ∀ (k : Fin 321) (h : (k : ℕ) < 320), t k = w (eC ⟨(k : ℕ), h⟩) :=
    fun k h => by rw [ht]; exact dif_pos h
  have htP : ∀ (k : Fin 321), ¬ (k : ℕ) < 320 → t k = pstar :=
    fun k h => by rw [ht]; exact dif_neg h
  have htmem : ∀ k, t k ∈ (span ℝ ({u12, u23} : Set (EuclideanSpace ℝ (Fin 65))))ᗮ := by
    intro k
    by_cases h : (k : ℕ) < 320
    · rw [htC k h]
      exact hmemV _ (hu12C _ (eC _).2) (hu23C _ (eC _).2)
    · rw [htP k h, hpstar]
      refine hmemV _ ?_ ?_ <;> rw [real_inner_smul_right]
      · rw [hu12p]; ring
      · rw [hu23p]; ring
  -- distance facts at the level of `t`
  have hCdichot : ∀ (ki kj : Fin 321) (hi : (ki : ℕ) < 320) (hj : (kj : ℕ) < 320),
      ki ≠ kj → dist (t ki) (t kj) = 12 ∨ dist (t ki) (t kj) = Real.sqrt 192 := by
    intro ki kj hi hj hne
    rw [htC ki hi, htC kj hj, hdist]
    have hxy : ((eC ⟨(ki : ℕ), hi⟩ : Fin 416)) ≠ (eC ⟨(kj : ℕ), hj⟩ : Fin 416) := by
      intro h
      have h2 := eC.injective (Subtype.coe_injective h)
      have h3 := congrArg Fin.val h2
      exact hne (Fin.ext h3)
    by_cases h : adj (eC ⟨(ki : ℕ), hi⟩ : Fin 416) (eC ⟨(kj : ℕ), hj⟩ : Fin 416) = true
    · exact Or.inl (dist_vRow_of_adj h)
    · exact Or.inr (dist_vRow_of_not_adj hxy h)
  have hPdichot : ∀ (ki kj : Fin 321) (hi : (ki : ℕ) < 320), ¬ (kj : ℕ) < 320 →
      dist (t ki) (t kj) = Real.sqrt (192 - 48 * μ) ∨
      dist (t ki) (t kj) = Real.sqrt 192 := by
    intro ki kj hi hj
    rw [htC ki hi, htP kj hj, dist_comm]
    by_cases h : adj 0 (eC ⟨(ki : ℕ), hi⟩ : Fin 416) = true
    · exact Or.inl (hdist_pstar_near _ (eC _).2 h)
    · exact Or.inr (hdist_pstar_far _ (eC _).2 h)
  have hlast : ∀ ki kj : Fin 321, ¬ (ki : ℕ) < 320 → ¬ (kj : ℕ) < 320 → ki = kj := by
    intro ki kj hi hj
    have h1 : (ki : ℕ) = 320 := by omega
    have h2 : (kj : ℕ) = 320 := by omega
    exact Fin.ext (h1.trans h2.symm)
  -- assemble via the dimension reduction
  obtain ⟨v, hv⟩ := exists_dist_preserving_of_mem t htmem hrankV
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  -- injectivity
  · intro ki kj heq
    by_contra hne
    have hd : dist (v ki) (v kj) = 0 := by rw [heq, dist_self]
    rw [hv] at hd
    by_cases hi : (ki : ℕ) < 320 <;> by_cases hj : (kj : ℕ) < 320
    · rcases hCdichot ki kj hi hj hne with h | h <;> rw [h] at hd
      · norm_num at hd
      · exact absurd hd (by positivity)
    · rcases hPdichot ki kj hi hj with h | h <;> rw [h] at hd
      · exact absurd hd (ne_of_gt hnear_pos)
      · exact absurd hd (by positivity)
    · rw [dist_comm] at hd
      rcases hPdichot kj ki hj hi with h | h <;> rw [h] at hd
      · exact absurd hd (ne_of_gt hnear_pos)
      · exact absurd hd (by positivity)
    · exact hne (hlast ki kj hi hj)
  -- all distances are at most √192
  · intro ki kj
    rw [hv]
    rcases eq_or_ne ki kj with rfl | hne
    · rw [dist_self]
      positivity
    by_cases hi : (ki : ℕ) < 320 <;> by_cases hj : (kj : ℕ) < 320
    · rcases hCdichot ki kj hi hj hne with h | h
      · exact h.trans_le twelve_le_sqrt192
      · exact le_of_eq h
    · rcases hPdichot ki kj hi hj with h | h
      · exact h.trans_le hnear_lt.le
      · exact le_of_eq h
    · rw [dist_comm]
      rcases hPdichot kj ki hj hi with h | h
      · exact h.trans_le hnear_lt.le
      · exact le_of_eq h
    · exact absurd (hlast ki kj hi hj) hne
  -- the diameter √192 is attained
  · obtain ⟨i, hi, j, hj, hij, hnadj⟩ := exists_nonadj_C
    obtain ⟨ki, hki⟩ : ∃ k : Fin 320, eC k = ⟨i, hi⟩ :=
      ⟨eC.symm ⟨i, hi⟩, eC.apply_symm_apply _⟩
    obtain ⟨kj, hkj⟩ : ∃ k : Fin 320, eC k = ⟨j, hj⟩ :=
      ⟨eC.symm ⟨j, hj⟩, eC.apply_symm_apply _⟩
    have h321 : (320 : ℕ) ≤ 321 := by norm_num
    refine ⟨ki.castLE h321, kj.castLE h321, ?_⟩
    have hti : t (ki.castLE h321) = w i := by
      rw [htC (ki.castLE h321) ki.isLt]
      congr 1
      rw [show (⟨((ki.castLE h321 : Fin 321) : ℕ), ki.isLt⟩ : Fin 320) = ki from
        Fin.ext rfl, hki]
    have htj : t (kj.castLE h321) = w j := by
      rw [htC (kj.castLE h321) kj.isLt]
      congr 1
      rw [show (⟨((kj.castLE h321 : Fin 321) : ℕ), kj.isLt⟩ : Fin 320) = kj from
        Fin.ext rfl, hkj]
    rw [hv, hti, htj, hdist]
    exact dist_vRow_of_not_adj hij (by simp [hnadj])
  -- the clique bound
  · intro s hs
    have hs' : ∀ ki ∈ s, ∀ kj ∈ s, dist (t ki) (t kj) < Real.sqrt 192 := by
      intro ki hki kj hkj
      rw [← hv ki kj]
      exact hs ki hki kj hkj
    -- map the indices to graph vertices: `C`-indices to their vertex, the last to `0`
    set f : Fin 321 → Fin 416 := fun k =>
      if h : (k : ℕ) < 320 then (eC ⟨(k : ℕ), h⟩ : Fin 416) else 0 with hf
    have hfC : ∀ (k : Fin 321) (h : (k : ℕ) < 320), f k = (eC ⟨(k : ℕ), h⟩ : Fin 416) :=
      fun k h => by rw [hf]; exact dif_pos h
    have hfP : ∀ (k : Fin 321), ¬ (k : ℕ) < 320 → f k = 0 :=
      fun k h => by rw [hf]; exact dif_neg h
    have hfinj : Function.Injective f := by
      intro ki kj h
      by_cases hi : (ki : ℕ) < 320 <;> by_cases hj : (kj : ℕ) < 320
      · rw [hfC ki hi, hfC kj hj] at h
        have h2 := eC.injective (Subtype.coe_injective h)
        have h3 := congrArg Fin.val h2
        exact Fin.ext h3
      · rw [hfC ki hi, hfP kj hj] at h
        exact absurd (h ▸ (eC _).2) bstar_notMem_Cset
      · rw [hfP ki hi, hfC kj hj] at h
        exact absurd (h.symm ▸ (eC _).2) bstar_notMem_Cset
      · exact hlast ki kj hi hj
    have himg : (s.image f).card = s.card := Finset.card_image_of_injective s hfinj
    rw [← himg]
    refine clique_card_le_five _ ?_
    intro a ha b hb hab
    obtain ⟨ka, hka, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨kb, hkb, rfl⟩ := Finset.mem_image.mp hb
    have hkab : ka ≠ kb := fun h => hab (by rw [h])
    have hdlt := hs' ka hka kb hkb
    by_cases hi : (ka : ℕ) < 320 <;> by_cases hj : (kb : ℕ) < 320
    · rw [hfC ka hi, hfC kb hj]
      rw [htC ka hi, htC kb hj, hdist] at hdlt
      by_contra h
      have hxy : ((eC ⟨(ka : ℕ), hi⟩ : Fin 416)) ≠ (eC ⟨(kb : ℕ), hj⟩ : Fin 416) := by
        rw [hfC ka hi, hfC kb hj] at hab
        exact hab
      rw [dist_vRow_of_not_adj hxy h] at hdlt
      exact lt_irrefl _ hdlt
    · rw [hfC ka hi, hfP kb hj]
      rw [htC ka hi, htP kb hj, dist_comm] at hdlt
      by_contra h
      rw [adj_symm] at h
      rw [hdist_pstar_far _ (eC _).2 h] at hdlt
      exact lt_irrefl _ hdlt
    · rw [hfP ka hi, hfC kb hj]
      rw [htP ka hi, htC kb hj] at hdlt
      by_contra h
      rw [hdist_pstar_far _ (eC _).2 h] at hdlt
      exact lt_irrefl _ hdlt
    · exact absurd (hlast ka kb hi hj) hkab

end G2Four

end Borsuk
