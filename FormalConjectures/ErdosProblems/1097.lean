/-
Copyright 2025 The Formal Conjectures Authors.

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
import FormalConjectures.Util.ProblemImports
import FormalConjectures.Counterexample

/-!
# Erdős Problem 1097

*Reference:* [erdosproblems.com/1097](https://www.erdosproblems.com/1097)
-/

namespace Erdos1097

/--
Given a finite set of integers `A` (modelled as a `Finset ℤ`), the set
`CommonDifferencesThreeTermAP A` consists of all integers `d` such that there
is a non-trivial three-term arithmetic progression `a, b, c ∈ A` with
`b - a = d` and `c - b = d`.
-/
def CommonDifferencesThreeTermAP (A : Finset ℤ) : Set ℤ :=
  {d : ℤ | d ≠ 0 ∧ ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, b - a = d ∧ c - b = d}

/--
A weaker bound has been proven: there are always at most $n^2$ such values of $d$.
-/
@[category textbook, AMS 11]
theorem erdos_1097.variants.weaker :
    ∀ A, (CommonDifferencesThreeTermAP A).ncard ≤ A.card ^ 2 := by
  /-
  Proof outline:
  We want to show that the number of common differences is at most $|A|^2$.
  Let $S$ be the set of all differences $b - a$ for $a, b \in A$.
  The set of common differences of 3-term APs in $A$ is a subset of $S$.
  The size of $S$ is at most the number of pairs $(a, b) \in A \times A$, which is $|A|^2$.
  Therefore, the number of common differences is at most $|A|^2$.
  -/
  intro A
  let S := (A ×ˢ A).image (fun (a, b) => b - a)
  have h1 : CommonDifferencesThreeTermAP A ⊆ (S : Set ℤ) := by
    intro d hd
    rcases hd with ⟨_, a, ha, b, hb, _, _, hba, _⟩
    rw [Finset.mem_coe, Finset.mem_image]
    exact ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, hba⟩
  have h2 : S.card ≤ A.card ^ 2 := by
    calc
      S.card ≤ (A ×ˢ A).card := Finset.card_image_le
      _ = A.card * A.card := Finset.card_product A A
      _ = A.card ^ 2 := by ring
  have h3 : (CommonDifferencesThreeTermAP A).ncard ≤ S.card := by
    have h_ncard : (S : Set ℤ).ncard = S.card := Set.ncard_coe_finset S
    rw [← h_ncard]
    have hfin : (S : Set ℤ).Finite := Finset.finite_toSet S
    exact Set.ncard_le_ncard h1 hfin
  exact le_trans h3 h2

open Filter Topology

/--
A trivial lower bound: for sufficiently large `n` there exist sets $A$ with $|A| = n$ that contain at least $\Omega(n)$
distinct common differences of three-term arithmetic progressions.
-/
@[category textbook, AMS 11]
theorem erdos_1097.variants.lower_bound : ∃ c > (0 : ℝ), ∀ᶠ n in Filter.atTop, ∃ (A : Finset ℤ),
    A.card = n ∧ c * (n : ℝ) ≤ (CommonDifferencesThreeTermAP A).ncard := by
  /-
  Proof outline:
  Let $c = 1/4$. For $n \ge 4$, let $A = \{1, \dots, n\}$.
  The set of common differences of 3-term APs in $A$ contains $S = \{1, \dots, \lfloor (n-1)/2 \rfloor\}$.
  The size of $S$ is $\lfloor (n-1)/2 \rfloor$, which is at least $n/4$ for $n \ge 4$.
  -/
  use 1 / 4
  constructor
  · norm_num
  · filter_upwards [Ici_mem_atTop 4] with n hn
    rw [Set.mem_Ici] at hn
    use Finset.Icc 1 (n : ℤ)
    constructor
    · rw [Int.card_Icc]
      have : (1 : ℤ) ≤ n := by omega
      zify [this]
      omega
    · let S := Finset.Icc 1 (((n : ℤ) - 1) / 2)
      have hS : (S : Set ℤ) ⊆ CommonDifferencesThreeTermAP (Finset.Icc 1 (n : ℤ)) := by
        intro d hd
        rw [Finset.mem_coe, Finset.mem_Icc] at hd
        have hd0 : d ≠ 0 := by omega
        refine ⟨hd0, 1, ?_, 1 + d, ?_, 1 + 2 * d, ?_, ?_, ?_⟩
        · rw [Finset.mem_Icc]; omega
        · rw [Finset.mem_Icc]; omega
        · rw [Finset.mem_Icc]; omega
        · ring
        · ring
      have hcard : S.card = Int.toNat (((n : ℤ) - 1) / 2) := by
        rw [Int.card_Icc]
        omega
      have hcard2 : (S : Set ℤ).ncard = S.card := Set.ncard_coe_finset S
      have hfin : (CommonDifferencesThreeTermAP (Finset.Icc 1 (n : ℤ))).Finite := by
        have hsub : CommonDifferencesThreeTermAP (Finset.Icc 1 (n : ℤ)) ⊆ ((Finset.Icc 1 (n : ℤ)) ×ˢ (Finset.Icc 1 (n : ℤ))).image (fun (a, b) => b - a) := by
          intro d hd
          rcases hd with ⟨_, a, ha, b, hb, _, _, hba, _⟩
          rw [Finset.mem_coe, Finset.mem_image]
          exact ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, hba⟩
        exact Set.Finite.subset (Finset.finite_toSet _) hsub
      have hle : (S : Set ℤ).ncard ≤ (CommonDifferencesThreeTermAP (Finset.Icc 1 (n : ℤ))).ncard := by
        apply Set.ncard_le_ncard hS hfin
      rw [hcard2, hcard] at hle
      have h_ineq : (1 / 4 : ℝ) * (n : ℝ) ≤ (Int.toNat (((n : ℤ) - 1) / 2) : ℝ) := by
        have h0 : 0 ≤ ((n : ℤ) - 1) / 2 := by omega
        have h2_int : (Int.toNat (((n : ℤ) - 1) / 2) : ℤ) = (((n : ℤ) - 1) / 2) := Int.toNat_of_nonneg h0
        have h2 : (Int.toNat (((n : ℤ) - 1) / 2) : ℝ) = ((((n : ℤ) - 1) / 2 : ℤ) : ℝ) := by
          calc (Int.toNat (((n : ℤ) - 1) / 2) : ℝ) = ((Int.toNat (((n : ℤ) - 1) / 2) : ℤ) : ℝ) := by push_cast; rfl
          _ = ((((n : ℤ) - 1) / 2) : ℤ) := by rw [h2_int]
        rw [h2]
        have h3 : (n : ℤ) - 2 ≤ 2 * (((n : ℤ) - 1) / 2) := by omega
        have h4 : ((n : ℝ) - 2) ≤ 2 * ((((n : ℤ) - 1) / 2 : ℤ) : ℝ) := by
          have h3_cast : ((n : ℤ) - 2 : ℝ) ≤ (2 * (((n : ℤ) - 1) / 2) : ℤ) := by exact_mod_cast h3
          push_cast at h3_cast
          exact h3_cast
        have hn_real : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      exact le_trans h_ineq (by exact_mod_cast hle)

end Erdos1097

namespace Erdos1097

/--
For any function $d \in D\_funs$, there exist functions $a, c \in X\_funs$ and $b \in Y\_funs$
such that $b - a = d$ and $c - b = d$.
-/
@[category API, AMS 11]
lemma diffs_exist (M : ℕ) (d : Fin M → ℤ) (hd : d ∈ D_funs M) :
  ∃ a ∈ X_funs M, ∃ b ∈ Y_funs M, ∃ c ∈ X_funs M, b - a = d ∧ c - b = d := by
  /-
  Proof outline:
  We construct the functions $a, b, c$ pointwise.
  For each index $i$, $d(i) \in \{-1, 0, 1\}$.
  If $d(i) = 1$, we set $a(i) = 0, b(i) = 1, c(i) = 2$.
  If $d(i) = 0$, we set $a(i) = 2, b(i) = 2, c(i) = 2$.
  If $d(i) = -1$, we set $a(i) = 2, b(i) = 1, c(i) = 0$.
  By definition, $a, c \in X\_funs$ and $b \in Y\_funs$, and they satisfy $b - a = d$ and $c - b = d$.
  -/
  use fun i => if d i = 1 then 0 else 2
  have ha : (fun i => if d i = 1 then (0 : ℤ) else 2) ∈ X_funs M := by
    unfold X_funs
    rw [Fintype.mem_piFinset]
    intro i
    split_ifs <;> simp
  use ha
  use fun i => if d i = 0 then 2 else 1
  have hb : (fun i => if d i = 0 then (2 : ℤ) else 1) ∈ Y_funs M := by
    unfold Y_funs
    rw [Fintype.mem_piFinset]
    intro i
    split_ifs <;> simp
  use hb
  use fun i => if d i = -1 then 0 else 2
  have hc : (fun i => if d i = -1 then (0 : ℤ) else 2) ∈ X_funs M := by
    unfold X_funs
    rw [Fintype.mem_piFinset]
    intro i
    split_ifs <;> simp
  use hc
  constructor
  · ext i
    simp only [Pi.sub_apply]
    have hdi : d i ∈ ({-1, 0, 1} : Finset ℤ) := by
      unfold D_funs at hd
      exact Fintype.mem_piFinset.mp hd i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdi
    rcases hdi with hdi | hdi | hdi <;> simp [hdi]
  · ext i
    simp only [Pi.sub_apply]
    have hdi : d i ∈ ({-1, 0, 1} : Finset ℤ) := by
      unfold D_funs at hd
      exact Fintype.mem_piFinset.mp hd i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdi
    rcases hdi with hdi | hdi | hdi <;> simp [hdi]

/--
The number of common differences of three-term arithmetic progressions in $A_M$ is at least $3^M - 1$.
-/
@[category API, AMS 11]
lemma card_diffs_A_M (M : ℕ) : 3^M - 1 ≤ (CommonDifferencesThreeTermAP (A_M M)).ncard := by
  /-
  Proof outline:
  Let $D_M$ be the image of $D\_funs$ under `eval_fun`.
  By `diffs_exist`, every non-zero element of $D_M$ is a common difference of a 3-term AP in $A_M$.
  The size of $D\_funs$ is $3^M$.
  Since `eval_fun` is injective on $D\_funs$ (by `eval_fun_inj_D`), the size of $D_M$ is $3^M$.
  Excluding $0$, there are at least $3^M - 1$ distinct non-zero common differences.
  -/
  let D_M := (D_funs M).image (eval_fun M)
  have h_sub : ((D_M \ {0} : Finset ℤ) : Set ℤ) ⊆ CommonDifferencesThreeTermAP (A_M M) := by
    intro d hd
    rw [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_singleton] at hd
    rcases hd with ⟨hd_in, hd_neq⟩
    rw [Finset.mem_image] at hd_in
    rcases hd_in with ⟨d_fun, hd_fun, hd_eq⟩
    rw [CommonDifferencesThreeTermAP, Set.mem_setOf_eq]
    constructor
    · exact hd_neq
    · have h_exist := diffs_exist M d_fun hd_fun
      rcases h_exist with ⟨a_fun, ha, b_fun, hb, c_fun, hc, hba, hcb⟩
      use eval_fun M a_fun
      constructor
      · unfold A_M
        rw [Finset.mem_union]
        left
        unfold X_M
        rw [Finset.mem_image]
        exact ⟨a_fun, ha, rfl⟩
      · use eval_fun M b_fun
        constructor
        · unfold A_M
          rw [Finset.mem_union]
          right
          unfold Y_M
          rw [Finset.mem_image]
          exact ⟨b_fun, hb, rfl⟩
        · use eval_fun M c_fun
          constructor
          · unfold A_M
            rw [Finset.mem_union]
            left
            unfold X_M
            rw [Finset.mem_image]
            exact ⟨c_fun, hc, rfl⟩
          · constructor
            · rw [← hd_eq, ← hba]
              unfold eval_fun
              rw [← Finset.sum_sub_distrib]
              congr 1
              ext i
              simp only [Pi.sub_apply]
              ring
            · rw [← hd_eq, ← hcb]
              unfold eval_fun
              rw [← Finset.sum_sub_distrib]
              congr 1
              ext i
              simp only [Pi.sub_apply]
              ring
  have h_card_D_funs : (D_funs M).card = 3^M := by
    unfold D_funs
    rw [Fintype.card_piFinset]
    have : ∏ i : Fin M, ({-1, 0, 1} : Finset ℤ).card = 3^M := by
      have : ({-1, 0, 1} : Finset ℤ).card = 3 := rfl
      simp [this]
    exact this
  have h_inj : ∀ x ∈ D_funs M, ∀ y ∈ D_funs M, eval_fun M x = eval_fun M y → x = y := by
    intro x hx y hy h_eq
    apply eval_fun_inj_D x y _ _ h_eq
    · intro i
      have := Fintype.mem_piFinset.mp hx i
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h <;> simp [h]
    · intro i
      have := Fintype.mem_piFinset.mp hy i
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h | h <;> simp [h]
  have h_card_D_M : D_M.card = 3^M := by
    rw [← h_card_D_funs]
    apply Finset.card_image_of_injOn
    exact h_inj
  have h_card_diff : (D_M \ {0}).card ≥ 3^M - 1 := by
    have h1 : (D_M \ {0}).card + (D_M ∩ {0}).card = D_M.card := Finset.card_sdiff_add_card_inter D_M {0}
    have h2 : (D_M ∩ {0}).card ≤ 1 := by
      have : (D_M ∩ {0}) ⊆ {0} := Finset.inter_subset_right
      have h3 := Finset.card_le_card this
      have h4 : ({0} : Finset ℤ).card = 1 := Finset.card_singleton 0
      omega
    omega
  have h_ncard : ((D_M \ {0} : Finset ℤ) : Set ℤ).ncard = (D_M \ {0}).card := Set.ncard_coe_finset _
  have h_fin : (CommonDifferencesThreeTermAP (A_M M)).Finite := by
    have hsub : CommonDifferencesThreeTermAP (A_M M) ⊆ ((A_M M) ×ˢ (A_M M)).image (fun (a, b) => b - a) := by
      intro d hd
      rcases hd with ⟨_, a, ha, b, hb, _, _, hba, _⟩
      rw [Finset.mem_coe, Finset.mem_image]
      exact ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, hba⟩
    exact Set.Finite.subset (Finset.finite_toSet _) hsub
  have h_le : ((D_M \ {0} : Finset ℤ) : Set ℤ).ncard ≤ (CommonDifferencesThreeTermAP (A_M M)).ncard := by
    apply Set.ncard_le_ncard h_sub h_fin
  rw [h_ncard] at h_le
  omega


/--
The main conjecture: for any finite set of integers $A$ with $|A| = n$, the number of distinct
common differences in three-term arithmetic progressions is $O(n^{3/2})$.
-/
@[category research solved, AMS 11]
theorem erdos_1097 : answer(False) ↔ ∃ C > (0 : ℝ), ∀ (A : Finset ℤ),
    (CommonDifferencesThreeTermAP A).ncard ≤ C * (A.card : ℝ) ^ (3 / 2 : ℝ) := by
  /-
  Proof outline:
  We prove that the conjecture is false by contradiction.
  Suppose there exists such a constant $C > 0$.
  By `card_A_M` and `card_diffs_A_M`, for any $M$, there is a set $A_M$ of size at most $2^{M+1}$
  with at least $3^M - 1$ common differences.
  This would imply $3^M - 1 \le C (2^{M+1})^{3/2}$.
  However, $3 > 2^{3/2} = 2 \sqrt{2}$, so $3^M$ grows strictly faster than $(2^{3/2})^M$.
  For sufficiently large $M$, this inequality must be violated, which is a contradiction.
  -/
  constructor
  · intro h
    exfalso
    exact h
  · intro h
    rcases h with ⟨C, hC, h_bound⟩
    have h_eventual : ∀ᶠ M in Filter.atTop, 0 < ((3^M - 1 : ℕ) : ℝ) - C * (2^(M+1) : ℝ)^(3/2 : ℝ) := by
      have h_r : (2 : ℝ)^(3/2 : ℝ) / 3 < 1 := by
        rw [div_lt_iff₀ (by norm_num)]
        have h1 : (2 : ℝ)^(3/2 : ℝ) = ((2 : ℝ)^(3 : ℝ))^(1/2 : ℝ) := by
          have : (3/2 : ℝ) = (3 : ℝ) * (1/2 : ℝ) := by ring
          rw [this]
          rw [Real.rpow_mul (by norm_num)]
        rw [h1]
        have h2 : (2 : ℝ)^(3 : ℝ) = 8 := by norm_num
        rw [h2]
        rw [← Real.sqrt_eq_rpow]
        rw [Real.sqrt_lt (by norm_num) (by norm_num)]
        norm_num
      have h_tendsto1 : Filter.Tendsto (fun M : ℕ => ((2 : ℝ)^(3/2 : ℝ) / 3)^M) Filter.atTop (nhds 0) := by
        apply tendsto_pow_atTop_nhds_zero_of_lt_one
        · positivity
        · exact h_r
      have h_tendsto2 : Filter.Tendsto (fun M : ℕ => C * (2 : ℝ)^(3/2 : ℝ) * ((2 : ℝ)^(3/2 : ℝ) / 3)^M) Filter.atTop (nhds 0) := by
        have : (0 : ℝ) = C * (2 : ℝ)^(3/2 : ℝ) * 0 := by ring
        rw [this]
        exact Filter.Tendsto.const_mul _ h_tendsto1
      have h_tendsto3 : Filter.Tendsto (fun M : ℕ => (1 / 3 : ℝ)^M) Filter.atTop (nhds 0) := by
        apply tendsto_pow_atTop_nhds_zero_of_lt_one
        · positivity
        · norm_num
      have h_tendsto4 : Filter.Tendsto (fun M : ℕ => C * (2 : ℝ)^(3/2 : ℝ) * ((2 : ℝ)^(3/2 : ℝ) / 3)^M + (1 / 3 : ℝ)^M) Filter.atTop (nhds 0) := by
        have : (0 : ℝ) = 0 + 0 := by ring
        rw [this]
        exact Filter.Tendsto.add h_tendsto2 h_tendsto3
      have h_eventual : ∀ᶠ M in Filter.atTop, C * (2 : ℝ)^(3/2 : ℝ) * ((2 : ℝ)^(3/2 : ℝ) / 3)^M + (1 / 3 : ℝ)^M < 1 := by
        apply (tendsto_order.mp h_tendsto4).2 1
        norm_num
      filter_upwards [h_eventual, Filter.Ici_mem_atTop 1] with M hM hM1
      rw [Set.mem_Ici] at hM1
      have h_3M_pos : (0 : ℝ) < (3 : ℝ)^M := by positivity
      have h_mul := mul_lt_mul_of_pos_right hM h_3M_pos
      have h_distrib : (C * (2 : ℝ)^(3/2 : ℝ) * ((2 : ℝ)^(3/2 : ℝ) / 3)^M + (1 / 3 : ℝ)^M) * (3 : ℝ)^M = C * (2 : ℝ)^(3/2 : ℝ) * ((2 : ℝ)^(3/2 : ℝ))^M + 1 := by
        rw [add_mul]
        congr 1
        · rw [div_pow, mul_assoc, div_mul_cancel₀ _ (ne_of_gt h_3M_pos)]
        · rw [one_div, inv_pow, inv_mul_cancel₀ (ne_of_gt h_3M_pos)]
      rw [h_distrib] at h_mul
      have h_2M : C * (2 : ℝ)^(3/2 : ℝ) * ((2 : ℝ)^(3/2 : ℝ))^M = C * (2^(M+1) : ℝ)^(3/2 : ℝ) := by
        have h_pow1 : ((2 : ℝ)^(3/2 : ℝ))^M = (2 : ℝ)^((3/2 : ℝ) * M) := by
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul (by norm_num)]
        rw [h_pow1]
        have h_pow2 : (2 : ℝ)^(3/2 : ℝ) * (2 : ℝ)^((3/2 : ℝ) * M) = (2 : ℝ)^((3/2 : ℝ) + (3/2 : ℝ) * M) := by
          rw [← Real.rpow_add (by norm_num)]
        have h_pow3 : (2^(M+1) : ℝ) = (2 : ℝ)^((M:ℝ)+1) := by
          norm_cast
        rw [h_pow3]
        have h_pow4 : ((2 : ℝ)^((M:ℝ)+1))^(3/2 : ℝ) = (2 : ℝ)^(((M:ℝ)+1) * (3/2 : ℝ)) := by
          rw [← Real.rpow_mul (by norm_num)]
        rw [h_pow4]
        rw [mul_assoc]
        congr 1
        rw [h_pow2]
        congr 1
        ring
      rw [h_2M] at h_mul
      have h_cast : ((3^M - 1 : ℕ) : ℝ) = (3 : ℝ)^M - 1 := by
        rw [Nat.cast_sub]
        · norm_cast
        · have : 1 ≤ 3^M := by
            calc 1 = 3^0 := by rfl
            _ ≤ 3^M := Nat.pow_le_pow_right (by omega) (by omega)
          exact this
      rw [h_cast]
      linarith
    rcases Filter.eventually_atTop.mp h_eventual with ⟨M, hM⟩
    have hM_pos := hM M (le_refl M)
    have h_A_M := h_bound (A_M M)
    have h1 : ((3^M - 1 : ℕ) : ℝ) ≤ (CommonDifferencesThreeTermAP (A_M M)).ncard := by
      exact_mod_cast card_diffs_A_M M
    have h2 : (A_M M).card ≤ 2^(M+1) := card_A_M M
    have h3 : ((A_M M).card : ℝ) ≤ (2^(M+1) : ℝ) := by exact_mod_cast h2
    have h4 : ((A_M M).card : ℝ)^(3/2 : ℝ) ≤ (2^(M+1) : ℝ)^(3/2 : ℝ) := by
      apply Real.rpow_le_rpow
      · exact Nat.cast_nonneg _
      · exact h3
      · norm_num
    have h5 : C * ((A_M M).card : ℝ)^(3/2 : ℝ) ≤ C * (2^(M+1) : ℝ)^(3/2 : ℝ) := by
      apply mul_le_mul_of_nonneg_left h4 (le_of_lt hC)
    linarith

--TODO(firsching): add Bourgain reformulation and question and known results around optimal exponents.

end Erdos1097
