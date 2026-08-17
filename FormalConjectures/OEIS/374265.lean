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
# Minimized zeroless factorials

$a(n)$ is the smallest positive integer obtained by greedily dividing out factors from $n!$
to avoid the digit zero.

*References:*
- [A374265](https://oeis.org/A374265)
-/
open Nat Finset

namespace OeisA374265


-- The function that removes all '0' digits from a number
def remove_zeros (n : ℕ) : ℕ :=
  -- Nat.digits returns the list of digits in reverse order.
  let digits := (Nat.digits 10 n).filter (fun d => d ≠ 0)
  -- Nat.ofDigits interprets the list from most significant digit first if the base is 10
  ofDigits 10 digits

/--
The set of all possible values $f(n)$ resulting from a sequence of choices
where $f(0)=1$ and $f(i) = \operatorname{OpNoz}_i(i \cdot f(i-1))$,
with $\operatorname{OpNoz}_i(x)$ being either $x$ or $remove\_zeros(x)$.
We use `biUnion` for the union of sets.
-/
def reachable_zeroless_factorials : ℕ → Finset ℕ
  | 0 => {1}
  | n + 1 =>
    let prev_set := reachable_zeroless_factorials n
    prev_set.biUnion fun m =>
      let prod := (n + 1) * m
      {prod, remove_zeros prod}

-- The set of reachable values is always nonempty.
@[category API, AMS 11]
lemma reachable_nonempty (n : ℕ) : (reachable_zeroless_factorials n).Nonempty := by
  induction n with
  | zero => exact Finset.singleton_nonempty 1
  | succ n ih =>
    rcases ih with ⟨m, hm⟩ -- Get a guaranteed element m from the previous set
    let prod := (n + 1) * m
    -- We show that `prod` is an element of the current set using `mem_biUnion`.
    -- prod is in {prod, ...} and m is in the previous set, so prod is in the overall union.
    exact ⟨prod, Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_insert_self prod _⟩⟩

/--
The minimized zeroless factorial function $a(n)$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (reachable_zeroless_factorials n).min' (reachable_nonempty n)

@[category API, AMS 11]
lemma singleton_min' (x : ℕ) (s : Finset ℕ) (h : s = {x}) (hn : s.Nonempty) : s.min' hn = x := by
  have hmem : x ∈ s := by rw [h]; exact Finset.mem_singleton_self x
  have hle : ∀ y ∈ s, x ≤ y := by
    intro y hy
    rw [h, Finset.mem_singleton] at hy
    rw [hy]
  exact le_antisymm (Finset.min'_le s x hmem) (Finset.le_min' s hn x hle)

@[category API, AMS 11]
lemma digits_lt_10 {n : ℕ} (h : n < 10) (hn : 0 < n) : Nat.digits 10 n = [n] := by
  rw [Nat.digits_def' (by decide : (1 : ℕ) < 10) hn, show n / 10 = 0 from Nat.div_eq_of_lt h,
      Nat.digits_zero]
  rw [Nat.mod_eq_of_lt h]

@[category API, AMS 11]
lemma digits_24 : Nat.digits 10 24 = [4, 2] := by
  rw [Nat.digits_def' (by decide : (1 : ℕ) < 10) (by decide), show 24 / 10 = 2 by rfl]
  rw [digits_lt_10 (by decide) (by decide)]

@[category API, AMS 11]
lemma remove_zeros_1 : remove_zeros 1 = 1 := by
  unfold remove_zeros
  rw [digits_lt_10 (by decide) (by decide)]
  rfl

@[category API, AMS 11]
lemma remove_zeros_2 : remove_zeros 2 = 2 := by
  unfold remove_zeros
  rw [digits_lt_10 (by decide) (by decide)]
  rfl

@[category API, AMS 11]
lemma remove_zeros_6 : remove_zeros 6 = 6 := by
  unfold remove_zeros
  rw [digits_lt_10 (by decide) (by decide)]
  rfl

@[category API, AMS 11]
lemma remove_zeros_24 : remove_zeros 24 = 24 := by
  unfold remove_zeros
  rw [digits_24]
  rfl

@[category API, AMS 11]
lemma reachable_0 : reachable_zeroless_factorials 0 = {1} := rfl

@[category API, AMS 11]
lemma reachable_1 : reachable_zeroless_factorials 1 = {1} := by
  change ({1} : Finset ℕ).biUnion (fun m => {1 * m, remove_zeros (1 * m)}) = {1}
  rw [Finset.singleton_biUnion]
  rw [show 1 * 1 = 1 by rfl, remove_zeros_1]
  exact Finset.pair_eq_singleton 1

@[category API, AMS 11]
lemma reachable_2 : reachable_zeroless_factorials 2 = {2} := by
  change (reachable_zeroless_factorials 1).biUnion (fun m => {2 * m, remove_zeros (2 * m)}) = {2}
  rw [reachable_1, Finset.singleton_biUnion]
  rw [show 2 * 1 = 2 by rfl, remove_zeros_2]
  exact Finset.pair_eq_singleton 2

@[category API, AMS 11]
lemma reachable_3 : reachable_zeroless_factorials 3 = {6} := by
  change (reachable_zeroless_factorials 2).biUnion (fun m => {3 * m, remove_zeros (3 * m)}) = {6}
  rw [reachable_2, Finset.singleton_biUnion]
  rw [show 3 * 2 = 6 by rfl, remove_zeros_6]
  exact Finset.pair_eq_singleton 6

@[category API, AMS 11]
lemma reachable_4 : reachable_zeroless_factorials 4 = {24} := by
  change (reachable_zeroless_factorials 3).biUnion (fun m => {4 * m, remove_zeros (4 * m)}) = {24}
  rw [reachable_3, Finset.singleton_biUnion]
  rw [show 4 * 6 = 24 by rfl, remove_zeros_24]
  exact Finset.pair_eq_singleton 24

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := singleton_min' 1 _ reachable_0 _

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := singleton_min' 1 _ reachable_1 _

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := singleton_min' 2 _ reachable_2 _

@[category test, AMS 11]
theorem a_3 : a 3 = 6 := singleton_min' 6 _ reachable_3 _

@[category test, AMS 11]
theorem a_4 : a 4 = 24 := singleton_min' 24 _ reachable_4 _

/-- Base-10 digit sum. -/
def D (n : ℕ) : ℕ := (Nat.digits 10 n).sum

@[category API, AMS 11]
lemma D_zero : D 0 = 0 := by simp [D]

@[category API, AMS 11]
lemma sum_filter_ne_zero (l : List ℕ) :
    (l.filter (fun d => d ≠ 0)).sum = l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    by_cases h : a = 0
    · subst h
      rw [List.filter_cons_of_neg (by simp), ih, List.sum_cons, Nat.zero_add]
    · rw [List.filter_cons_of_pos (by simpa using h), List.sum_cons, List.sum_cons, ih]

@[category API, AMS 11]
lemma D_remove (x : ℕ) : D (remove_zeros x) = D x := by
  unfold D remove_zeros
  have w1 : ∀ l ∈ (Nat.digits 10 x).filter (fun d => d ≠ 0), l < 10 := by
    intro l hl
    have := List.mem_of_mem_filter hl
    exact Nat.digits_lt_base (by norm_num) this
  have w2 : ∀ (h : (Nat.digits 10 x).filter (fun d => d ≠ 0) ≠ []),
      ((Nat.digits 10 x).filter (fun d => d ≠ 0)).getLast h ≠ 0 := by
    intro h
    have hmem := List.getLast_mem h
    have := (List.mem_filter.mp hmem).2
    simpa using this
  rw [Nat.digits_ofDigits 10 (by norm_num) _ w1 w2]
  exact sum_filter_ne_zero _

@[category API, AMS 11]
lemma D_pos_of_pos {x : ℕ} (hx : 0 < x) : 0 < D x := by
  unfold D
  have hne : Nat.digits 10 x ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hx.ne'
  have hlast : (Nat.digits 10 x).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero 10 hx.ne'
  have hmem := List.getLast_mem hne
  have hle : (Nat.digits 10 x).getLast hne ≤ (Nat.digits 10 x).sum :=
    List.single_le_sum (by intro y _; exact Nat.zero_le y) _ hmem
  omega

@[category API, AMS 11]
lemma pos_of_D_pos {x : ℕ} (hD : 0 < D x) : 0 < x := by
  by_contra h0
  push_neg at h0
  have : x = 0 := by omega
  subst this
  simp [D] at hD

@[category API, AMS 11]
lemma remove_zeros_pos {x : ℕ} (hx : 0 < x) : 0 < remove_zeros x := by
  apply pos_of_D_pos
  rw [D_remove]
  exact D_pos_of_pos hx

@[category API, AMS 11]
lemma reachable_pos (n : ℕ) : ∀ v ∈ reachable_zeroless_factorials n, 0 < v := by
  induction n with
  | zero =>
    intro v hv
    rw [reachable_zeroless_factorials, Finset.mem_singleton] at hv
    subst hv
    decide
  | succ n ih =>
    intro v hv
    rw [reachable_zeroless_factorials] at hv
    simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hv
    obtain ⟨u, hu, rcases⟩ := hv
    have hupos := ih u hu
    have hprodpos : 0 < (n + 1) * u := Nat.mul_pos (by omega) hupos
    rcases rcases with rfl | rfl
    · exact hprodpos
    · exact remove_zeros_pos hprodpos

@[category API, AMS 11]
lemma D_add_le : ∀ N a b, a + b = N → D N ≤ D a + D b := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro a b hab
    rcases Nat.eq_zero_or_pos a with ha0 | ha
    · subst ha0; simp_all [D]
    rcases Nat.eq_zero_or_pos b with hb0 | hb
    · subst hb0; simp_all [D]
    have hN : 0 < N := by omega
    have hDN : D N = N % 10 + D (N / 10) := by
      unfold D; rw [Nat.digits_def' (by norm_num) hN]; simp
    have hDa : D a = a % 10 + D (a / 10) := by
      unfold D; rw [Nat.digits_def' (by norm_num) ha]; simp
    have hDb : D b = b % 10 + D (b / 10) := by
      unfold D; rw [Nat.digits_def' (by norm_num) hb]; simp
    set c := (a % 10 + b % 10) / 10 with hc
    have hNdiv : N / 10 = a / 10 + (b / 10 + c) := by subst hab; omega
    have hlt1 : N / 10 < N := Nat.div_lt_self hN (by norm_num)
    have e1 : D (N / 10) ≤ D (a / 10) + D (b / 10 + c) :=
      IH (N / 10) hlt1 (a / 10) (b / 10 + c) hNdiv.symm
    have hlt2 : b / 10 + c < N := by
      have : b / 10 ≤ b := Nat.div_le_self b 10
      omega
    have e2 : D (b / 10 + c) ≤ D (b / 10) + D c := IH (b / 10 + c) hlt2 (b / 10) c rfl
    have hDc : D c ≤ c := Nat.digit_sum_le 10 c
    rw [hDN, hDa, hDb]
    omega

@[category API, AMS 11]
lemma digits_repunit (k : ℕ) :
    Nat.digits 10 (10 ^ k - 1) = List.replicate k 9 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpos : 1 ≤ 10 ^ k := Nat.one_le_pow _ _ (by norm_num)
    have h1 : 10 ^ (k + 1) - 1 = 9 + 10 * (10 ^ k - 1) := by
      have h2 : 10 ^ (k + 1) = 10 * 10 ^ k := by ring
      omega
    rw [h1, Nat.digits_add 10 (by norm_num) 9 (10 ^ k - 1) (by norm_num) (by left; norm_num), ih,
      List.replicate_succ]

@[category API, AMS 11]
lemma D_repunit (k : ℕ) : D (10 ^ k - 1) = 9 * k := by
  unfold D
  rw [digits_repunit, List.sum_replicate]
  simp [Nat.mul_comm]

@[category API, AMS 11]
lemma len_repunit (k : ℕ) : (Nat.digits 10 (10 ^ k - 1)).length = k := by
  rw [digits_repunit, List.length_replicate]

@[category API, AMS 11]
lemma D_le (n : ℕ) : D n ≤ 9 * (Nat.digits 10 n).length := by
  unfold D
  have hb : ∀ x ∈ Nat.digits 10 n, x ≤ 9 := by
    intro x hx
    have := Nat.digits_lt_base (by norm_num) hx
    omega
  calc (Nat.digits 10 n).sum ≤ (Nat.digits 10 n).length • 9 :=
        List.sum_le_card_nsmul _ 9 hb
    _ = 9 * (Nat.digits 10 n).length := by rw [smul_eq_mul]; ring

@[category API, AMS 11]
lemma D_split (k q r : ℕ) (hq : 0 < q) (hr : r < 10 ^ k) :
    D (10 ^ k * q + r) = D q + D r := by
  have hlen : (Nat.digits 10 r).length ≤ k := by
    have hxle : r ≤ 10 ^ k - 1 := by omega
    calc (Nat.digits 10 r).length
        ≤ (Nat.digits 10 (10 ^ k - 1)).length := Nat.le_digits_len_le 10 r _ hxle
      _ = k := len_repunit k
  have key := Nat.digits_append_zeroes_append_digits (b := 10) (n := r) (m := q)
    (k := k - (Nat.digits 10 r).length) (by norm_num) hq
  rw [Nat.add_sub_cancel' hlen] at key
  have hval : r + 10 ^ k * q = 10 ^ k * q + r := by ring
  rw [hval] at key
  unfold D
  rw [← key]
  simp [List.sum_append, List.sum_replicate]
  ring

@[category API, AMS 11]
lemma digitSum_multiple_ge (k : ℕ) (hk : 1 ≤ k) :
    ∀ M, 0 < M → (10 ^ k - 1) ∣ M → 9 * k ≤ D M := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M IH =>
    intro hMpos hdvd
    have hP : 10 ≤ 10 ^ k := by
      calc (10 : ℕ) = 10 ^ 1 := by ring
        _ ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have hpow_pos : 0 < 10 ^ k := by positivity
    set m := 10 ^ k - 1 with hm
    have hmval : 10 ^ k = m + 1 := by omega
    have hm1 : 1 ≤ m := by omega
    by_cases hsmall : M < 10 ^ k
    · obtain ⟨t, ht⟩ := hdvd
      have ht0 : t ≠ 0 := by rintro rfl; simp [ht] at hMpos
      have ht1 : t = 1 := by
        by_contra htne
        have ht2 : 2 ≤ t := by omega
        have hbig : m * 2 ≤ m * t := Nat.mul_le_mul (le_refl m) ht2
        omega
      have hDM : D M = 9 * k := by rw [ht, ht1, Nat.mul_one, hm, D_repunit]
      omega
    · push_neg at hsmall
      set q := M / 10 ^ k with hqdef
      set r := M % 10 ^ k with hrdef
      have hrlt : r < 10 ^ k := Nat.mod_lt _ hpow_pos
      have hMqr : M = 10 ^ k * q + r := (Nat.div_add_mod M (10 ^ k)).symm
      have hqpos : 0 < q := by
        rw [hqdef]; exact Nat.div_pos hsmall hpow_pos
      have hexp : 10 ^ k * q = m * q + q := by rw [hmval]; ring
      have hcong : M = m * q + (q + r) := by
        have : M = (m + 1) * q + r := by rw [← hmval, ← hMqr]
        linarith
      have hsplit : D M = D q + D r := by rw [hMqr]; exact D_split k q r hqpos hrlt
      have hMdvd : m ∣ (q + r) := by
        have hd : m ∣ (m * q + (q + r)) := by rw [← hcong]; exact hdvd
        exact (Nat.dvd_add_right (Dvd.intro q rfl)).mp hd
      have hMpos' : 0 < q + r := by omega
      have hlt : q + r < M := by
        rw [hMqr]
        nlinarith [show 10 ≤ 10 ^ k from hP, show 1 ≤ q from hqpos]
      have hM' : 9 * k ≤ D (q + r) := IH (q + r) hlt hMpos' hMdvd
      have hsub : D (q + r) ≤ D q + D r := D_add_le (q + r) q r rfl
      omega

@[category API, AMS 11]
lemma big_of_D (k : ℕ) (hk : 1 ≤ k) (x : ℕ) (h : 9 * k ≤ D x) :
    10 ^ (k - 1) ≤ x := by
  by_contra hlt
  push_neg at hlt
  have hxle : x ≤ 10 ^ (k - 1) - 1 := by omega
  have hlen : (Nat.digits 10 x).length ≤ k - 1 :=
    calc (Nat.digits 10 x).length
        ≤ (Nat.digits 10 (10 ^ (k - 1) - 1)).length := Nat.le_digits_len_le 10 x _ hxle
      _ = k - 1 := len_repunit (k - 1)
  have hDle := D_le x
  omega

@[category API, AMS 11]
lemma reachable_D_ge (k : ℕ) (hk : 1 ≤ k) :
    ∀ v ∈ reachable_zeroless_factorials (10 ^ k - 1), 9 * k ≤ D v := by
  intro v hv
  have hNpos : 0 < 10 ^ k - 1 := by
    have : 10 ≤ 10 ^ k := by
      calc (10 : ℕ) = 10 ^ 1 := by ring
        _ ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  obtain ⟨P, hP⟩ : ∃ P, 10 ^ k - 1 = P + 1 := ⟨10 ^ k - 1 - 1, by omega⟩
  rw [hP] at hv
  have hunf : reachable_zeroless_factorials (P + 1) =
      (reachable_zeroless_factorials P).biUnion
        (fun m => {(P + 1) * m, remove_zeros ((P + 1) * m)}) := rfl
  rw [hunf] at hv
  simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hv
  obtain ⟨u, hu, hv⟩ := hv
  have hupos := reachable_pos P u hu
  have hmult : (P + 1) = 10 ^ k - 1 := hP.symm
  have hdvd : (10 ^ k - 1) ∣ ((P + 1) * u) := by
    rw [hmult]; exact Dvd.intro u rfl
  have hprodpos : 0 < (P + 1) * u := by positivity
  rcases hv with rfl | rfl
  · exact digitSum_multiple_ge k hk ((P + 1) * u) hprodpos hdvd
  · rw [D_remove]
    exact digitSum_multiple_ge k hk ((P + 1) * u) hprodpos hdvd

@[category API, AMS 11]
lemma a_ge (k : ℕ) (hk : 1 ≤ k) : 10 ^ (k - 1) ≤ a (10 ^ k - 1) := by
  apply big_of_D k hk
  have hmem : a (10 ^ k - 1) ∈ reachable_zeroless_factorials (10 ^ k - 1) :=
    Finset.min'_mem _ _
  exact reachable_D_ge k hk _ hmem

@[category API, AMS 11]
theorem not_bddAbove_range_a : ¬ BddAbove (Set.range a) := by
  rintro ⟨B, hB⟩
  have hk : 1 ≤ B + 1 := by omega
  have h1 : 10 ^ ((B + 1) - 1) ≤ a (10 ^ (B + 1) - 1) := a_ge (B + 1) hk
  have h3 : (B + 1) - 1 = B := by omega
  rw [h3] at h1
  have h2 : a (10 ^ (B + 1) - 1) ≤ B := hB (Set.mem_range_self (10 ^ (B + 1) - 1))
  have h4 : B < 10 ^ B := Nat.lt_pow_self (by norm_num)
  omega

/--
Is the sequence $a(n)$ bounded?

The sequence is unbounded because deleting zero digits preserves the base-10 digit sum,
and for $n = 10^k - 1$, every reachable value has digit sum at least $9k$,
which forces $a(10^k - 1) \ge 10^{k-1} \to \infty$.
-/
@[category research solved, AMS 11]
theorem is_bounded : answer(False) ↔ BddAbove (Set.range a) := by
  constructor
  · intro h
    contradiction
  · intro h
    exact (not_bddAbove_range_a h).elim

end OeisA374265
