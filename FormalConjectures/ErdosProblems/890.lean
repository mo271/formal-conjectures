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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 890

*Reference:*
- [erdosproblems.com/890](https://www.erdosproblems.com/890)
- [ErSe67] Erdős, P. and Selfridge, J. L., Some problems on the prime factors of consecutive
  integers. Illinois J. Math. (1967), 428--430.
-/

open Filter Finset Real
open scoped Nat.Prime ArithmeticFunction.omega

namespace Erdos890


lemma multiples_in_range (n k p : ℕ) (hp : p > 0) :
  k / p ≤ ((Finset.range k).filter (fun i => p ∣ n + i)).card := by
  use k.strongRec fun and x => if a :and<p then and.div_eq_of_lt a▸bot_le else (and.sub_add_cancel (not_lt.mp a))▸.trans (?_) (by rw [ Finset.card_filter, Finset.sum_range_add])
  exact (Nat.add_div_right _) hp▸Nat.add_le_add (((x _) (by valid)).trans (by rw [ Finset.card_filter])) (by cases hp with simp_all![←ZMod.natCast_eq_zero_iff,←eq_sub_iff_add_eq', Finset.sum_range _])

lemma omega_ge_card_primes (x : ℕ) (hx : x > 0) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
  (S.filter (fun p => p ∣ x)).card ≤ ω x := by
  show (star _)≥_
  exact ( Finset.card_mono fun and=>by simp_all[hx.ne']).trans (List.toFinset_card_le _)

lemma sum_swap_helper (n k : ℕ) (S : Finset ℕ) :
  ∑ i ∈ Finset.range k, (S.filter (fun p => p ∣ n + i)).card =
  ∑ p ∈ S, ((Finset.range k).filter (fun i => p ∣ n + i)).card := by
  simp_rw [ Finset.card_filter, S.sum_comm]

def S_26 : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23}

lemma S_26_primes (p : ℕ) (hp : p ∈ S_26) : p.Prime := by
  cases hp
  · decide
  · exact (by decide +revert ∘ List.mem_cons.1) (by valid:)

lemma sum_S_26 : ∑ p ∈ S_26, 26 / p = 36 := by
  exact ( Finset.sum_insert (by decide ) ).trans ( (by bound))

lemma pi_26_val : (π 26 : EReal) = 9 := by
  show(id _) = _
  show Nat.cast (star _) = _
  norm_num[Add.add]

lemma ereal_cast_le (a b : ℕ) (h : a ≤ b) : (a : EReal) ≤ (b : EReal) := by
  exact EReal.coe_le_coe_iff.2 (by gcongr)

lemma ereal_cast_sum (k n : ℕ) :
  ((∑ i ∈ Finset.range k, ω (n + i) : ℕ) : EReal) = ∑ i ∈ Finset.range k, (ω (n + i) : EReal) := by
  induction k with| zero=>norm_num|succ R L=>exact (.trans (L▸.trans (by rw [ Finset.sum_range_succ _,Nat.cast_add]) (by constructor)) ( Finset.sum_range_succ _ _).symm)

lemma omega_sum_ge_36 (n : ℕ) (hn : n > 0) :
  (36 : EReal) ≤ ∑ i ∈ Finset.range 26, (ω (n + i) : EReal) := by
  have h1 : ∀ i ∈ Finset.range 26, (S_26.filter (fun p => p ∣ n + i)).card ≤ ω (n + i) := by
    intro i _
    have hni : n + i > 0 := by omega
    exact omega_ge_card_primes (n + i) hni S_26 S_26_primes
  have h2 : ∑ i ∈ Finset.range 26, (S_26.filter (fun p => p ∣ n + i)).card ≤ ∑ i ∈ Finset.range 26, ω (n + i) := by
    exact Finset.sum_le_sum h1
  have h3 : ∑ i ∈ Finset.range 26, (S_26.filter (fun p => p ∣ n + i)).card = ∑ p ∈ S_26, ((Finset.range 26).filter (fun i => p ∣ n + i)).card := sum_swap_helper n 26 S_26
  have h4 : ∀ p ∈ S_26, 26 / p ≤ ((Finset.range 26).filter (fun i => p ∣ n + i)).card := by
    intro p hp
    have hp0 : p > 0 := by
      have hp_prime : p.Prime := S_26_primes p hp
      exact Nat.Prime.pos hp_prime
    exact multiples_in_range n 26 p hp0
  have h5 : ∑ p ∈ S_26, 26 / p ≤ ∑ p ∈ S_26, ((Finset.range 26).filter (fun i => p ∣ n + i)).card := by
    exact Finset.sum_le_sum h4
  have h6 : 36 ≤ ∑ i ∈ Finset.range 26, ω (n + i) := by
    have h_sum26 := sum_S_26
    omega
  have h7 : (36 : EReal) ≤ ((∑ i ∈ Finset.range 26, ω (n + i) : ℕ) : EReal) := ereal_cast_le 36 _ h6
  have h8 : ((∑ i ∈ Finset.range 26, ω (n + i) : ℕ) : EReal) = ∑ i ∈ Finset.range 26, (ω (n + i) : EReal) := ereal_cast_sum 26 n
  rw [←h8]
  exact h7

lemma filter_liminf_le_liminf (f g : ℕ → EReal) (h : ∀ᶠ n in Filter.atTop, f n ≤ g n) :
  Filter.liminf f Filter.atTop ≤ Filter.liminf g Filter.atTop := by
  simp_rw [Filter.liminf_eq,Filter.eventually_atTop] at h⊢
  apply (sSup_le_sSup fun and=>.rec fun and x =>⟨ _, fun and=>And.elim (x and ·|>.trans.comp (h.choose_spec and)) ∘sup_le_iff.1⟩)

lemma filter_liminf_const (c : EReal) :
  Filter.liminf (fun (_ : ℕ) => c) Filter.atTop = c := by
  simp_all

lemma liminf_ge_36 :
  (36 : EReal) ≤ Filter.liminf (fun n => ∑ i ∈ Finset.range 26, (ω (n + i) : EReal)) Filter.atTop := by
  have h : ∀ᶠ n in Filter.atTop, (36 : EReal) ≤ ∑ i ∈ Finset.range 26, (ω (n + i) : EReal) := by
    apply Filter.eventually_atTop.mpr
    use 1
    intro b hb
    exact omega_sum_ge_36 b hb
  have h_liminf : Filter.liminf (fun _ => (36 : EReal)) Filter.atTop ≤ Filter.liminf (fun n => ∑ i ∈ Finset.range 26, (ω (n + i) : EReal)) Filter.atTop := filter_liminf_le_liminf _ _ h
  have h_const : Filter.liminf (fun _ => (36 : EReal)) Filter.atTop = 36 := filter_liminf_const 36
  rw [h_const] at h_liminf
  exact h_liminf

lemma ereal_36_le_35_false (h : (36 : EReal) ≤ 35) : False := by
  contrapose! h
  constructor
  exact (mod_cast (by bound))

lemma ereal_bound_35 (h_pi : (π 26 : EReal) = 9) : (26 : EReal) + ↑(π 26) = 35 := by
  norm_num only [*]

/--
If $\omega(n)$ counts the number of distinct prime factors of $n$, then is it true that,
for every $k\geq 1$, $\liminf_{n\to \infty}\sum_{0\leq i < k}\omega(n+i)\leq k+\pi(k)?$
-/
@[category research open, AMS 11]
theorem erdos_890.parts.a :
    answer(False) ↔
    ∀ k ≥ 1, liminf (fun n ↦ (∑ i ∈ range k, (ω (n + i) : EReal))) atTop ≤ k + π k := by
  constructor
  · intro h
    exact False.elim h
  · intro h
    have h1 : 26 ≥ 1 := by norm_num
    have h26 := h 26 h1
    have h_pi : (π 26 : EReal) = 9 := pi_26_val
    have h_bound : (26 : EReal) + ↑(π 26) = 35 := ereal_bound_35 h_pi
    have h_le_35 : Filter.liminf (fun n => ∑ i ∈ Finset.range 26, (ω (n + i) : EReal)) Filter.atTop ≤ 35 := by
      rw [←h_bound]
      exact h26
    have h_contra : (36 : EReal) ≤ 35 := le_trans liminf_ge_36 h_le_35
    exact ereal_36_le_35_false h_contra



/--
Is it true that
$\limsup_{n\to \infty}\left(\sum_{0\leq i < k}\omega(n+i)\right) \frac{\log\log n}{\log n}=1?$
-/
@[category research open, AMS 11]
theorem erdos_890.parts.b :
    answer(sorry) ↔ ∀ k ≥ 1, limsup (fun n ↦ (∑ i ∈ range k, (ω (n + i) : EReal)) *
      (log (log n) / log n)) atTop = 1 := by
  sorry

/--
A question of Erdős and Selfridge [ErSe67], who observe that
$\liminf_{n\to \infty}\sum_{0\leq i < k}\omega(n+i)\geq k+\pi(k)-1$ for every $k$. This follows from
Pólya's theorem that the set of $k$-smooth integers has unbounded gaps - indeed,
$n(n+1)\cdots (n+k-1)$ is divisible by all primes $\leq k$ and, provided $n$ is large, all but at
most one of $n,n+1,\ldots,n+k-1$ has a prime factor $>k$ by Pólya's theorem.
-/
@[category research solved, AMS 11]
theorem erdos_890.variants.liminf_lower_bound (k : ℕ) :
    liminf (fun n ↦ (∑ i ∈ range k, (ω (n + i) : EReal))) atTop ≥ k + π k - 1 := by
  sorry

/--
It is a classical fact that $\limsup_{n\to \infty}\omega(n)\frac{\log\log n}{\log n}=1.$
-/
@[category research solved, AMS 11]
theorem erdos_890.variants.omega_limsup :
    limsup (fun n ↦ (ω n : EReal) * (log (log n) / log n)) atTop = 1 := by
  sorry

end Erdos890
