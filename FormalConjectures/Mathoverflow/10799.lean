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
# Optimal monotone families for the discrete isoperimetric inequality

*References:*
- [mathoverflow/10799](https://mathoverflow.net/questions/10799)
  asked by user [*Gil Kalai*](https://mathoverflow.net/users/1532/gil-kalai)
- [Optimal Monotone Families for the Discrete Isoperimetric Inequality](https://gilkalai.wordpress.com/ai/optimal-monotone-families-for-the-discrete-isoperimetric-inequality/)
  by *Gil Kalai* (2026), a Polymath project with AI agents
- [An Isoperimetric Inequality for the Hamming Cube and Integrality Gaps in Bounded-Degree
  Graphs](https://arxiv.org/abs/math/0603218) by *Jeff Kahn* and *Gil Kalai* (2006)
- [A Proof of the Kahn–Kalai Conjecture](https://arxiv.org/abs/2203.17207) by *Jinyoung Park*
  and *Huy Tuan Pham* (2022)

-/

namespace Mathoverflow10799

open Finset Real

/--
Start with a set $X=\{1,2,...,n\}$ of $n$ elements and the family $2^X$ of all subsets of $X$.
For a real number $p$ between zero and one, we consider a probability distribution $\mu_p$ on
$2^X$ where the probability that $i \in S$ is $p$, independently for different $i$'s.
Thus for $p=1/2$ we get the uniform probability distribution.

For $S \subseteq \{0, \ldots, n-1\}$, its probability is $p^{|S|} (1-p)^{n - |S|}$.
-/
noncomputable def μ {n : ℕ} (p : ℝ) (S : Finset (Fin n)) : ℝ :=
  p ^ #S * (1 - p) ^ (n - #S)

/-- For $p = 1/2$, the $p$-biased measure is the uniform distribution:
$\mu_{1/2}(S) = (1/2)^n$ for every $S \subseteq [n]$. -/
@[category test, AMS 5]
theorem μ_half_eq_uniform {n : ℕ} (S : Finset (Fin n)) :
    μ (1/2) S = (1/2 : ℝ) ^ n := by
  have h : #S ≤ n := S.card_le_univ.trans_eq (Fintype.card_fin n)
  simp only [μ]
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 from by ring, ← pow_add, Nat.add_sub_cancel' h]

/--
The $p$-biased measure of a family $\mathcal F \subseteq 2^{[n]}$,
i.e. $\mu_p(\mathcal F) = \sum_{S \in \mathcal F} \mu_p(S)$.
-/
noncomputable def μFamily {n : ℕ} (p : ℝ) (F : Finset (Finset (Fin n))) : ℝ :=
  ∑ S ∈ F, μ p S

/--
Given a family $F$, for a subset $S$ of $X$, we write $h(S)$ as the number of subsets $T$ in $X$
such that
(1) $T$ differs from $S$ in exactly one element
(2) Exactly one set among $S$ and $T$ belongs to $F$.
-/
def boundaryCount (n : ℕ) (F : Finset (Finset (Fin n))) (S : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n ↦ Xor' (S ∈ F) (symmDiff S {i} ∈ F)).card

/--
The edge-boundary of $F$ is the expectation of $h(S)$ (according to $\mu_p$) over all
subsets $S$ of $X$. It is denoted by $I^p(F)$.
-/
noncomputable def edgeBoundary (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) : ℝ :=
  ∑ S : Finset (Fin n), μ p S * boundaryCount n F S

/--
A family $F$ of subsets of $2^X$ is monotone increasing if when $S$ belongs to $F$ and $T$
contains $S$ then $T$ also belongs to $F$. (Monotone increasing families also also called "filtes"
and "up-families".) From now on we will restrict our attention to the case of monotone increasing
families.

This is Mathlib's `IsUpperSet` applied to the coercion of $\mathcal F$ to a set,
using the fact that `≤` on `Finset` is `⊆`.
-/
abbrev IsMonotoneIncreasing {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  IsUpperSet (↑F : Set (Finset (Fin n)))

/--
We say that a family is optimal for $\mu_p$ if the isoperimetric inequality (IR) is sharp up to a
multiplicative constant $1000 \log (1/p)$.

Since the lower bound from (IR) is
$$\frac{\mu_p(\mathcal F) \cdot \log(1/\mu_p(\mathcal F))}{p \cdot \log(1/p)},$$
multiplying by $1000 \log(1/p)$ gives the condition
$$I^p(\mathcal F) \le \frac{1000}{p} \cdot \mu_p(\mathcal F) \cdot \log \frac{1}{\mu_p(\mathcal F)}.$$
-/
noncomputable def IsOptimal {n : ℕ} (p : ℝ) (F : Finset (Finset (Fin n))) : Prop :=
  let m := μFamily p F
  edgeBoundary n p F ≤ 1000 * (1 / p * m * Real.log (1 / m))

section PerlesCounterexample

/-- The counterexample family: all non-empty subsets of `Fin n`. -/
def perlesFamily (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.erase ∅

/-- The counterexample family is monotone increasing: if $S \neq \emptyset$ and $S \subseteq T$,
then $T \neq \emptyset$. -/
lemma perlesFamily_monotone (n : ℕ) : IsMonotoneIncreasing (perlesFamily n) := by
  intro S T hST hS
  simp only [perlesFamily, Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true] at hS ⊢
  exact fun h => hS (Finset.subset_empty.mp (h ▸ hST))

/-- For the counterexample family, $\mu_p(F) = 1 - (1-p)^n$. -/
lemma perlesFamily_measure {n : ℕ} (p : ℝ) :
    μFamily p (perlesFamily n) = 1 - (1 - p) ^ n := by
  unfold μFamily perlesFamily
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)]
  have : ∑ S : Finset (Fin n), μ p S = 1 := by
    unfold μ
    have h := Fintype.sum_pow_mul_eq_add_pow (Fin n) p (1 - p)
    rw [Fintype.card_fin] at h; rw [h]; simp
  rw [this]
  simp [μ, Finset.card_empty]

/-- For the counterexample family, $I^p(F) = n(1-p)^{n-1}$. -/
lemma perlesFamily_edgeBoundary {n : ℕ} (p : ℝ) (hp : 0 < p) (hp' : p < 1) :
    edgeBoundary n p (perlesFamily n) = n * (1 - p) ^ (n - 1) := by
  norm_num(config := {singlePass :=1}) [perlesFamily, true,edgeBoundary]
  norm_num[boundaryCount, μ,mul_comm]
  rw [ Fintype.sum_congr _ _ fun and=>by rw [ Finset.card_filter,Nat.cast_sum, Finset.mul_sum], Finset.sum_comm]
  norm_num[iff_iff_and_or_not_and_not,Finset.sum_ite,ite_and,ite_or,Finset.filter_eq']
  cases n with ring!

/-- Key analytic inequality: $\log(1/(1-q)) \leq q/(1-q)$ for $q \in (0, 1)$. -/
lemma log_one_sub_inv_le {q : ℝ} (hq : 0 < q) (hq' : q < 1) :
    Real.log (1 / (1 - q)) ≤ q / (1 - q) := by
  have h1mq : 0 < 1 - q := by linarith
  rw [one_div]
  -- log(x) ≤ x - 1 applied to x = (1-q)⁻¹ gives log((1-q)⁻¹) ≤ (1-q)⁻¹ - 1
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr h1mq)
  -- (1-q)⁻¹ - 1 = q/(1-q)
  have hid : (1 - q)⁻¹ - 1 = q / (1 - q) := by
    rw [inv_eq_one_div, div_sub_one h1mq.ne', sub_sub_cancel]
  linarith


/-- For the counterexample family, if $np/(1-p) > 1000$ then $F$ is not optimal for $\mu_p$.
This combines the measure and edge boundary computations with the log inequality. -/
lemma perlesFamily_not_optimal {n : ℕ} {p : ℝ} (hp : 0 < p) (hp' : p < 1)
    (hn : 0 < n)
    (hbig : n * p / (1 - p) > 1000) :
    ¬ IsOptimal p (perlesFamily n) := by
  -- IsOptimal says: edgeBoundary ≤ 1000 * (1/p * m * log(1/m))
  -- We show edgeBoundary > 1000 * (1/p * m * log(1/m))
  unfold IsOptimal
  simp only [not_le]
  rw [perlesFamily_measure, perlesFamily_edgeBoundary p hp hp']
  set q := (1 - p) ^ n with hq_def
  -- Now goal: 1000 * (1/p * (1 - q) * log(1/(1 - q))) < n * (1 - p)^(n-1)
  -- Note: (1-p)^(n-1) = q / (1-p) when n ≥ 1.
  have h1mp : 0 < 1 - p := by linarith
  have hq_pos : 0 < q := pow_pos h1mp n
  have hq_lt_one : q < 1 := by
    have h1p_lt : 1 - p < 1 := by linarith
    exact pow_lt_one₀ h1mp.le h1p_lt (by omega)
  have h1mq : 0 < 1 - q := by linarith
  -- Upper bound the RHS using log inequality
  calc 1000 * (1 / p * (1 - q) * Real.log (1 / (1 - q)))
      ≤ 1000 * (1 / p * (1 - q) * (q / (1 - q))) := by
        gcongr; exact log_one_sub_inv_le hq_pos hq_lt_one
    _ = 1000 * (q / p) := by field_simp
    _ < n * p / (1 - p) * (q / p) := by
        gcongr
    _ = ↑n * q / (1 - p) := by field_simp
    _ = ↑n * (1 - p) ^ (n - 1) := by
        rw [hq_def]
        have hpow : (1 - p) ^ n = (1 - p) ^ (n - 1) * (1 - p) := by
          conv_lhs => rw [show n = n - 1 + 1 from by omega, pow_succ]
        rw [hpow, ← mul_assoc, mul_div_cancel_right₀ _ h1mp.ne']


end PerlesCounterexample

/--
Counterexample to the original conjecture (Shlomo Perles, April 2026).
The family of all non-empty subsets $F = \{S \subseteq [n] \mid S \neq \emptyset\}$ is monotone
increasing, yet for the interval $s = 1/(1001 \log n)$, $t = 1 - 1/n$, which satisfies
$t/s > 1000 \log n$ for large $n$, the family $F$ is not optimal for any $p \in [s, t]$.

The key computation: for this $F$, $\mu_p(F) = 1 - (1-p)^n$ and
$I^p(F) = n(1-p)^{n-1}$, and one shows $I^p(F) / H_p(F) \geq np/(1-p) \geq 1000 \log(1/s)
\geq 1000 \log(1/p)$ for all $p \in [s, t]$.

See the [blog discussion](https://gilkalai.wordpress.com/ai/optimal-monotone-families-for-the-discrete-isoperimetric-inequality/).
-/
@[category research solved, AMS 5 60]
theorem perles_counterexample :
    ∃ᶠ n in Filter.atTop, ∃ (F : Finset (Finset (Fin n))),
    IsMonotoneIncreasing F ∧
    ∃ (s t : ℝ), 0 < s ∧ s ≤ t ∧ t < 1 ∧ t / s > 1000 * Real.log n ∧
    ∀ p, s ≤ p → p ≤ t → ¬ IsOptimal p F := by
  rw [Filter.frequently_atTop]
  intro N
  -- Choose n large enough so that n/(1001 log n - 1) > 1000 and n > max N 2.
  obtain ⟨n, hn_large, hn_N⟩ : ∃ n : ℕ, n / (1001 * Real.log n - 1) > 1000 ∧ N ≤ n := by
    rcases(((Real.isLittleO_log_id_atTop.natCast_atTop.const_mul_left 1001).const_mul_left 1000).tendsto_div_nhds_zero.eventually_lt_const one_pos).and (Filter.mem_atTop (N+3))|>.exists
    use (by valid), (lt_div_iff₀ (by linarith only[Real.log_le_log three_pos (Nat.cast_le.2 (by valid:by valid≥3)),Real.lt_log_one_add_of_pos two_pos])).2 ? _,by valid
    linarith![(div_lt_one (Nat.cast_pos.2 (by valid))).1 (by valid:).1]
  refine ⟨n, hn_N, perlesFamily n, perlesFamily_monotone n,
    1 / (1001 * Real.log n), 1 - 1 / n, ?_, ?_, ?_, ?_, ?_⟩
  -- (i) 0 < s
  · use one_div_pos.2 (not_le.1 (by norm_num ∘hn_large.trans_le ∘div_nonpos_of_nonneg_of_nonpos n.cast_nonneg ∘ (by linear_combination.)))
  -- (ii) s ≤ t
  · use match n with|0|1=>by norm_num at* | S+2=>((div_le_div_iff₀ (by norm_num[Real.log_pos, one_lt_two.trans_le]) (by bound)).2 ?_).trans (one_sub_div (by norm_cast)).ge
    nlinarith only[Real.log_two_gt_d9,Real.log_le_log two_pos (Nat.cast_le.2 ((2).le_add_left S)),show(S: ℝ)+2 = _ by norm_cast]
  -- (iii) t < 1
  · norm_num[n.pos_of_ne_zero ∘mt (.▸hn_large)]
  -- (iv) t / s > 1000 * log n
  · match (n : ℕ) with|0 | ( (1)) =>norm_num at * | S+2 =>_
    field_simp at*
    nlinarith[Real.log_two_gt_d9,Real.log_le_log two_pos (Nat.cast_le.2 (by valid: S+2 > 1)),(lt_div_iff₀ ((div_pos_iff_of_pos_left (by bound)).1 (hn_large.trans' (by bound)))).1 hn_large]
  -- (v) ¬ IsOptimal p F for all p ∈ [s, t]
  · intro p hsp hpt
    have hp : 0 < p := by use (one_div_pos.2 (by linear_combination not_le.1 (by norm_num ∘hn_large.trans_le ∘div_nonpos_of_nonneg_of_nonpos n.cast_nonneg))).trans_le hsp-- 0 < s ≤ p
    have hp' : p < 1 := by norm_num [hpt.trans_lt, n.pos_of_ne_zero ∘mt ↑( ·▸hn_large)]-- p ≤ t = 1 - 1/n < 1
    have hn : 0 < n := by exact (pos_of_ne_zero (by·norm_num [·]at*))
    apply perlesFamily_not_optimal hp hp' hn
    -- Need: n * p / (1 - p) > 1000.
    -- Since p ≥ s = 1/(1001 log n), we have n * p / (1 - p) ≥ n / (1001 log n - 1) > 1000.
    exact (hn_large).trans_le ((mul_div_mul_right _ _ hp.ne')▸by bound[(div_le_iff₀ (by norm_num[hn.nat_succ_le.lt_of_ne ∘mt (·▸hp.trans_le hpt),Real.log_pos])).1 hsp])

/--
Problem: For every monotone increasing family $F$, given an interval $[s,t]$ of real numbers so
that $t/s > 1000 \log n$ we have some $p$ in the interval $[s,t]$ so that $F$ is optimal with
respect to $\mu_p$.

This was a "missing lemma" in the work of Kahn and Kalai on threshold behavior of monotone
properties. The related [Kahn–Kalai conjecture](https://arxiv.org/abs/math/0603218) was
[settled by Park and Pham](https://arxiv.org/abs/2203.17207).

**This conjecture is false** without the additional assumption $\mu_t(F) = 1/2$.
A counterexample was found by Shlomo Perles (April 7, 2026), see `perles_counterexample`.
The answer `False` follows from `perles_counterexample`.
-/
@[category research solved, AMS 5 60]
theorem mathoverflow_10799 : answer(False) ↔
    ∀ (n : ℕ) (_ : 2 ≤ n)
    (F : Finset (Finset (Fin n))) (_ : IsMonotoneIncreasing F)
    (s t : ℝ) (_ : 0 < s) (_ : s ≤ t) (_ : t < 1)
    (_ : t / s > 1000 * Real.log n),
    ∃ p, s ≤ p ∧ p ≤ t ∧ IsOptimal p F := by
  constructor
  · exact False.elim
  · intro h
    obtain ⟨n, ⟨F, hF, s, t, hs, hst, ht, hlog, hopt⟩, hn⟩ :=
      (perles_counterexample.and_eventually
        (Filter.eventually_atTop.mpr ⟨2, fun _ h => h⟩)).exists
    obtain ⟨p, hsp, hpt, hp⟩ := h n hn F hF s t hs hst ht hlog
    exact hopt p hsp hpt hp

/--
Conjecture 7 from Kahn–Kalai 2006: the same statement as the original
conjecture, but with the additional assumption that $t$ is the critical probability for $F$,
namely $\mu_t(F) = 1/2$.
-/
@[category research open, AMS 5 60]
theorem mathoverflow_10799.variants.kahn_kalai_conjecture_7 : answer(sorry) ↔
    ∀ (n : ℕ) (_ : 2 ≤ n)
    (F : Finset (Finset (Fin n))) (_ : IsMonotoneIncreasing F)
    (s t : ℝ) (_ : 0 < s) (_ : s ≤ t) (_ : t < 1)
    (_ : μFamily t F = 1 / 2)
    (_ : t / s > 1000 * Real.log n),
    ∃ p, s ≤ p ∧ p ≤ t ∧ IsOptimal p F := by
  sorry

/--
Weaker version proven by Kahn–Kalai: the same conclusion holds when $1000 \log n$ is replaced by
$C_\varepsilon \, n^\varepsilon$ for every fixed $\varepsilon > 0$.
-/
@[category research solved, AMS 5 60]
theorem mathoverflow_10799.variants.weak_kahn_kalai :
    ∀ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ (n : ℕ) (_ : 2 ≤ n)
    (F : Finset (Finset (Fin n))) (_ : IsMonotoneIncreasing F)
    (s t : ℝ) (_ : 0 < s) (_ : s ≤ t) (_ : t < 1)
    (_ : t / s > C * (n : ℝ) ^ ε),
    ∃ p, s ≤ p ∧ p ≤ t ∧ IsOptimal p F := by
  sorry

/--
Now a famous isoperimetric relation asserts that
(IR) $I^p(F) \ge (1/p) \mu_p(F) \cdot \log \mu_p(F)$
This relation is true for every family $F$ and every $p$. It is especially famous and simple when
$p=1/2$ and $\mu_p(F)=1/2$. In this case, it says that given a set of half the vertices of the
discrete cube $2^X$, the number of edges between $F$ and its complement is at least $2^{n-1}$.
-/
@[category graduate, AMS 5 60]
theorem discrete_isoperimetric_inequality (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (F : Finset (Finset (Fin n))) :
    let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.log (1 / m) / (p * Real.log (1 / p)) := by
  sorry

section Tests

/--
The $p$-biased measure is a probability distribution: it sums to $1$ over all subsets.
This is the binomial identity $(p + (1-p))^n = 1$.
-/
@[category test, AMS 5]
theorem μ_sum_eq_one (n : ℕ) (p : ℝ) :
    ∑ S : Finset (Fin n), μ p S = 1 := by
  unfold μ
  have h := Fintype.sum_pow_mul_eq_add_pow (Fin n) p (1 - p)
  rw [Fintype.card_fin] at h
  rw [h]
  simp

/-- The measure of the full power set is $1$. -/
@[category test, AMS 5]
theorem μFamily_univ (n : ℕ) (p : ℝ) :
    μFamily p (Finset.univ : Finset (Finset (Fin n))) = 1 := by
  unfold μFamily
  exact μ_sum_eq_one n p

/-- The boundary count is zero for the empty family (no set is in $\mathcal F$). -/
@[category test, AMS 5]
theorem boundaryCount_empty (n : ℕ) (S : Finset (Fin n)) :
    boundaryCount n ∅ S = 0 := by
  simp [boundaryCount, Xor', filter_false]

/-- The edge boundary is zero for the empty family. -/
@[category test, AMS 5]
theorem edgeBoundary_empty (n : ℕ) (p : ℝ) :
    edgeBoundary n p ∅ = 0 := by
  simp [edgeBoundary, boundaryCount_empty]

/-- The boundary count is zero for the full family (every set is in $\mathcal F$). -/
@[category test, AMS 5]
theorem boundaryCount_univ (n : ℕ) (S : Finset (Fin n)) :
    boundaryCount n Finset.univ S = 0 := by
  simp [boundaryCount, Xor', filter_false]

/-- The edge boundary is zero for the full family. -/
@[category test, AMS 5]
theorem edgeBoundary_univ (n : ℕ) (p : ℝ) :
    edgeBoundary n p Finset.univ = 0 := by
  simp [edgeBoundary, boundaryCount_univ]

end Tests

end Mathoverflow10799
