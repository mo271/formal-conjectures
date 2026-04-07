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

/--
Problem: For every monotone increasing family $F$, given an interval $[s,t]$ of real numbers so that
$t/s > 1000 \log n$ we have some $p$ in the interval $[s,t]$ so that $F$ is optimal with respect
to $\mu_p$.

This is a "missing lemma" in the work of Kahn and Kalai on threshold behavior of monotone
properties. The related [Kahn–Kalai conjecture](https://arxiv.org/abs/math/0603218) was
[settled by Park and Pham](https://arxiv.org/abs/2203.17207), but this lemma remains open.
-/
@[category research open, AMS 5 60]
theorem mathoverflow_10799 : answer(sorry) ↔
    ∀ (n : ℕ) (hn : 2 ≤ n)
    (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) (ht : t < 1)
    (hlog : t / s > 1000 * Real.log n),
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
