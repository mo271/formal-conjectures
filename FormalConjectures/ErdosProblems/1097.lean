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

/-!
# Erdős Problem 1097

*References:*
- [erdosproblems.com/1097](https://www.erdosproblems.com/1097)
- [Bo99] Bourgain, J., On the dimension of {K}akeya sets and related maximal
inequalities. Geom. Funct. Anal. (1999), 256--282
- [KaTa99] Katz, Nets Hawk and Tao, Terence, Bounds on arithmetic projections, and applications to the
{K}akeya conjecture. Math. Res. Lett. (1999), 625--630.
- [Le15] Lemm, Marius, New counterexamples for sums-differences. Proc. Amer. Math. Soc. (2015), 3863--3868.
- [GGTW25] B. Georgiev, J. Gómez-Serrano, T. Tao, and A. Wagner, Mathematical exploration and discovery at scale. arXiv:2511.02864 (2025).
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
The main conjecture: for any finite set of integers $A$ with $|A| = n$, the number of distinct
common differences in three-term arithmetic progressions is $O(n^{3/2})$.

This conjecture was resolved negatively by showing that the problem is exactly equivalent to
Bourgain's sums-differences question [Bo99], which was introduced as an arithmetic path towards
the Kakeya conjecture. Under this equivalence:
- The greatest achievable exponent for this problem is equal to the smallest constant $c$
  achievable for Bourgain's sums-differences question:
  $$|A -_G B| \ll \max(|A|, |B|, |A +_G B|)^c$$
- The $O(n^{3/2})$ prediction is disproved because the lower bound has been shown to satisfy
  $c \ge 1.77898$ (due to Zheng and AlphaEvolve [GGTW25], improving on Lemm [Le15]), which is
  strictly greater than $3/2 = 1.5$.
- The best known upper bound is $c \le 11/6 \approx 1.833$ (due to Katz and Tao [KaTa99]).
- While the specific $O(n^{3/2})$ prediction is resolved negatively, the general question of
  determining the exact optimal exponent $c$ remains open.
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/f13dd54b520cdf2136fdd3a04f0f9fa50e311358/FormalConjectures/ErdosProblems/1097.lean#L306"]
theorem erdos_1097 : answer(False) ↔ ∃ C > (0 : ℝ), ∀ (A : Finset ℤ),
    (CommonDifferencesThreeTermAP A).ncard ≤ C * (A.card : ℝ) ^ (3 / 2 : ℝ) := by
  sorry

/--
A weaker bound has been proven: there are always at most $n^2$ such values of $d$.
-/
@[category textbook, AMS 11]
theorem erdos_1097.variants.weaker :
    ∀ A, (CommonDifferencesThreeTermAP A).ncard ≤ A.card ^ 2 := by
  sorry

/--
A trivial lower bound: for sufficiently large `n` there exist sets $A$ with $|A| = n$ that contain at least $\Omega(n)$
distinct common differences of three-term arithmetic progressions.
-/
@[category textbook, AMS 11]
theorem erdos_1097.variants.lower_bound : ∃ c > (0 : ℝ), ∀ᶠ n in Filter.atTop, ∃ (A : Finset ℤ),
    A.card = n ∧ c * (n : ℝ) ≤ (CommonDifferencesThreeTermAP A).ncard := by
  sorry

end Erdos1097
