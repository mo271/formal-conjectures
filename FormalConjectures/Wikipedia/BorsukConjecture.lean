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
# Borsuk's conjecture

In 1933 Karol Borsuk [Bo33] asked whether every bounded subset of $\mathbb{R}^n$ can be
partitioned into $n + 1$ sets, each of strictly smaller diameter. The hypothesis that the
answer is positive became known as **Borsuk's conjecture**.

The conjecture is true for $n = 2$ [Bo33] and $n = 3$ [Pe47, Eg55]. It is false in general:
Kahn and Kalai [KK93] disproved it for $n = 1325$ and for all $n > 2014$. The smallest
dimension in which it is currently known to fail is $n = 64$ [JB14], building on Bondarenko's
counterexample in dimension $65$ [Bo14]. The cases $4 \leq n \leq 63$ are open.

A closely related formulation, using `Metric.diam` on sets of positive diameter, is
`erdos_505` in `FormalConjectures.ErdosProblems.«505»`.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Borsuk%27s_conjecture)
- [Bo33] Borsuk, K. (1933). *Drei Sätze über die n-dimensionale euklidische Sphäre*.
  Fundamenta Mathematicae 20, 177–190. https://doi.org/10.4064/fm-20-1-177-190
- [Pe47] Perkal, J. (1947). *Sur la subdivision des ensembles en parties de diamètre inférieur*.
  Colloquium Mathematicum 2, 45.
- [Eg55] Eggleston, H. G. (1955). *Covering a three-dimensional set with sets of smaller
  diameter*. Journal of the London Mathematical Society 30, 11–24.
  https://doi.org/10.1112/jlms/s1-30.1.11
- [KK93] Kahn, J., Kalai, G. (1993). *A counterexample to Borsuk's conjecture*.
  Bulletin of the American Mathematical Society 29(1), 60–62.
  https://arxiv.org/abs/math/9307229
- [Bo14] Bondarenko, A. (2014). *On Borsuk's conjecture for two-distance sets*.
  Discrete & Computational Geometry 51(3), 509–515. https://doi.org/10.1007/s00454-014-9579-4
- [JB14] Jenrich, T., Brouwer, A. E. (2014). *A 64-dimensional counterexample to Borsuk's
  conjecture*. Electronic Journal of Combinatorics 21(4), P4.29. https://doi.org/10.37236/4069
- [Ka15] Kalai, G. (2015). *Some old and new problems in combinatorial geometry I: Around
  Borsuk's problem*. https://arxiv.org/abs/1505.04952
-/

open Metric Bornology

open scoped EuclideanGeometry

namespace Borsuk

variable {E : Type*} [PseudoEMetricSpace E]

/--
`HasBorsukCover k s` means that the set `s` can be covered by `k` sets, each of strictly
smaller extended diameter than `s`.

We use the extended diameter `Metric.ediam` rather than `Metric.diam`: the latter takes the
junk value `0` on unbounded sets, which would make `Set.univ` a covering set of "small"
diameter. With `Metric.ediam`, a set of diameter `0` has no Borsuk cover, and an unbounded
set has no finite Borsuk cover, matching Borsuk's formulation for bounded sets with at
least two points.
-/
def HasBorsukCover (k : ℕ) (s : Set E) : Prop :=
  ∃ c : Fin k → Set E, s ⊆ ⋃ i, c i ∧ ∀ i, ediam (c i) < ediam s

/--
**Borsuk's conjecture** in dimension `n`: every bounded subset of $\mathbb{R}^n$ with at
least two points can be partitioned into $n + 1$ sets of strictly smaller diameter.
-/
def BorsukConjecture (n : ℕ) : Prop :=
  ∀ s : Set (ℝ^n), IsBounded s → s.Nontrivial → HasBorsukCover (n + 1) s

/--
**Borsuk's conjecture**, open range: every bounded subset of $\mathbb{R}^n$ with at least two
points can be partitioned into $n + 1$ sets of strictly smaller diameter, for
$4 \leq n \leq 63$.

The conjecture is known to be true for $n \leq 3$ and false for $n \geq 64$.
-/
@[category research open, AMS 52]
theorem borsuk_conjecture (n : ℕ) (hn : 4 ≤ n) (hn' : n ≤ 63) : BorsukConjecture n := by
  sorry

/-- **Borsuk's conjecture** in dimension $4$, the smallest open case. -/
@[category research open, AMS 52]
theorem borsuk_conjecture.four : BorsukConjecture 4 := by
  sorry

/-- **Borsuk's conjecture** in the plane, proved by Borsuk [Bo33]. -/
@[category research solved, AMS 52]
theorem borsuk_conjecture.two : BorsukConjecture 2 := by
  sorry

/-- **Borsuk's conjecture** in dimension $3$, proved by Perkal [Pe47] and Eggleston [Eg55]. -/
@[category research solved, AMS 52]
theorem borsuk_conjecture.three : BorsukConjecture 3 := by
  sorry

/--
**Borsuk's conjecture** is false in general: Kahn and Kalai [KK93] gave counterexamples in
dimension $1325$ and in every dimension $n > 2014$.
-/
@[category research solved, AMS 52]
theorem borsuk_conjecture.not_forall : ¬ ∀ n, BorsukConjecture n := by
  sorry

/-- **Borsuk's conjecture** fails in dimension $65$, by Bondarenko [Bo14]. -/
@[category research solved, AMS 52]
theorem borsuk_conjecture.not_sixty_five : ¬ BorsukConjecture 65 := by
  sorry

/--
**Borsuk's conjecture** fails in dimension $64$, by Jenrich and Brouwer [JB14]. This is the
smallest dimension in which the conjecture is currently known to be false.
-/
@[category research solved, AMS 52]
theorem borsuk_conjecture.not_sixty_four : ¬ BorsukConjecture 64 := by
  sorry

end Borsuk
