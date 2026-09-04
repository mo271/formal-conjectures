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
import FormalConjectures.Wikipedia.Borsuk.TwoDistance
import FormalConjectures.Wikipedia.Borsuk.Hyperplane
import FormalConjectures.Wikipedia.Borsuk.G2Four.Representation

/-!
# Counterexamples to Borsuk's conjecture

This file derives the falsity of Borsuk's conjecture in dimension $65$ from
the existence of the record point configurations, all of which are proved from the explicit
$G_2(4)$ construction in `FormalConjectures/Wikipedia/Borsuk/G2Four/` (with `native_decide`
used for the large finite graph facts, which are tagged `category test`):

* `exists_bondarenko_vectors`: Bondarenko's 416 vectors in $\mathbb{R}^{65}$ [Bo14];

## The constructions

* **Bondarenko (2013), dimension 65.** The $G_2(4)$ graph is a strongly regular graph
  $\mathrm{srg}(416, 100, 36, 20)$ with eigenvalues $100, 20, -4$ of multiplicities
  $1, 65, 350$. The matrix $M = A + 4I - J/4$ (with $A$ the adjacency matrix) satisfies
  $M^2 = 24M$ and has rank $65$, so its rows realise the 416 vertices as vectors in
  $\mathbb{R}^{65}$ with inner products $90, 18, -6$ according to whether $x = y$, $x \sim y$,
  $x \not\sim y$; hence $\|\bar x - \bar y\|^2 = 144$ for adjacent and $192$ for non-adjacent
  vertices. A subset of smaller diameter avoids the distance $\sqrt{192}$, hence is a clique,
  and the clique number of the $G_2(4)$ graph is $5$.

*References:*
- [Bo14] Bondarenko, A. (2014). *On Borsuk's conjecture for two-distance sets*.
  Discrete & Computational Geometry 51(3), 509–515. https://arxiv.org/abs/1305.2584
-/

namespace Borsuk

open Metric Bornology Set

open scoped RealInnerProductSpace

/-- The two distances of the Bondarenko and Jenrich–Brouwer configurations satisfy
`12 < √192`. -/
@[category API, AMS 52]
private theorem twelve_lt_sqrt192 : (12 : ℝ) < Real.sqrt 192 := by
  have h : (12 : ℝ) = Real.sqrt 144 := by
    rw [show (144 : ℝ) = 12 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- **The mathematical core of Bondarenko's counterexample** (dimension 65): 416 vectors
in `ℝ⁶⁵`, the Euclidean representation of the `G₂(4)` strongly regular graph, with
pairwise distances `12` (adjacent) and `√192` (non-adjacent), such that every `12`-clique
has at most 5 elements. Proved in `FormalConjectures/Wikipedia/Borsuk/G2Four/Representation.lean`
from the explicit `G₂(4)` construction (`native_decide` is used for the finite graph facts). -/
@[category API, AMS 52]
theorem exists_bondarenko_vectors :
    ∃ v : Fin 416 → EuclideanSpace ℝ (Fin 65),
      Function.Injective v ∧
      (∀ i j, i ≠ j → dist (v i) (v j) = 12 ∨ dist (v i) (v j) = Real.sqrt 192) ∧
      (∃ i j, i ≠ j ∧ dist (v i) (v j) = 12) ∧
      ∀ s : Finset (Fin 416),
        (∀ i ∈ s, ∀ j ∈ s, i ≠ j → dist (v i) (v j) = 12) → s.card ≤ 5 :=
  G2Four.exists_bondarenko

/-- **Bondarenko's configuration**: a two-distance set of 416 points in `ℝ⁶⁵` in which
every subset of smaller diameter has at most 5 points. -/
@[category API, AMS 52]
theorem exists_bondarenko_set :
    ∃ T : Set (EuclideanSpace ℝ (Fin 65)),
      T.Finite ∧ T.ncard = 416 ∧ IsTwoDistSet T ∧ SmallPartsLE T 5 := by
  obtain ⟨v, hv, h2, hnear, hclique⟩ := exists_bondarenko_vectors
  have hfar := exists_far_pair v (by simp) h2 hclique
  obtain ⟨hfin, hcard, htwo, hsmall⟩ :=
    finite_two_dist_package v hv (by norm_num) twelve_lt_sqrt192 h2 hnear hfar hclique
  exact ⟨Set.range v, hfin, by simpa using hcard, htwo, hsmall⟩

/-- Bondarenko's configuration refutes Borsuk's conjecture in dimension 65: covering 416
points by 66 parts of at most 5 points each is impossible, as `66 * 5 = 330 < 416`. -/
@[category API, AMS 52]
theorem not_borsukConjecture_of_bondarenko_set
    (h : ∃ T : Set (EuclideanSpace ℝ (Fin 65)),
      T.Finite ∧ T.ncard = 416 ∧ IsTwoDistSet T ∧ SmallPartsLE T 5) :
    ¬ BorsukConjecture 65 := by
  obtain ⟨T, hfin, hcard, -, hm⟩ := h
  exact not_borsukConjecture_of_bad_set T hfin hcard (by norm_num) hm (by norm_num)

/-- **Borsuk's conjecture is false in dimension 65** (Bondarenko 2013). -/
@[category API, AMS 52]
theorem not_borsukConjecture_65 : ¬ BorsukConjecture 65 :=
  not_borsukConjecture_of_bondarenko_set exists_bondarenko_set

/-- **Borsuk's conjecture is false**: there is a dimension in which it fails. -/
@[category API, AMS 52]
theorem not_forall_borsukConjecture : ¬ ∀ n, BorsukConjecture n :=
  fun h => not_borsukConjecture_65 (h 65)

end Borsuk
