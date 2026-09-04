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
import FormalConjectures.Wikipedia.Borsuk.G2Four.Partition
import FormalConjectures.Wikipedia.Borsuk.G2Four.Dim63

/-!
# Counterexamples to Borsuk's conjecture

This file derives the falsity of Borsuk's conjecture in dimensions $63$, $64$ and $65$ from
the existence of the record point configurations, all of which are proved from the explicit
$G_2(4)$ construction in `FormalConjectures/Wikipedia/Borsuk/G2Four/` (with `native_decide`
used for the large finite graph facts, which are tagged `category test`):

* `exists_bondarenko_vectors`: Bondarenko's 416 vectors in $\mathbb{R}^{65}$ [Bo14];
* `exists_jenrichBrouwer_vectors_in_hyperplane`: 352 of them orthogonal to a common
  nonzero vector [JB14];
* `exists_borsuk63_vectors`: the 321-point configuration in $\mathbb{R}^{63}$ [Gr26].

## The constructions

* **Bondarenko (2013), dimension 65.** The $G_2(4)$ graph is a strongly regular graph
  $\mathrm{srg}(416, 100, 36, 20)$ with eigenvalues $100, 20, -4$ of multiplicities
  $1, 65, 350$. The matrix $M = A + 4I - J/4$ (with $A$ the adjacency matrix) satisfies
  $M^2 = 24M$ and has rank $65$, so its rows realise the 416 vertices as vectors in
  $\mathbb{R}^{65}$ with inner products $90, 18, -6$ according to whether $x = y$, $x \sim y$,
  $x \not\sim y$; hence $\|\bar x - \bar y\|^2 = 144$ for adjacent and $192$ for non-adjacent
  vertices. A subset of smaller diameter avoids the distance $\sqrt{192}$, hence is a clique,
  and the clique number of the $G_2(4)$ graph is $5$.

* **Jenrich–Brouwer (2014), dimension 64.** The $G_2(4)$ graph $\Gamma$ is the local graph
  of the Suzuki graph $\Sigma = \mathrm{srg}(1782, 416, 100, 96)$. For two non-adjacent
  vertices $a, b$ of $\Sigma$, the 96 common neighbours form a set $B \subseteq V(\Gamma)$
  which splits into three mutually non-adjacent 32-sets $B_1, B_2, B_3$. The 352 points
  corresponding to $B_1 \cup (V(\Gamma) \setminus B)$ are orthogonal to the vector
  $u = \sum_{y \in B_2} \bar y - \sum_{y \in B_3} \bar y$, which is nonzero, hence they lie in
  a hyperplane; the reduction to $\mathbb{R}^{64}$ is `exists_isometric_map_of_inner_eq_zero`.

* **Grinsztajn (2026), dimension 63.** The 320 vectors indexed by $V(\Gamma) \setminus B$ are
  orthogonal to two independent vectors, hence lie in a 63-dimensional subspace. Adding the
  orthogonal projection of one deleted $B_1$-vertex onto that subspace, rescaled by
  $\mu = (-1 + \sqrt{222})/13$ so that its far distance is exactly $\sqrt{192}$, gives 321
  points of diameter $\sqrt{192}$ in which every subset avoiding the distance $\sqrt{192}$ has
  at most 5 points. The construction was found with AI assistance and verified by exact
  computation in [Gr26]; it was found independently by Konz and by Ji.

*References:*
- [Bo14] Bondarenko, A. (2014). *On Borsuk's conjecture for two-distance sets*.
  Discrete & Computational Geometry 51(3), 509–515. https://arxiv.org/abs/1305.2584
- [JB14] Jenrich, T., Brouwer, A. E. (2014). *A 64-dimensional counterexample to Borsuk's
  conjecture*. Electronic Journal of Combinatorics 21(4), P4.29. https://arxiv.org/abs/1308.0206
- [Gr26] Grinsztajn, M. (2026). *A 63-dimensional counterexample to Borsuk's conjecture*.
  https://github.com/maaxgrin/borsuk-63-counterexample
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

/-- **The mathematical core of the Jenrich–Brouwer counterexample**: 352 of Bondarenko's
416 vectors are orthogonal to a common nonzero vector, i.e. lie in a hyperplane of
`ℝ⁶⁵`, and retain the two-distance and clique properties. Proved in
`FormalConjectures/Wikipedia/Borsuk/G2Four/Partition.lean` from the explicit `B₁, B₂, B₃`
partition data. -/
@[category API, AMS 52]
theorem exists_jenrichBrouwer_vectors_in_hyperplane :
    ∃ (v : Fin 352 → EuclideanSpace ℝ (Fin 65)) (u : EuclideanSpace ℝ (Fin 65)),
      u ≠ 0 ∧ (∀ k, ⟪u, v k⟫ = 0) ∧
      Function.Injective v ∧
      (∀ i j, i ≠ j → dist (v i) (v j) = 12 ∨ dist (v i) (v j) = Real.sqrt 192) ∧
      (∃ i j, i ≠ j ∧ dist (v i) (v j) = 12) ∧
      ∀ s : Finset (Fin 352),
        (∀ i ∈ s, ∀ j ∈ s, i ≠ j → dist (v i) (v j) = 12) → s.card ≤ 5 :=
  G2Four.exists_jenrichBrouwer

/-- The Jenrich–Brouwer configuration transported to `ℝ⁶⁴` via the hyperplane reduction
`exists_isometric_map_of_inner_eq_zero`. -/
@[category API, AMS 52]
theorem exists_jenrichBrouwer_vectors :
    ∃ v : Fin 352 → EuclideanSpace ℝ (Fin 64),
      Function.Injective v ∧
      (∀ i j, i ≠ j → dist (v i) (v j) = 12 ∨ dist (v i) (v j) = Real.sqrt 192) ∧
      (∃ i j, i ≠ j ∧ dist (v i) (v j) = 12) ∧
      ∀ s : Finset (Fin 352),
        (∀ i ∈ s, ∀ j ∈ s, i ≠ j → dist (v i) (v j) = 12) → s.card ≤ 5 := by
  obtain ⟨v, u, hu, hvu, hinj, h2, hnear, hclique⟩ :=
    exists_jenrichBrouwer_vectors_in_hyperplane
  obtain ⟨v', hdist⟩ := exists_isometric_map_of_inner_eq_zero v hu hvu
  refine ⟨v', ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have h0 : dist (v i) (v j) = 0 := by rw [← hdist i j, hij, dist_self]
    exact hinj (dist_eq_zero.mp h0)
  · intro i j hij
    rw [hdist i j]
    exact h2 i j hij
  · obtain ⟨i, j, hij, hd⟩ := hnear
    exact ⟨i, j, hij, by rw [hdist i j]; exact hd⟩
  · intro s hs
    exact hclique s fun i hi j hj hij => by rw [← hdist i j]; exact hs i hi j hj hij

/-- **The Jenrich–Brouwer configuration**: a two-distance set of 352 points in `ℝ⁶⁴` in
which every subset of smaller diameter has at most 5 points. -/
@[category API, AMS 52]
theorem exists_jenrichBrouwer_set :
    ∃ T : Set (EuclideanSpace ℝ (Fin 64)),
      T.Finite ∧ T.ncard = 352 ∧ IsTwoDistSet T ∧ SmallPartsLE T 5 := by
  obtain ⟨v, hv, h2, hnear, hclique⟩ := exists_jenrichBrouwer_vectors
  have hfar := exists_far_pair v (by simp) h2 hclique
  obtain ⟨hfin, hcard, htwo, hsmall⟩ :=
    finite_two_dist_package v hv (by norm_num) twelve_lt_sqrt192 h2 hnear hfar hclique
  exact ⟨Set.range v, hfin, by simpa using hcard, htwo, hsmall⟩

/-- The Jenrich–Brouwer configuration refutes Borsuk's conjecture in dimension 64:
covering 352 points by 65 parts of at most 5 points each is impossible, as
`65 * 5 = 325 < 352`. -/
@[category API, AMS 52]
theorem not_borsukConjecture_of_jenrichBrouwer_set
    (h : ∃ T : Set (EuclideanSpace ℝ (Fin 64)),
      T.Finite ∧ T.ncard = 352 ∧ IsTwoDistSet T ∧ SmallPartsLE T 5) :
    ¬ BorsukConjecture 64 := by
  obtain ⟨T, hfin, hcard, -, hm⟩ := h
  exact not_borsukConjecture_of_bad_set T hfin hcard (by norm_num) hm (by norm_num)

/-- **The mathematical core of the dimension-63 counterexample** [Gr26]: the 320 vectors
of the `C`-part of Bondarenko's configuration lie in a 63-dimensional subspace (they are
orthogonal to the two independent vectors `u₁₂ = ∑_{B₁} v - ∑_{B₂} v` and
`u₂₃ = ∑_{B₂} v - ∑_{B₃} v`), and adding the orthogonal projection of one deleted
`B₁`-vertex onto that subspace, rescaled by `μ = (-1 + √222)/13` (so that its far
distance is exactly `√192`), yields 321 points with diameter `√192` in which every subset
avoiding the distance `√192` has at most 5 points. The resulting set has three distinct
distances, not two. Proved in `FormalConjectures/Wikipedia/Borsuk/G2Four/Dim63.lean`. -/
@[category API, AMS 52]
theorem exists_borsuk63_vectors :
    ∃ v : Fin 321 → EuclideanSpace ℝ (Fin 63),
      Function.Injective v ∧
      (∀ i j, dist (v i) (v j) ≤ Real.sqrt 192) ∧
      (∃ i j, dist (v i) (v j) = Real.sqrt 192) ∧
      ∀ s : Finset (Fin 321),
        (∀ i ∈ s, ∀ j ∈ s, dist (v i) (v j) < Real.sqrt 192) → s.card ≤ 5 :=
  G2Four.exists_borsuk63

/-- **The dimension-63 configuration**: 321 points in `ℝ⁶³` in which every subset of
smaller diameter has at most 5 points. -/
@[category API, AMS 52]
theorem exists_borsuk63_set :
    ∃ T : Set (EuclideanSpace ℝ (Fin 63)),
      T.Finite ∧ T.ncard = 321 ∧ SmallPartsLE T 5 := by
  obtain ⟨v, hv, hle, hfar, hclique⟩ := exists_borsuk63_vectors
  obtain ⟨hfin, hcard, hsmall⟩ :=
    finite_farGraph_package v hv hle hfar hclique
  exact ⟨Set.range v, hfin, by simpa using hcard, hsmall⟩

/-- The dimension-63 configuration refutes Borsuk's conjecture in dimension 63: covering
321 points by 64 parts of at most 5 points each is impossible, as `64 * 5 = 320 < 321`. -/
@[category API, AMS 52]
theorem not_borsukConjecture_of_borsuk63_set
    (h : ∃ T : Set (EuclideanSpace ℝ (Fin 63)),
      T.Finite ∧ T.ncard = 321 ∧ SmallPartsLE T 5) :
    ¬ BorsukConjecture 63 := by
  obtain ⟨T, hfin, hcard, hm⟩ := h
  exact not_borsukConjecture_of_bad_set T hfin hcard (by norm_num) hm (by norm_num)

/-- **Borsuk's conjecture is false in dimension 65** (Bondarenko 2013). -/
@[category API, AMS 52]
theorem not_borsukConjecture_65 : ¬ BorsukConjecture 65 :=
  not_borsukConjecture_of_bondarenko_set exists_bondarenko_set

/-- **Borsuk's conjecture is false in dimension 64** (Jenrich–Brouwer 2014), the smallest
dimension with a refereed counterexample. -/
@[category API, AMS 52]
theorem not_borsukConjecture_64 : ¬ BorsukConjecture 64 :=
  not_borsukConjecture_of_jenrichBrouwer_set exists_jenrichBrouwer_set

/-- **Borsuk's conjecture is false in dimension 63** (Grinsztajn 2026), the current record
for the smallest dimension of a counterexample. -/
@[category API, AMS 52]
theorem not_borsukConjecture_63 : ¬ BorsukConjecture 63 :=
  not_borsukConjecture_of_borsuk63_set exists_borsuk63_set

/-- **Borsuk's conjecture is false**: there is a dimension in which it fails. -/
@[category API, AMS 52]
theorem not_forall_borsukConjecture : ¬ ∀ n, BorsukConjecture n :=
  fun h => not_borsukConjecture_65 (h 65)

end Borsuk
