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
# Erdős Problem 944

*Reference:* [erdosproblems.com/944](https://www.erdosproblems.com/944)
-/

universe u
variable {V : Type u}


/--
Let $k \ge 4$ and $r\ge 1$. Must there exist a graph $G$ with chromatic number $k$
 such that every vertex is critical, yet every critical set of edges has size $>r$?

-/
@[category research open, AMS 11]
theorem erdos_944 : (∀ k ≥ 4, ∀ r ≥ 1, ∃ (G : SimpleGraph V), G.IsCritical k ∧
    (∀ (edges : Set (Sym2 V)), G.IsCriticalEdges edges → r < edges.ncard)) ↔ answer(sorry) := by
  sorry

/--
Let $k \ge 4$. Must there exist a graph $G$ with chromatic number $k$
such that every vertex is critical, yet every critical set of edges has size $>1$?

This was conjectured by Dirac in 1970.
-/
@[category research open, AMS 11]
theorem erdos_944.variants.one : (∀ k ≥ 4, ∃ (G : SimpleGraph V), G.IsCritical k ∧
    (∀ (edges : Set (Sym2 V)), G.IsCriticalEdges edges → 1 < edges.ncard)) ↔ answer(sorry) := by
  sorry


/--
Dirac's conjecture was proved, for $k=5$: There exists a graph $G$ with chromatic number $5$, such
that every vertex is critical, yet every critical set of edges has size $>1$, or in other words:
has no critical edge.

[Br92] Brown, Jason I., A vertex critical graph without critical edges. Discrete Math. (1992), 99--101
-/
@[category research solved, AMS 11]
theorem erdos_944.variants.one.five : ∃ G : SimpleGraph V, G.IsCritical 5 ∧
    (∀ (edges : Set (Sym2 V)), G.IsCriticalEdges edges → 1 < edges.ncard) := by
  sorry

/--
Lattanzio [La02] proved there exist $k$-critical graphs without critical edges for all $k$ such that
$k - 1$ is not prime.

[La02] Lattanzio, John J., A note on a conjecture of {D}irac. Discrete Math. (2002), 323--330
-/
@[category research solved, AMS 11]
theorem erdos_944.variants.one.not_prime (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime) :
     ∃ (G : SimpleGraph V), G.IsCritical k ∧
    (∀ (edges : Set (Sym2 V)), G.IsCriticalEdges edges → 1 < edges.ncard):= by
  sorry

/--
Jensen [Je02] gave an construction for $k$-critical graphs without any critical edges for all $k≥5$.

[Je02] Jensen, Tommy R., Dense critical and vertex-critical graphs. Discrete Math. (2002), 63--84.
-/
@[category research solved, AMS 11]
theorem erdos_944.variants.one.ge_five (k : ℕ) (hk : 5 ≤ k) :
    ∃ (G : SimpleGraph V), G.IsCritical k ∧
    (∀ (edges : Set (Sym2 V)), G.IsCriticalEdges edges → 1 < edges.ncard):= by
  sorry

/--
The case $k=4$ and $r=1$ remains open: Are there $4$-critical graphs without any critical edges?
-/
@[category research open, AMS 11]
theorem erdos_944 : (∀ k ≥ 4, ∀ r ≥ 1, ∃ (G : SimpleGraph V), G.IsCritical k ∧
    (∀ (edges : Set (Sym2 V)), G.IsCriticalEdges edges → r < edges.ncard)) ↔ answer(sorry) := by
  sorry

/--
Martinsson and Steiner [MaSt25] proved for every $r \ge 1$ if $k$ is sufficiently large, depending
on $r$, there exist a graph $G$ with chromatic number $k$ such that every vertex is critical,
yet every critical set of edges has size $>r$.

[MaSt25] Martinsson, Anders and Steiner, Raphael, Vertex-critical graphs far from edge-criticality. Combin. Probab. Comput. (2025), 151--157
-/
@[category research solved, AMS 11]
theorem erdos_944.variants.depending (r : ℕ) (hr : 1 ≤ r) : ∃ k₀, ∀ k ≥ k₀,
    ∃ (G : SimpleGraph V), G.IsCritical k ∧
    (∀ (edges : Set (Sym2 V)), G.IsCriticalEdges edges → r < edges.ncard) := by
  sorry
