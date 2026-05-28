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
# The path graph on 5 vertices ($P_5$)

Properties of $P_5$ used as a counterexample for graph conjectures.
-/

namespace MyP5

open SimpleGraph

/--
The path graph on 5 vertices, $P_5$.
-/
def P5 : SimpleGraph (Fin 5) :=
  SimpleGraph.fromEdgeSet {s(0,1), s(1,2), s(2,3), s(3,4)}

/--
Adjacency in $P_5$ is decidable.
-/
instance : DecidableRel P5.Adj := by
  dsimp [P5]
  infer_instance

/--
The average degree of $P_5$ is $8/5$.
-/
@[category test, AMS 5]
lemma P5_avg_deg : averageDegree P5 = 8/5 := by
  unfold averageDegree; decide +native

/--
The number of pendant vertices in $P_5$ is 2.
-/
@[category test, AMS 5]
lemma P5_pendant : (pendantVertices P5).card = 2 := by
  unfold pendantVertices; decide +native

/--
$P_5$ is not well totally dominated.
-/
@[category test, AMS 5]
lemma P5_not_WTD : ¬ IsWellTotallyDominated P5 := by
  unfold IsWellTotallyDominated IsMinimalTotalDominatingSet IsTotalDominatingSet
  push_neg
  use {1, 2, 3}, {0, 1, 3, 4}
  decide +native

/--
$P_5$ satisfies the hypothesis that its average degree is at most the number of its pendant
vertices.
-/
@[category test, AMS 5]
lemma P5_hyp : (averageDegree P5 : ℚ) ≤ (pendantVertices P5).card := by
  rw [P5_avg_deg, P5_pendant]
  norm_num

/--
$P_5$ is a connected graph.
-/
@[category test, AMS 5]
lemma P5_connected : P5.Connected := by
  rw [connected_iff_exists_forall_reachable]
  use 0
  decide +native

end MyP5

export MyP5 (P5 P5_avg_deg P5_pendant P5_not_WTD P5_hyp P5_connected)
