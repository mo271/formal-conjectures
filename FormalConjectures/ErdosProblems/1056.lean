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
# Erdős Problem 1056

*Reference:* [erdosproblems.com/1056](https://www.erdosproblems.com/1056)
-/

namespace Erdos1056

/--
Checks if the modular product of each interval equals 1 modulo the prime p,
where intervals are defined by consecutive boundaries.
-/
def Erdos1056For (p : ℕ) (boundaries : List ℕ) : Prop :=
  p.Prime ∧
  boundaries.length ≥ 2 ∧
  StrictMono (fun i => boundaries.get i) ∧
  ∀ i : Fin (boundaries.length - 1),
    (∏ n ∈ (Finset.Ico boundaries[i.val] boundaries[i.val + 1]), n) ≡ 1 [MOD p]

/--
Let $k ≥ 2$. Does there exist a prime $p$ and consecutive intervals $I_0,\dots,I_k$
such that $\prod\limits_{n{\in}I_i}n \equiv 1 [mod~n]$ for all $1 \le i \le k$?
-/
@[category research open, AMS 11]
theorem erdos_1056 :
    (∀ k ≥ 2, ∃ (p : ℕ) (boundaries : List ℕ) (_ : boundaries.length = k + 1),
    Erdos1056For p boundaries)
  ↔ answer(sorry) := by
  sorry

/--
This is problem A15 in Guy's collection [Gu04], where he reports that in a letter in 1979
Erdős observed that $3 * 4 \equiv 5 * 6 * 7 \equiv 1~[mod~11]$.
-/
@[category research solved, AMS 11]
theorem erdos_1056_k2 :
    Erdos1056For 11 [3, 5, 8] := by
  unfold Erdos1056For
  decide

/--
Makowski [Ma83] found, for $k=3$:
$2 * 3 * 4 * 5 \equiv 6 * 7 * 8 * 9 * 10 * 11 \equiv 12 * 13 * 14 * 15 \equiv 1~[mod~17]$.
-/
@[category research solved, AMS 11]
theorem erdos_1056_k3 :
    Erdos1056For 17 [2, 6, 12, 16] := by
  unfold Erdos1056For
  decide

/--
Noll and Simmons asked, more generally, whether there are solutions to
$q_1! \equiv \dots \equiv q_k!~[mod~p]$ for arbitrarily large $k$ (with $q_1 < \dots <q_k$).
-/
@[category research open, AMS 11]
theorem noll_simmons :
    (∀ k ≥ 2,
    ∃ (p : ℕ) (_ : p.Prime) (Q : List ℕ) (_ : Q.length = k) (_ : StrictMono (fun i => Q.get i)),
    p.Prime ∧ StrictMono (fun i => Q.get i) ∧
    ∀ i j : Fin k, Q[i.val]! ≡ Q[j.val]! [MOD p]) ↔ answer(sorry) := by
  sorry

end Erdos1056
