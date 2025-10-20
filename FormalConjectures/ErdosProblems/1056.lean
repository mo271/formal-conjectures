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
Boundaries between k intervals in a sequence.
-/
def boundaries (k : ℕ) : Type :=
  { boundaries : Fin (k + 1) → ℕ // StrictMono boundaries }

/--
Consecutive intervals between boundaries.
-/
def interval (k : ℕ) (ci : boundaries k) (i : Fin k) : Finset ℕ :=
  Finset.Ico (ci.val i.castSucc) (ci.val i.succ)

/--
Product of elements in a set modulo p.
-/
def modProd (p : ℕ) (I : Finset ℕ) : ℕ :=
  (∏ n ∈ I, n) % p

/--
Let $k ≥ 2$. Does there exist a prime $p$ and consecutive intervals $I_0,\dots,I_k$
such that $\prod\limits_{n{\in}I_i}n\equiv1 [mod n]$ for all $1 \le i \le k$?-/
@[category research open, AMS 11]
theorem erdos_1056 :
  ∀ k ≥ 2, ∃ (p : ℕ) (hp : p.Prime) (ci : boundaries k),
    ∀ i : Fin k, modProd p (interval k ci i) = 1 ↔ answer(sorry) := by
  sorry

end Erdos1056
