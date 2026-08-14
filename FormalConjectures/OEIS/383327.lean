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
# Multiplicities in bitwise modular sum sequence A049802

$a(n)$ is the number of occurrences of $n$ in the sequence A049802.

*References:*
- [A383327](https://oeis.org/A383327)
-/
open Nat

namespace OeisA383327


/--
The number of occurrences of $n$ in A049802.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- Define the auxiliary sequence A049802 locally.
    let A049802_val (m : ℕ) : ℕ :=
      let r := Nat.log 2 m
      -- Sum over k=1 to r. We use index i in {0, ..., r-1} such that k = i+1.
      (Finset.range r).sum (fun i => m % (2 ^ (i + 1)))

    -- Since $A049802(m) = n$ implies $m < 2^{n+1}$, we use $B = 2^{n+1}$ as a sufficient search bound.
    let B : ℕ := 2 ^ (n + 1)
    Finset.card (Finset.filter (fun m => A049802_val m = n) (Finset.range B))


@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by rfl
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by rfl
@[category test, AMS 11]
theorem a_4 : a 4 = 4 := by rfl

/--
Conjecture based on OEIS a comment:
From a combinatorial perspective, the tuple of summands (x_1, ..., x_t) mentioned above can be seen as a set of t counters, where the j-th counter cycles through 0 to 2^j-1. The natural question 'which m in A049802 appear k times?' becomes a question about how this cycling condition restricts the number of tuples which sum to m. For example, for n <= 100, when n = 1, 3, 5, 9, 15, 23, 35, 63, 65, and 67 there is only one m such that the tuple of summands sums to n (a trivial tuple consisting of n 1s, trivial because there is such a tuple for every n >= 1, i.e. for every m = 2^n+1).
This is a precise statement about the set of values $n$ for which $a(n) = 1$ among $n \le 100$.
-/
@[category research open, AMS 11]
theorem single_occurrence_values_le_100 :
  let S : Finset ℕ := {1, 3, 5, 9, 15, 23, 35, 63, 65, 67}
  ∀ n : ℕ, n ∈ S → a n = 1 :=
by sorry

end OeisA383327
