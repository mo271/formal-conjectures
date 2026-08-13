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

open Nat Finset

namespace OeisA369462


/--
a: Number of representations of $12n-1$ as a sum $(p \cdot q + p \cdot r + q \cdot r)$ with three odd primes $p \le q \le r$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if 1 ≤ n then
    let N : ℕ := 12 * n - 1
    -- N is the target number. Since p*q < N, p, q, r are all bounded by N.
    let B := N
    let search_range := range (B + 1)
    let search_space := search_range.product (search_range.product search_range)

    (search_space.filter (fun t : ℕ × ℕ × ℕ =>
      let p := t.fst
      let q := t.snd.fst
      let r := t.snd.snd
      -- 1. All must be odd primes (Prime and not equal to 2)
      p.Prime ∧ p ≠ 2 ∧ q.Prime ∧ q ≠ 2 ∧ r.Prime ∧ r ≠ 2 ∧
      -- 2. Order and sum constraint.
      p ≤ q ∧ q ≤ r ∧ p * q + p * r + q * r = N
    )).card
  else
    0


@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  sorry

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by
  sorry

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by
  sorry

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by
  sorry

/--
Conjecture a: Is there only a finite number of 0's in this sequence?
-/
theorem oeis_369462_conjecture_0 : {n : ℕ | a n = 0}.Finite := by
  sorry

end OeisA369462
