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
# Multiplicities in prime-counting sequence A362965

$a(n)$ is the number of times $n$ appears in the sequence A362965 (the number of primes $\le$ the $n$-th prime power).

*References:*
- [A366833](https://oeis.org/A366833)
-/
open Nat

namespace OeisA366833

/--
Number of times $n$ appears in A362965.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- p_n (1-indexed) is Nat.nth Nat.Prime (n-1) (0-indexed). Since n > 0, n-1 is safe.
    let p_n   : ℕ := Nat.nth Nat.Prime (n - 1)
    -- p_{n+1} is Nat.nth Nat.Prime n
    let p_np1 : ℕ := Nat.nth Nat.Prime n

    -- Count the number of prime powers in the inclusive interval [p_n, p_{n+1}]
    let count_prime_powers : ℕ :=
      Finset.card ((Finset.Icc p_n p_np1).filter IsPrimePow)

    -- Subtracting 1 is safe since both p_n and p_{n+1} are prime powers, giving a count >= 2.
    count_prime_powers - 1


@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  sorry

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  sorry

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  sorry

@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by
  sorry

/--
Conjecture: a(n) can be only 1, 2, or 3 (with the first occurrences of 3 appearing at n = 4, 9, 30, 327 and 3512).
-/
@[category research open, AMS 11]
theorem values_in_one_two_three : ∀ (n : ℕ), 1 ≤ n → a n ∈ ({1, 2, 3} : Finset ℕ) := by
  sorry

end OeisA366833
