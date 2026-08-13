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
# OEIS A389790

$a(n)$ is the number of ways to write $2n$ as $p + p' + q + q'$, where $p$ and $q$ are primes with
$p \le q$, and $r'$ is the first prime greater than $r$.

*References:*
- [A389790](https://oeis.org/A389790)
-/

open Nat

namespace OeisA389790

/-- The smallest prime strictly greater than $r$. Defined non-computably using the set infimum. -/
noncomputable def next_prime (r : ℕ) : ℕ :=
  sInf {k : ℕ | Nat.Prime k ∧ r < k}

/-- $r + r'$, where $r'$ is the next prime after $r$. -/
noncomputable def S_sum (r : ℕ) : ℕ := r + next_prime r

/--
Number of ways to write $2n$ as $p + p' + q + q'$, where $p$ and $q$ are primes with $p \le q$,
and $r'$ is the first prime greater than $r$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let target := 2 * n
  let R := Finset.range n
  Finset.card $ Finset.filter (fun ⟨p, q⟩ =>
    Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ S_sum p + S_sum q = target
  ) (R ×ˢ R)

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by sorry

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by sorry

/--
Conjecture 1: $a(n) > 0$ for all $n \ge 474$.
This is an analog of Goldbach's conjecture.
-/
@[category research open, AMS 11]
theorem conjecture_1 : ∀ n : ℕ, 474 ≤ n → 0 < a n := by
  sorry

/-- The statement that $n_{max}$ is the conjectured largest value of $n$ such that $a(n) = k$. -/
def is_conjectured_largest_value (n_max k : ℕ) : Prop :=
  a n_max = k ∧ ∀ n > n_max, a n ≠ k

/--
Conjecture 2: $a(n) = k$ for a largest value of $n$ given by the table:
$k=2 \implies 833$, $k=3 \implies 1487$, $k=4 \implies 1411$, $k=5 \implies 1523$,
$k=6 \implies 1747$, $k=7 \implies 2621$, $k=8 \implies 2153$, $k=9 \implies 3091$,
$k=10 \implies 3238$.
-/
@[category research open, AMS 11]
theorem conjecture_2 :
    is_conjectured_largest_value 833 2 ∧
    is_conjectured_largest_value 1487 3 ∧
    is_conjectured_largest_value 1411 4 ∧
    is_conjectured_largest_value 1523 5 ∧
    is_conjectured_largest_value 1747 6 ∧
    is_conjectured_largest_value 2621 7 ∧
    is_conjectured_largest_value 2153 8 ∧
    is_conjectured_largest_value 3091 9 ∧
    is_conjectured_largest_value 3238 10 := by
  sorry

end OeisA389790
