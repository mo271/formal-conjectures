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
# OEIS A378143

$a(n)$ is the smallest prime of the form $(2p)^{2^n} + 1$ for some prime $p$.

The conjecture is equivalent to the claim that a(n) is not 10^(2^n) + 1 for any n,
which in turn is equivalent to the claim that, if 10^(2^n) + 1 is prime,
then either 4^(2^n) + 1 or 6^(2^n) + 1 is prime. - Charles R Greathouse IV, Nov 17 2024

*References:*
- [A378143](https://oeis.org/A378143)
-/
open Nat Set

namespace OeisA378143


/--
a: $a(n)$ is the smallest prime of the form $(2p)^{2^n} + 1$ for some prime $p$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { k : ℕ | Nat.Prime k ∧ ∃ p : ℕ, Nat.Prime p ∧ k = (2 * p) ^ (2 ^ n) + 1 }


@[category test, AMS 11]
theorem a_0 : a 0 = 5 := by sorry
@[category test, AMS 11]
theorem a_1 : a 1 = 17 := by sorry
@[category test, AMS 11]
theorem a_2 : a 2 = 257 := by sorry
@[category test, AMS 11]
theorem a_3 : a 3 = 65537 := by sorry

/--
Conjecture 1: The last digit of each value of $a(n)$, where $n \ge 1$, is 7.
-/
@[category research open, AMS 11]
theorem conjecture_1 : ∀ (n : ℕ), 1 ≤ n → a n % 10 = 7 := by
  sorry

/--
Conjecture 2 (Equivalent formulation by Charles R Greathouse IV):
If $10^{2^n} + 1$ is prime, then either $4^{2^n} + 1$ or $6^{2^n} + 1$ is prime.
-/
@[category research open, AMS 11]
theorem conjecture_2 :
  ∀ (n : ℕ),
    Nat.Prime (10 ^ (2 ^ n) + 1) →
      Nat.Prime (4 ^ (2 ^ n) + 1) ∨ Nat.Prime (6 ^ (2 ^ n) + 1) :=
  by sorry

end OeisA378143
