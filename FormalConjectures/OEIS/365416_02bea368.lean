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
# OEIS A365416

a According to Pillai's conjecture, k = 13 is the only term such that 2*k-1 and 2*k+1 both have exponent greater than 1.

*References:*
- [A365416](https://oeis.org/A365416)
-/
open Nat

namespace OeisA365416


/--
Numbers $k$ such that $2k-1$ and $2k+1$ are both prime powers (A246655).
-/
def condition (k : ℕ) : Prop :=
  IsPrimePow (2 * k - 1) ∧ IsPrimePow (2 * k + 1)

/--
The $n$-th term of a (Numbers $k$ such that $2k-1$ and $2k+1$ are both prime powers).
Defined for $n \ge 1$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (n - 1).nth condition


@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  sorry

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by
  sorry

@[category test, AMS 11]
theorem a_3 : a 3 = 4 := by
  sorry

@[category test, AMS 11]
theorem a_4 : a 4 = 5 := by
  sorry

-- Formalization of the conjecture

/--
Predicate for a number to be a prime power with exponent strictly greater than 1.
This is equivalent to being a composite prime power (a perfect power whose base is prime).
-/
def IsCompositePrimePow (m : ℕ) : Prop :=
  ∃ (p e : ℕ), Nat.Prime p ∧ 1 < e ∧ p ^ e = m

/--
a According to Pillai's conjecture, k = 13 is the only term such that 2*k-1 and 2*k+1 both have exponent greater than 1.
-/
@[category research open, AMS 11]
theorem conjecture :
  ∀ k : ℕ,
    (IsCompositePrimePow (2 * k - 1) ∧ IsCompositePrimePow (2 * k + 1)) ↔ k = 13 :=
by sorry

end OeisA365416
