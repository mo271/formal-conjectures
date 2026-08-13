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

namespace OeisA361715


/--
a: $$a(n) = \sum_{k = 0}^{n-1} \binom{n}{k}^2 \binom{n+k-1}{k}$$
-/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ range n, (n.choose k) ^ 2 * multichoose n k


@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  sorry

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  sorry

@[category test, AMS 11]
theorem a_2 : a 2 = 9 := by
  sorry

@[category test, AMS 11]
theorem a_3 : a 3 = 82 := by
  sorry


/-- Conjecture 2: for r >= 2, the supercongruence a(p^r) == a(p^(r-1)) (mod p^(3*r+3)) holds for all primes p >= 5. -/
@[category research open, AMS 11]
theorem conjecture (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
  (a (p ^ r) : ℤ) ≡ a (p ^ (r - 1)) [ZMOD (p ^ (3 * r + 3) : ℕ)] := by sorry

end OeisA361715
