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
# OEIS A364173

The sequence defined by the factorial ratio
$$a(n) = \frac{(9n)! (2n)! (3n/2)!}{(9n/2)! (4n)! (3n)! n!}$$
where fractional factorials $x!$ are defined as $\Gamma(x+1)$.

Conjecture: the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes p >= 5 and all positive integers n and r.
Note: This conjecture requires that a(n) is an integer for all n, which is only conjectural.
We assume integrality for the purpose of stating the congruence.

*References:*
- [A364173](https://oeis.org/A364173)
-/
open scoped Real

namespace OeisA364173


/--
a: The sequence defined by the factorial ratio
$$a(n) = \frac{(9n)! (2n)! (3n/2)!}{(9n/2)! (4n)! (3n)! n!}$$
where fractional factorials $x!$ are defined as $\Gamma(x+1)$.
-/
noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))


@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by
  sorry

@[category test, AMS 11]
theorem a_1 : a 1 = 128 := by
  sorry

@[category test, AMS 11]
theorem a_2 : a 2 = 43758 := by
  sorry

@[category test, AMS 11]
theorem a_3 : a 3 = 17039360 := by
  sorry

/--
Conjecture: the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes p >= 5 and all positive integers n and r.
Note: This conjecture requires that a(n) is an integer for all n, which is only conjectural.
We assume integrality for the purpose of stating the congruence.
-/
@[category research open, AMS 11]
theorem conjecture
    (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (hn : n > 0) (hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] :=
by sorry

end OeisA364173
