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
# Laurent series power coefficients $[x^n] ((1-x)/(1-x+x^2))^n$

The sequence is defined by $a(n) = [x^n] \left( \frac{1-x}{1-x+x^2} \right)^n$.

*References:*
- [A386548](https://oeis.org/A386548)
-/
open Finset Nat BigOperators Int

namespace OeisA386548


/--
The sequence $a(n) = [x^n] \left( \frac{1-x}{1-x+x^2} \right)^n$.
-/
def a (n : ℕ) : ℤ :=
  Finset.sum (Finset.range (n / 2 + 1))
    (fun k ↦
      let sign : ℤ := if k % 2 = 0 then 1 else -1
      -- Nat.choose handles binomial(n, k) = 0 if k > n due to truncated subtraction on Nat.
      let term1 : ℕ := (n + k - 1).choose k
      let term2 : ℕ := (n - k - 1).choose (n - 2 * k)
      sign * (term1 : ℤ) * (term2 : ℤ))

/--
Conjecture: the stronger supercongruences $a(n \cdot p^k) \equiv a(n \cdot p^{k-1}) \pmod{p^{2k}}$
hold for all primes $p \ge 5$ and all positive integers $n$ and $k$.
-/
@[category research open, AMS 11]
theorem supercongruence :
  ∀ (p : ℕ), Nat.Prime p → p ≥ 5 →
  ∀ (n k : ℕ), n > 0 → k > 0 →
  a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p ^ (2 * k) : ℤ)] :=
by sorry

end OeisA386548
