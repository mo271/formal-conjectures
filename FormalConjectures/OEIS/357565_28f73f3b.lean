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
# OEIS A357565

$a(n) = 3 \sum_{k = 0}^n \binom{n+k-1}{k}^2 + 2 \sum_{k = 0}^n \binom{n+k-1}{k}^3$.

The generalized sequence $u(n, m)$ from the conjecture section:
$u(n, m) = (m + 2) \sum_{k = 0}^{m \cdot n} \binom{n+k-1}{k}^2 + 2m \sum_{k = 0}^{m \cdot n} \binom{n+k-1}{k}^3$.
Note that $a(n) = a\_u(n, 1)$.

*References:*
- [A357565](https://oeis.org/A357565)
-/
open Finset Nat

namespace OeisA357565


/--
a: $a(n) = 3 \sum_{k = 0}^n \binom{n+k-1}{k}^2 + 2 \sum_{k = 0}^n \binom{n+k-1}{k}^3$.
-/
def a (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k =>
    let b := choose (n + k - 1) k
    3 * b ^ 2 + 2 * b ^ 3

/--
The generalized sequence $u(n, m)$ from the conjecture section:
$u(n, m) = (m + 2) \sum_{k = 0}^{m \cdot n} \binom{n+k-1}{k}^2 + 2m \sum_{k = 0}^{m \cdot n} \binom{n+k-1}{k}^3$.
Note that $a(n) = a\_u(n, 1)$.
-/
def u (n m : ℕ) : ℕ :=
  (range (m * n + 1)).sum fun k =>
    (m + 2) * (choose (n + k - 1) k) ^ 2 + (2 * m) * (choose (n + k - 1) k) ^ 3

-- Formalizing Conjecture 1
/--
Conjecture 1 for a: $a(p) \equiv a(1) \pmod{p^5}$ for all odd primes $p$ except $p = 5$.
-/
@[category research open, AMS 11]
theorem conjecture_1 (p : ℕ) (hp : Nat.Prime p) (h_odd : p % 2 ≠ 0) (h_ne5 : p ≠ 5) :
    (a p) ≡ (a 1) [MOD (p ^ 5)] := by
  sorry

-- Formalizing Conjecture 2
/--
Conjecture 2 for a: $a(p^r) \equiv a(p^{r-1}) \pmod{p^{3r+3}}$ for $r \ge 2$ and all primes $p \ge 3$.
-/
@[category research open, AMS 11]
theorem conjecture_2 (p r : ℕ) (hp : Nat.Prime p) (h_pge3 : p ≥ 3) (hr : r ≥ 2) :
    (a (p ^ r)) ≡ (a (p ^ (r - 1))) [MOD (p ^ (3 * r + 3))] := by
  sorry

-- Formalizing Conjecture 3
/--
Conjecture 3 for generalized sequence $u(n, m)$: $u(p) \equiv u(1) \pmod{p^5}$ holds for all primes $p \ge 7$ and positive integer $m$.
-/
@[category research open, AMS 11]
theorem conjecture_3 (m p : ℕ) (hm : m > 0) (hp : Nat.Prime p) (h_pge7 : p ≥ 7) :
    (u p m) ≡ (u 1 m) [MOD (p ^ 5)] := by
  sorry

-- Formalizing Conjecture 4
/--
Conjecture 4 for generalized sequence $u(n, m)$: $u(p^r) \equiv u(p^{r-1}) \pmod{p^{3r+3}}$ for $r \ge 2$, all primes $p \ge 3$, and all positive integers $m$.
-/
@[category research open, AMS 11]
theorem conjecture_4 (m p r : ℕ) (hm : m > 0) (hp : Nat.Prime p) (h_pge3 : p ≥ 3) (hr : r ≥ 2) :
    (u (p ^ r) m) ≡ (u (p ^ (r - 1)) m) [MOD (p ^ (3 * r + 3))] := by
  sorry

end OeisA357565
