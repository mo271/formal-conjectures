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
# OEIS A358684

$a(n)$ is the minimum integer $k$ such that the smallest prime factor of the $n$-th Fermat number exceeds $2^{2^n - k}$.
Let $F_n = 2^{2^n} + 1$ be the $n$-th Fermat number, and $P_n$ be its smallest prime factor.
The definition of $a(n)$ is equivalent to the closed form:
$$a(n) = 2^n - \lfloor \log_2(P_n) \rfloor$$
where $P_n = \operatorname{minFac}(\operatorname{fermatNumber} n)$.
The subtraction is defined in $\mathbb{N}$ and is safe since $P_n \le F_n$, implying $\log_2 P_n < 2^n$.

*References:*
- [A358684](https://oeis.org/A358684)
-/
open Nat Asymptotics Filter

namespace OeisA358684

/--
a: $a(n)$ is the minimum integer $k$ such that the smallest prime factor of the $n$-th Fermat number exceeds $2^{2^n - k}$.
Let $F_n = 2^{2^n} + 1$ be the $n$-th Fermat number, and $P_n$ be its smallest prime factor.
The definition of $a(n)$ is equivalent to the closed form:
$$a(n) = 2^n - \lfloor \log_2(P_n) \rfloor$$
where $P_n = \operatorname{minFac}(\operatorname{fermatNumber} n)$.
-/
def a (n : ℕ) : ℕ :=
  let pn := minFac (fermatNumber n)
  (2 ^ n) - (log2 pn)

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by sorry

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by sorry

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by sorry

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by sorry

/--
Conjecture I: The dyadic valuation of $\operatorname{minFac}(F_n) - 1$ does not exceed $2^n - a(n)$.
Note: Proved by AlphaProof using the inequality $\nu_2(k-1) \le \lfloor \log_2 k \rfloor$.
-/
@[category research solved, AMS 11]
theorem conjecture_1 (n : ℕ) :
    padicValNat 2 (minFac (fermatNumber n) - 1) ≤ 2 ^ n - a n := by
  sorry

/--
Conjecture II: $a(n) \sim 2^n$ as $n \to \infty$.
-/
@[category research open, AMS 11]
theorem conjecture_2 :
    (fun n ↦ (a n : ℝ)) ~[atTop] (fun n ↦ ((2 ^ n : ℕ) : ℝ)) := by
  sorry

end OeisA358684
