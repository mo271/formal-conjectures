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

import FormalConjectures.Util.ProblemImports

/-!
# Permutation of natural numbers with prime run length 2

A280864 is the lexicographically earliest sequence of distinct terms such that, for any prime $p$,
any run of consecutive multiples of $p$ has length exactly 2.

The main conjecture states that every positive integer appears in the sequence, making it a
permutation of the positive integers. N. J. A. Sloane established that the sequence contains every
prime and every even number, and showed that to prove the main conjecture it suffices to show that
it contains every odd number (or even just every odd square).

*References:*
- [A280864](https://oeis.org/A280864)
- [N. J. A. Sloane, *Properties of A280864*, 2017](https://oeis.org/A280864/a280864_5.txt)
-/

namespace OeisA280864

/-- Divides `n` by `d` as many times as possible using fuel. -/
def removeFactor (n d fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => n
  | fuel' + 1 =>
    if d < 2 then n
    else if n % d = 0 then removeFactor (n / d) d fuel'
    else n

/-- Computes the radical of `n` using trial division with fuel. -/
def radLoop (n cur fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => 1
  | fuel' + 1 =>
    if n < 2 then
      1
    else if cur * cur > n then
      n
    else if n % cur = 0 then
      cur * radLoop (removeFactor n cur n) (cur + 1) fuel'
    else
      radLoop n (cur + 1) fuel'

/-- The radical (square-free part) of `n`. -/
def rad (n : ℕ) : ℕ := if n = 0 then 0 else radLoop n 2 n

/-- Computes the greatest common divisor of `a` and `b` using structural recursion on fuel. -/
def gcdAux (a b fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => a
  | fuel' + 1 =>
    if b = 0 then a else gcdAux b (a % b) fuel'

/-- Kernel-computable gcd function. -/
def gcd (a b : ℕ) : ℕ := gcdAux a b (a + b + 1)

/-- Helper function to find the smallest multiple of `mandatory` not in `history`
and coprime to `forbidden`. -/
def findCandidate (mandatory forbidden : ℕ) (history : List ℕ) (cur fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => cur
  | fuel' + 1 =>
    if cur ∈ history ∨ gcd cur forbidden > 1 then
      findCandidate mandatory forbidden history (cur + mandatory) fuel'
    else
      cur

/-- Generates the first `n` terms of A280864 in reverse order.
As noted in Sloane's Remark 1.6.1, a guaranteed upper bound for the next term `a(n+1)`
is given by $\pi \cdot \text{mandatory}$, where $\pi$ is the smallest prime not dividing
any of $a(1), \dots, a(n)$. By Euclid's theorem, $\pi \leq \prod_{k=1}^n a(k) + 1$.
Thus, the number of multiples of `mandatory` that need to be tested is at most
$\prod_{k=1}^n a(k) + 1$. We use `hist.prod + 2` as the mathematically rigorous fuel,
ensuring both clean structural recursion and absolute mathematical correctness for proofs. -/
def aList : ℕ → List ℕ
  | 0 => []
  | n + 1 =>
    let hist := aList n
    let p := match hist with
      | [] => 1
      | x :: _ => rad x
    let pp := match hist with
      | [] => 1
      | _ :: [] => 1
      | _ :: y :: _ => rad y
    let forbidden := gcd p pp
    let mandatory := p / forbidden
    let next := findCandidate mandatory forbidden hist mandatory (hist.prod + 2)
    next :: hist

/-- The `n`-th term of A280864 (1-indexed). -/
def a (n : ℕ) : ℕ := match aList n with
  | [] => 0
  | x :: _ => x

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 4 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 6 := by rfl

@[category test, AMS 11]
theorem a_6 : a 6 = 8 := by rfl

@[category test, AMS 11]
theorem a_7 : a 7 = 5 := by rfl

@[category test, AMS 11]
theorem a_8 : a 8 = 10 := by rfl

@[category test, AMS 11]
theorem a_9 : a 9 = 12 := by rfl

@[category test, AMS 11]
theorem a_10 : a 10 = 9 := by rfl

@[category test, AMS 11]
theorem a_42 : a 42 = 55 := by rfl

/--
**Conjecture (A280864)**: Every positive integer appears in the sequence A280864.
-/
@[category research open, AMS 11]
theorem conjecture (m : ℕ) (hm : 0 < m) : ∃ n : ℕ, a n = m := by
  sorry

/--
**Variant 1**: The sequence contains every odd number. As shown by N. J. A. Sloane,
this is sufficient to prove that the sequence contains all positive integers.
-/
@[category research open, AMS 11]
theorem conjecture.variants.odd_numbers (m : ℕ) (hm : Odd m) : ∃ n : ℕ, a n = m := by
  sorry

/--
**Variant 2**: The sequence contains every odd square. As shown by N. J. A. Sloane,
this is also sufficient to prove that the sequence contains all positive integers.
-/
@[category research open, AMS 11]
theorem conjecture.variants.odd_squares (m : ℕ) (hm : Odd m) : ∃ n : ℕ, a n = m ^ 2 := by
  sorry

/--
**Variant 3**: The sequence contains infinitely many powers of 2 that are preceded by even numbers.
As shown by N. J. A. Sloane, this is also sufficient to prove the main conjecture.
-/
@[category research open, AMS 11]
theorem conjecture.variants.powers_of_two (k : ℕ) :
    ∃ n > k, ∃ r : ℕ, a n = 2 ^ r ∧ Even (a (n - 1)) := by
  sorry

/--
**Variant 4**: If a prime $p$ divides $a(n)$ (for $n > 0$), then $p \leq n$.
Conjectured by N. J. A. Sloane (Apr 07 2017 and Apr 16 2017).
-/
@[category research open, AMS 11]
theorem conjecture.variants.prime_divisors_bounded (n p : ℕ) (hn : 0 < n) (hp : p.Prime)
    (hdvd : p ∣ a n) : p ≤ n := by
  sorry

/--
**Solved Variant 1**: The sequence contains every even number $m > 0$.
Proved by N. J. A. Sloane (2017).
-/
@[category research solved, AMS 11]
theorem conjecture.variants.even_numbers (m : ℕ) (hm_pos : 0 < m) (hm : Even m) :
    ∃ n : ℕ, a n = m := by
  sorry

/--
**Solved Variant 2**: The sequence contains every prime number.
Proved by N. J. A. Sloane (2017).
-/
@[category research solved, AMS 11]
theorem conjecture.variants.primes (p : ℕ) (hp : p.Prime) : ∃ n : ℕ, a n = p := by
  sorry

end OeisA280864
