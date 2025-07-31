/-
Copyright 2025 The Formal Conjectures Authors.

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

import Mathlib.Data.Nat.PrimeFin
import Mathlib
namespace Nat

/--
A natural number $n$ is said to be $k$-full if for every prime factor $p$ of $n$, the $k$-th power
$p^k$ also divides $n$.
-/
def Full (k : ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p^k ∣ n

/--
A [Powerful number](https://en.wikipedia.org/wiki/Powerful_number) is a natural number $n$ where
for every prime divisor $p$, $p^2$ divides $n$.
Powerful numbers are also known as "squareful", "square-full", or "$2$-full".
-/
abbrev Powerful : ℕ → Prop := (2).Full

theorem full_of_succ_full (k : ℕ) (n : ℕ) (h : (k + 1).Full n) : k.Full n := by
  unfold Full at *
  intro hp
  exact fun a ↦ dvd_of_mul_right_dvd (h hp a)

/-- If $n \equiv 2 \pmod{4}$, then $n$ is not powerful -/
theorem not_powerful_of_2mod4 (n : ℕ) (h : n % 4 = 2) : ¬ Powerful n := by
  rw [Powerful, Full]
  push_neg
  use 2
  simp only [mem_primeFactors, prime_two, ne_eq, true_and, reducePow]
  constructor
  · rw [←Nat.div_add_mod n 4, h]
    simp [Nat.dvd_add (dvd_mul_of_dvd_left (show 2 ∣ 4 by decide) (n / 4)) (dvd_refl 2)]
  · intro h
    simp_all [OfNat.zero_ne_ofNat, Nat.dvd_iff_mod_eq_zero.mp h]
