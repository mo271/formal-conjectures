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
# Numbers whose prime divisors all end in the same digit

Sequence of natural numbers whose prime divisors all end in the same decimal digit (also called "lopsided" numbers).

*References:*
- [A381159](https://oeis.org/A381159)
-/
open Nat

namespace OeisA381159


/--
Numbers whose prime divisors all end in the same digit.
-/
def condition (n : ℕ) : Prop :=
  Finset.card (n.primeFactors.image (fun p => p % 10)) ≤ 1

/--
Natural numbers whose prime divisors all end in the same decimal digit.
-/
noncomputable def a (n : ℕ) : ℕ := n.nth condition


@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  norm_num [ a]
  rewrite [Nat.nth_eq_sInf]
  norm_num [ condition]
  refine IsLeast.csInf_eq ⟨ (by exists (by ·norm_num)), fun and => And.right⟩

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  norm_num[a]
  borelize Real
  delta condition
  use(((congr_arg _)) ? _).trans (Nat.nth_count (by bound))
  norm_num[ Finset.sum,Nat.count_succ]

@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by
  norm_num [a]
  nontriviality
  delta condition
  use(congr_arg _ ? _).trans (Nat.nth_count (by bound))
  norm_num[Nat.count_succ]

@[category test, AMS 11]
theorem a_4 : a 4 = 4 := by
  norm_num[a]
  inhabit ℝ
  delta condition
  use(4).nth_count (by norm_num[Nat.primeFactors,Nat.primeFactorsList])|>.subst ((congr_arg _) @? _)
  norm_num[Nat.count_succ]


/--
a 51st All-Russian Mathematical Olympiad for Schoolchildren. Problem.
Let us call a natural number "lopsided" if it is greater than 1 and all its prime divisors end with the same digit.
Is there an increasing arithmetic progression with a difference not exceeding 2025,
consisting of 150 natural numbers, each of which is "lopsided"? (A. Chironov)
-/
@[category textbook, AMS 11]
theorem conjecture :
  answer(sorry) ↔
  ∃ (a d : ℕ),
    2 ≤ a ∧ -- The starting number 'a' must be lopsided, hence > 1. All subsequent terms will also be > 1.
    1 ≤ d ∧ -- 'd' must be positive for an increasing arithmetic progression
    d ≤ 2025 ∧ -- difference not exceeding 2025
    ∀ (i : Fin 150), condition (a + i.val * d) := by
  sorry

end OeisA381159
