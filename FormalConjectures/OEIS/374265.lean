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
# Minimized zeroless factorials

$a(n)$ is the smallest positive integer obtained by greedily dividing out factors from $n!$
to avoid the digit zero.

*References:*
- [A374265](https://oeis.org/A374265)
-/
open Nat Finset

namespace OeisA374265


-- The function that removes all '0' digits from a number
def remove_zeros (n : ℕ) : ℕ :=
  -- Nat.digits returns the list of digits in reverse order.
  let digits := (Nat.digits 10 n).filter (fun d => d ≠ 0)
  -- Nat.ofDigits interprets the list from most significant digit first if the base is 10
  ofDigits 10 digits

/--
The set of all possible values $f(n)$ resulting from a sequence of choices
where $f(0)=1$ and $f(i) = \operatorname{OpNoz}_i(i \cdot f(i-1))$,
with $\operatorname{OpNoz}_i(x)$ being either $x$ or $remove\_zeros(x)$.
We use `biUnion` for the union of sets.
-/
def reachable_zeroless_factorials : ℕ → Finset ℕ
  | 0 => {1}
  | n + 1 =>
    let prev_set := reachable_zeroless_factorials n
    prev_set.biUnion fun m =>
      let prod := (n + 1) * m
      {prod, remove_zeros prod}

-- The set of reachable values is always nonempty.
@[category API, AMS 11]
lemma reachable_nonempty (n : ℕ) : (reachable_zeroless_factorials n).Nonempty := by
  induction n with
  | zero => exact Finset.singleton_nonempty 1
  | succ n ih =>
    rcases ih with ⟨m, hm⟩ -- Get a guaranteed element m from the previous set
    let prod := (n + 1) * m
    -- We show that `prod` is an element of the current set using `mem_biUnion`.
    -- prod is in {prod, ...} and m is in the previous set, so prod is in the overall union.
    exact ⟨prod, Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_insert_self prod _⟩⟩

/--
The minimized zeroless factorial function $a(n)$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  (reachable_zeroless_factorials n).min' (reachable_nonempty n)

/--
Conjecture from OEIS a: Is this sequence bounded?
Formalization of the affirmative claim: The sequence `a` is bounded.
The sequence $a(n)$ is bounded if there exists an upper bound $B$ in $\mathbb{N}$
such that $a(n) \leq B$ for all $n$.
-/
@[category research open, AMS 11]
theorem conjecture : ∃ B : ℕ, ∀ n : ℕ, a n ≤ B := by
  sorry

end OeisA374265
