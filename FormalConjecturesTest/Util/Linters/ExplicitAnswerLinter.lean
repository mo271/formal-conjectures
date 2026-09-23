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
module

public meta import FormalConjecturesUtil.Linters.ExplicitAnswerLinter
public import FormalConjecturesUtil

/-!
# Tests for the explicit answer linter

The linter warns on filled answers that are not explicit. The test of
`Google.checkExplicitAnswer` covers the individual rules; this file checks that the linter
finds the answers, skips `answer(sorry)`, and places its warning on the `answer( )` syntax.
-/

@[expose] public section

set_option warn.sorry false

-- Off by default; on here because this file is what tests it.
set_option linter.style.answer_explicit true

namespace ExplicitAnswerLinterTest

#guard_msgs in
theorem not_flagged_true : answer(True) ↔ 1 + 1 = 2 := by
  sorry

#guard_msgs in
theorem not_flagged_sorry_prop : answer(sorry) ↔ 1 + 1 = 2 := by
  sorry

#guard_msgs in
theorem not_flagged_sorry_nat : answer(sorry) = 2 := by
  sorry

#guard_msgs in
theorem not_flagged_literal : (4 : ℕ) = answer(4) := by
  sorry

#guard_msgs in
theorem not_flagged_interval : {n : ℕ | n ≤ 3} = answer(Set.Iic 3) := by
  sorry

#guard_msgs in
theorem not_flagged_limit :
    Filter.Tendsto (fun n : ℕ => (1 : ℝ) / n) Filter.atTop answer(nhds 0) := by
  sorry

#guard_msgs in
theorem not_flagged_let :
    let c : ℕ := answer(5)
    c = 5 := by
  sorry

/--
warning: The answer `1 + 1 = 2` is not explicit:
- an answer of type `Prop` must be `True` or `False`

Note: This linter can be disabled with `set_option linter.style.answer_explicit false`
-/
#guard_msgs in
theorem flagged_restated_prop : answer(1 + 1 = 2) ↔ 1 + 1 = 2 := by
  sorry

/--
warning: The answer `Nat.card { n // n < 3 }` is not explicit:
- `Nat.card` may not appear in an answer

Note: This linter can be disabled with `set_option linter.style.answer_explicit false`
-/
#guard_msgs in
theorem flagged_card : Nat.card {n : ℕ // n < 3} = answer(Nat.card {n : ℕ // n < 3}) := by
  sorry

/--
warning: The answer `if ∀ (n : ℕ), n = n then 1 else 0` is not explicit:
- `Classical.propDecidable` may not appear in an answer

Note: This linter can be disabled with `set_option linter.style.answer_explicit false`
-/
#guard_msgs in
open Classical in
theorem flagged_under_open :
    (if ∀ n : ℕ, n = n then 1 else 0) = answer(if ∀ n : ℕ, n = n then 1 else 0) := by
  sorry

/--
warning: The answer `sInf {n | 1 < n}` is not explicit:
- `InfSet.sInf` may not appear in an answer
- `Set.ofPred` is not in the allowlist of explicit constants

Note: This linter can be disabled with `set_option linter.style.answer_explicit false`
-/
#guard_msgs in
theorem flagged_second_answer : answer(True) ↔ (2 : ℕ) = answer(sInf {n : ℕ | 1 < n}) := by
  sorry

/--
warning: The answer `1 + 1 = 2` is not explicit:
- an answer of type `Prop` must be `True` or `False`

Note: This linter can be disabled with `set_option linter.style.answer_explicit false`
-/
#guard_msgs in
lemma flagged_lemma : answer(1 + 1 = 2) ↔ 1 + 1 = 2 := by
  sorry

#guard_msgs in
set_option linter.style.answer_explicit false in
theorem not_flagged_disabled : answer(1 + 1 = 2) ↔ 1 + 1 = 2 := by
  sorry

end ExplicitAnswerLinterTest
