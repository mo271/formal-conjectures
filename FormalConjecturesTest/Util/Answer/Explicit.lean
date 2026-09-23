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

public import FormalConjecturesUtil

/-!
# Tests for explicit answers

This file tests `Google.checkExplicitAnswer` and the `answer_allow` attribute. The
`ExplicitAnswerLinter` test covers the same check through the linter.
-/

@[expose] public section

set_option warn.sorry false

open Lean Meta Elab Command Google

namespace ExplicitAnswerTest

-- Every name in the allowlist and in the forbidden list is a constant.
#guard_msgs in
run_cmd do
  let env ← getEnv
  for n in explicitConstants.toList ++ forbiddenConstants.toList do
    unless env.contains n do logError m!"unknown constant {n}"

/-- Runs the check on every answer in the statement of `declName` and reports the result. -/
meta def checkAll (declName : Name) : CommandElabM Unit := liftTermElabM do
  let some info := (← getEnv).find? declName | throwError "unknown declaration {declName}"
  forEachAnswer info.type fun a => do
    let problems ← checkExplicitAnswer declName (allowedAnswerConstants (← getEnv) declName) a
    logInfo m!"{problems}"

theorem prop_true : answer(True) ↔ 1 + 1 = 2 := by
  sorry

/-- info: [] -/
#guard_msgs in
run_cmd checkAll ``prop_true

theorem prop_restated : answer(1 + 1 = 2) ↔ 1 + 1 = 2 := by
  sorry

/-- info: [an answer of type `Prop` must be `True` or `False`] -/
#guard_msgs in
run_cmd checkAll ``prop_restated

def Shadow.True : Prop := 1 = 2

namespace Shadow

theorem prop_shadowed : answer(True) ↔ 1 = 2 := by
  sorry

end Shadow

-- The check looks at the elaborated constant, so a namespace cannot disguise a term.
/--
info: [an answer of type `Prop` must be `True` or `False`, but this term is the constant `ExplicitAnswerTest.Shadow.True`]
-/
#guard_msgs in
run_cmd checkAll ``Shadow.prop_shadowed

theorem nat_literal : (2 : ℕ) ^ 2 ^ 100 = answer(2 ^ 2 ^ 100) := by
  sorry

/-- info: [] -/
#guard_msgs in
run_cmd checkAll ``nat_literal

theorem real_closed_form : (1 : ℝ) / 2 + Real.sqrt 2 = answer(1 / 2 + Real.sqrt 2) := by
  sorry

/-- info: [] -/
#guard_msgs in
run_cmd checkAll ``real_closed_form

/-- An answer may depend on the binders of the statement. -/
theorem piecewise : ∀ n : ℕ, n.choose 2 = answer(if n ≤ 1 then 0 else n * (n - 1) / 2) := by
  sorry

/-- info: [] -/
#guard_msgs in
run_cmd checkAll ``piecewise

theorem least_by_specification : IsLeast {n : ℕ | 3 < n} answer(sInf {n : ℕ | 3 < n}) := by
  sorry

/--
info: [`InfSet.sInf` may not appear in an answer, `Set.ofPred` is not in the allowlist of explicit constants]
-/
#guard_msgs in
run_cmd checkAll ``least_by_specification

theorem least_by_find (h : ∃ n : ℕ, 3 < n) : IsLeast {n : ℕ | 3 < n} answer(Nat.find h) := by
  sorry

/-- info: [`Nat.find` may not appear in an answer] -/
#guard_msgs in
run_cmd checkAll ``least_by_find

open Classical in
theorem classical_branch :
    (if ∀ n : ℕ, n = n then 1 else 0) = answer(if ∀ n : ℕ, n = n then 1 else 0) := by
  sorry

/-- info: [`Classical.propDecidable` may not appear in an answer] -/
#guard_msgs in
run_cmd checkAll ``classical_branch

theorem real_branch (x : ℝ) : (if x < 1 then 0 else 1 : ℝ) = answer(if x < 1 then 0 else 1) := by
  sorry

/-- info: [the `Decidable` instance `Real.decidableLT` is noncomputable] -/
#guard_msgs in
run_cmd checkAll ``real_branch

/-- A hand-written instance is not exempt from the allowlist. -/
theorem forged_instance : (3 : ℕ) = answer(@HAdd.hAdd ℕ ℕ ℕ ⟨fun _ _ => 3⟩ 1 1) := by
  sorry

/-- info: [`HAdd.mk` is not in the allowlist of explicit constants] -/
#guard_msgs in
run_cmd checkAll ``forged_instance

noncomputable def hidden : ℕ := sInf {n : ℕ | 3 < n}

theorem local_definition : IsLeast {n : ℕ | 3 < n} answer(hidden) := by
  sorry

/--
info: [`ExplicitAnswerTest.hidden` is defined in the same file as the problem; add `@[answer_allow ExplicitAnswerTest.hidden]` to the theorem if it is part of the intended answer]
-/
#guard_msgs in
run_cmd checkAll ``local_definition

@[answer_allow hidden]
theorem local_definition_allowed : IsLeast {n : ℕ | 3 < n} answer(hidden) := by
  sorry

/-- info: [] -/
#guard_msgs in
run_cmd checkAll ``local_definition_allowed

@[answer_allow Set.ofPred]
theorem set_builder_allowed : {n : ℕ | n % 2 = 1} = answer({n : ℕ | n % 2 = 1}) := by
  sorry

/-- info: [] -/
#guard_msgs in
run_cmd checkAll ``set_builder_allowed

/-- error: `Nat.find` may not appear in an answer -/
#guard_msgs in
@[answer_allow Nat.find]
theorem forbidden_allowance (h : ∃ n : ℕ, 3 < n) : IsLeast {n : ℕ | 3 < n} answer(Nat.find h) := by
  sorry

/-- error: `Classical.choice` may not appear in an answer -/
#guard_msgs in
@[answer_allow Classical.choice]
theorem axiom_allowance : (1 : ℕ) = answer(1) := by
  sorry

/-- The proof inside a subtype value is not inspected. -/
theorem subtype_value : (⟨3, by norm_num⟩ : {n : ℕ // 2 < n}) = answer(⟨3, by norm_num⟩) := by
  sorry

/-- info: [] -/
#guard_msgs in
run_cmd checkAll ``subtype_value

theorem two_answers : answer(True) ↔ (2 : ℕ) = answer(sInf {n : ℕ | 1 < n}) := by
  sorry

/--
info: []
---
info: [`InfSet.sInf` may not appear in an answer, `Set.ofPred` is not in the allowlist of explicit constants]
-/
#guard_msgs in
run_cmd checkAll ``two_answers

end ExplicitAnswerTest
