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
module

public import FormalConjecturesUtil.Attributes.Basic
public import FormalConjecturesUtil.Linters.Util
public import Mathlib.Tactic.Lemma

/-! # The Question Linter

The `QuestionLinter` ensures that the `question` attribute is not forgotten on a value question:
a theorem whose statement refers to its own unknown `<theorem>.answer` must carry
`@[question value]`. The attribute itself checks the converse, that a tagged theorem does refer
to its unknown.
-/

public meta section

open Lean Elab Meta Linter Command Parser Term ProblemAttributes

register_option linter.style.question_attribute : Bool := {
  defValue := false
  descr := "enable the linter checking that a value question carries `question value`"
}

namespace QuestionLinter

/-- Warns when the statement of the theorem `declName` refers to `declName.answer` but the
theorem is not tagged `@[question value]`. -/
def checkValueQuestionTagged (declName : Name) (declId : Syntax) : CommandElabM Unit := do
  let some info := (← getEnv).find? declName | return
  unless info.type.getUsedConstants.contains (declName ++ `answer) do return
  unless (← getQuestionKind? declName) == some .value do
    logLintIf linter.style.question_attribute declId
      m!"The statement refers to its unknown `{declName ++ `answer}`, so it asks for a value; \
        tag the theorem `@[question value]`."

/-- The question linter checks that a theorem using its `answer` definition is tagged
`@[question value]`. -/
def questionLinter : Linter where
  run := withSetOptionIn fun stx => do
    match stx with
    | `(command| $mods:declModifiers theorem $declId:declId $_:declSig $_:declVal)
    | `(command| $mods:declModifiers lemma $declId:declId $_:declSig $_:declVal) =>
      checkValueQuestionTagged (← FormalConjectures.Linter.resolveDeclName mods declId) declId
    | _ => return

initialize do
  addLinter questionLinter

end QuestionLinter
