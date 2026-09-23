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

public meta import FormalConjecturesUtil.Answer.Explicit
public import Mathlib.Tactic.Lemma

/-! # The Explicit Answer Linter

The `ExplicitAnswerLinter` warns when a filled `answer( )` in a theorem is not explicit in
the sense of `Google.checkExplicitAnswer`. An unfilled `answer(sorry)` is not checked.

The check runs on the elaborated statement. Each warning is placed on the `answer( )`
syntax in the same position, or on the theorem name when the positions cannot be matched.

A theorem whose answer needs a constant outside the default allowlist can name it with
`@[answer_allow c]`.
-/

public meta section

open Lean Elab Meta Linter Command Parser Term Google

register_option linter.style.answer_explicit : Bool := {
  defValue := false
  descr := "enable the linter checking that filled answers are explicit"
}

namespace ExplicitAnswerLinter

/-- The `answer(..)` nodes in `stx`, outermost first, in source order. -/
partial def answerNodes (stx : Syntax) : Array Syntax :=
  let here := if stx.isOfKind ``Google.answer then #[stx] else #[]
  stx.getArgs.foldl (init := here) fun acc arg => acc ++ answerNodes arg

/-- The declaration name that `declId` introduces under the current namespace and
modifiers. -/
def resolveDeclName (mods : TSyntax ``Lean.Parser.Command.declModifiers) (declId : Syntax) :
    CommandElabM Name := do
  let modifiers ← elabModifiers mods
  let (shortName, _) := expandDeclIdCore declId
  let declName ←
    if (`_root_).isPrefixOf shortName then
      pure <| shortName.replacePrefix `_root_ .anonymous
    else
      pure <| (← getCurrNamespace) ++ shortName
  let env ← getEnv
  return if modifiers.isPrivate then mkPrivateName env declName else declName

/-- For each answer in the type of `declName`, in traversal order, the message describing
why it is not explicit, or `none`. -/
def answerProblems (declName : Name) (type : Expr) :
    TermElabM (Array (Option MessageData)) := do
  let allowed := allowedAnswerConstants (← getEnv) declName
  let acc ← IO.mkRef #[]
  forEachAnswer type fun a => do
    if a.hasSorry then
      acc.modify (·.push none)
      return
    let problems ← checkExplicitAnswer declName allowed a
    if problems.isEmpty then
      acc.modify (·.push none)
      return
    let items := MessageData.joinSep (problems.toList.map (m!"\n- " ++ ·)) ""
    let msg ← addMessageContextFull m!"The answer `{a}` is not explicit:{items}"
    acc.modify (·.push (some msg))
  acc.get

/-- The linter checking that filled answers are explicit. -/
def explicitAnswerLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless linter.style.answer_explicit.get (← getOptions) do return
    -- Look through `open ... in` and similar wrappers to the declaration.
    let mut stx := stx
    while stx.isOfKind ``Lean.Parser.Command.in do
      stx := stx[2]
    match stx with
    | `(command| $mods:declModifiers theorem $id:declId $sig:declSig $_:declVal)
    | `(command| $mods:declModifiers lemma $id:declId $sig:declSig $_:declVal) =>
      let declName ← resolveDeclName mods id
      let some info := (← getEnv).findAsync? declName | return
      let problems ← liftTermElabM <| answerProblems declName info.toConstantInfo.type
      let nodes := answerNodes sig.raw
      for i in [0:problems.size] do
        if let some msg := problems[i]! then
          logLintIf linter.style.answer_explicit (nodes[i]?.getD id.raw) msg
    | _ => return

initialize
  addLinter explicitAnswerLinter

end ExplicitAnswerLinter
