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

-- A standard set of imports for open problems.
import Mathlib
import FormalConjecturesForMathlib
import FormalConjectures.Util.Answer
import FormalConjectures.Util.Linters.AMSLinter
import FormalConjectures.Util.Linters.AnswerLinter
import FormalConjectures.Util.Linters.CategoryLinter
import FormalConjectures.Util.Linters.CopyrightLinter

import Lean.Elab.Tactic
import Lean.Expr

import Lean

public meta section

open Lean Elab

/--
Like `revertAll` (from after lean4#6386), but also returns the user names of the reverted variables.
-/
@[inline] def _root_.Lean.MVarId.revertAllGetNames (mvarId : MVarId) : Tactic.TacticM (MVarId × Array (Option Name)) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `revertAllCore
    let mut fvarIds := #[]
    let mut userNames := #[]
    let ctx ← Lean.MonadLCtx.getLCtx
    for decl in ctx do
      unless decl.isAuxDecl do
        fvarIds := fvarIds.push decl.fvarId
        let name? := if decl.userName.hasMacroScopes then none else some decl.userName
        userNames := userNames.push name?
    let (_, newGoal) ← mvarId.revert fvarIds (preserveOrder := true) (clearAuxDeclsInsteadOfRevert := true)
    return (newGoal, userNames)


/-- Revert all the hypotheses in the local context. This used to exist in
Lean 3. -/
elab "revert_all" : tactic => do
  Tactic.withMainContext do
    let goal ← Tactic.getMainGoal
    let (newGoal, _) ← goal.revertAllGetNames
    Tactic.setGoals [newGoal]


/-- Revert all the hypotheses in the local context and log names of the
hypotheses that are reverted. -/
elab "revert_all_with_logging" : tactic => do
  Tactic.withMainContext do
    let goal ← Tactic.getMainGoal
    let (newGoal, userNames) ← goal.revertAllGetNames
    Lean.logInfo s!"Reverted: {Lean.toJson userNames}"
    Tactic.setGoals [newGoal]


private unsafe def internal_true_if_false_impl.{u} {α : Sort u} (_h : α → False) : α :=
  lcUnreachable

set_option backward.privateInPublic true in
/-- Internal axiom used for disproving. If to disprove some goal, we construct
a proof of its negation, and claim that this proved our original goal using that
axiom.

We provide a runtime implementation to silence errors about noncomputability. -/
@[implemented_by internal_true_if_false_impl]
private axiom internal_true_if_false.{u} {α : Sort u} (h : α → False) : α

set_option backward.privateInPublic true in
private theorem internal_true_if_not {α : Prop} (h : ¬α) : α :=
  internal_true_if_false h

/-- Replace the current goal with its negation.

Note that this uses a false axiom, so should not be used in final proofs. -/
macro "negate_goal" : tactic =>
  `(tactic| (
    revert_all
    first
      | refine @internal_true_if_not ?_ ?_
      | refine @internal_true_if_false ?_ ?_
    try push_neg))
