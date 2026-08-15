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

public import Mathlib.Tactic.Linter.Header

/-! # The Opaque Linter

The `OpaqueLinter` is a linter to ensure that no `opaque` definitions are introduced in the repository.
-/

public meta section

open Lean Elab Meta Linter Command Parser Term

register_option linter.style.opaque_decl : Bool := {
  defValue := false
  descr := "enable the linter to forbid opaque declarations"
}

namespace OpaqueLinter

/-- The opaque linter checks that no `opaque` definitions are present. -/
def opaqueLinter : Linter where
  run := withSetOptionIn fun stx => do
    if stx.getKind == ``Lean.Parser.Command.declaration && stx[1].getKind == ``Lean.Parser.Command.opaque then
      logLintIf linter.style.opaque_decl stx
        "Placeholder definitions (e.g., `opaque foo : Type*`) are not allowed."
    return

initialize do
  addLinter opaqueLinter

end OpaqueLinter
