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

public import Lean
public import FormalConjecturesUtil.Answer.Explicit

/-!
# Check answers

This script reports every `answer( )` in the theorems of the given modules, and whether
its filled value is explicit in the sense of `Google.checkExplicitAnswer`.

### Usage
```bash
lake build FormalConjecturesAnswerPostpone
lake exe check_answers FormalConjectures.ErdosProblems.«1047» [--allow-file=challenge.json]
```

Build with `FormalConjecturesAnswerPostpone` first. Under the default `google.answer`
setting an unfilled `answer(sorry)` of type `Prop` elaborates to a bare `True`, which this
script cannot see. A module name and a file path under `FormalConjectures/` are both
accepted.

The output is a JSON array with one object per theorem that contains an answer:
```json
{"theorem": "Erdos1047.erdos_1047", "module": "FormalConjectures.ErdosProblems.«1047»",
 "allowed": [],
 "answers": [{"index": 0, "type": "ℕ", "term": "...", "filled": true, "explicit": true,
              "problems": []}]}
```
The exit code is 1 when a filled answer is not explicit.

### Use by a comparator
Run the script on the challenge build and on the solution build. For each theorem the
`answers` arrays must have the same length, and every solution answer must be `filled` and
`explicit`. Pass the challenge output to the solution run with `--allow-file`, so that the
allowances come from the challenge and the solution cannot grant itself extra constants. A
constant that is allowed and defined in the problem's own module must also be compared
between the two builds, since the check does not unfold it.
-/

@[expose] public meta section

open Lean Meta Google

/-- The module name of a file under `FormalConjectures/`, or the name itself. -/
def toModuleName (arg : String) : IO Name := do
  if !arg.endsWith ".lean" then
    return arg.toName
  let components := (System.FilePath.mk arg).withExtension "" |>.components
  let some start := components.findIdx? (· == "FormalConjectures")
    | throw <| IO.userError s!"Could not determine the module name of {arg}."
  return (components.drop start).foldl Name.mkStr .anonymous

/-- The per-theorem allowances recorded in the output of an earlier run. -/
def readAllowFile (path : String) : IO (Std.HashMap String (Array Name)) := do
  let contents ← IO.FS.readFile path
  let json ← IO.ofExcept (Json.parse contents)
  let entries ← IO.ofExcept json.getArr?
  let mut map := {}
  for entry in entries do
    let thm ← IO.ofExcept (entry.getObjValAs? String "theorem")
    let allowed ← IO.ofExcept (entry.getObjValAs? (Array String) "allowed")
    map := map.insert thm (allowed.map String.toName)
  return map

/-- One `answer( )` in a statement and the result of the check. -/
structure AnswerReport where
  index : Nat
  type : String
  term : String
  filled : Bool
  explicit : Bool
  problems : Array String

def AnswerReport.toJson (r : AnswerReport) : Json :=
  Json.mkObj [("index", Lean.toJson r.index), ("type", Lean.toJson r.type),
    ("term", Lean.toJson r.term), ("filled", Lean.toJson r.filled),
    ("explicit", Lean.toJson r.explicit), ("problems", Lean.toJson r.problems)]

/-- The reports for the answers in `type`, in traversal order. -/
def reportAnswers (declName : Name) (allowed : NameSet) (type : Expr) :
    MetaM (Array AnswerReport) := do
  let acc ← IO.mkRef #[]
  forEachAnswer type fun a => do
    let filled := !a.hasSorry
    let problems ← if filled then checkExplicitAnswer declName allowed a else pure #[]
    let problems ← problems.mapM (·.toString)
    let type := toString (← ppExpr (← inferType a))
    let term := toString (← ppExpr a)
    acc.modify fun rs => rs.push
      { index := rs.size, type, term, filled, explicit := filled && problems.isEmpty, problems }
  acc.get

unsafe def runWithImports {α : Type} (moduleNames : Array Name) (action : CoreM α) : IO α := do
  initSearchPath (← getBuildDir)
  let imports := moduleNames.map fun n => { module := n }
  Lean.enableInitializersExecution
  let env ← importModules imports {} (trustLevel := 1024) (loadExts := true)
  let (result, _) ← action.toIO { fileName := "", fileMap := default } { env }
  return result

unsafe def main (args : List String) : IO UInt32 := do
  let (flags, fileArgs) := args.partition (·.startsWith "--")
  let mut allowFile : Option String := none
  for flag in flags do
    if flag.startsWith "--allow-file=" then
      allowFile := some (flag.drop "--allow-file=".length).toString
    else
      throw <| IO.userError s!"Unknown flag {flag}."
  if fileArgs.isEmpty then
    throw <| IO.userError
      "Usage: check_answers <module-or-file>... [--allow-file=challenge.json]\n\n\
       Build with `lake build FormalConjecturesAnswerPostpone` first."
  let allowances ← match allowFile with
    | some path => readAllowFile path
    | none => pure {}
  let moduleNames ← fileArgs.toArray.mapM toModuleName
  let (results, ok) ← runWithImports moduleNames do
    let env ← getEnv
    let mut results : Array Json := #[]
    let mut ok := true
    for modName in moduleNames do
      let some modIdx := env.header.moduleNames.findIdx? (· == modName)
        | throwError "Module {modName} is not in the environment."
      for info in env.header.moduleData[modIdx]!.constants do
        let .thmInfo _ := info | continue
        if info.name.isInternal then continue
        let allowed : Array Name := match allowFile with
          | some _ => allowances.getD info.name.toString #[]
          | none => (answerAllowAttr.getParam? env info.name).getD #[]
        let reports ← MetaM.run' <| reportAnswers info.name (.ofArray allowed) info.type
        if reports.isEmpty then continue
        if reports.any fun r => r.filled && !r.explicit then ok := false
        results := results.push <| Json.mkObj [
          ("theorem", toJson info.name.toString),
          ("module", toJson modName.toString),
          ("allowed", toJson (allowed.map Name.toString)),
          ("answers", Json.arr (reports.map AnswerReport.toJson))]
    return (results, ok)
  IO.println (Json.arr results).pretty
  return if ok then 0 else 1
