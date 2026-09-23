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

public meta import Lean.Meta.FunInfo
public meta import Lean.Meta.Instances
public meta import Lean.Compiler.NoncomputableAttr
public meta import Lean.Elab.Command
public import FormalConjecturesUtil.Answer

/-!
# Explicit answers

A filled `answer( )` must give the answer, not restate the question. For
`answer(sorry) ↔ P`, the term `answer(P)` makes the theorem provable by `Iff.rfl`, and for
`IsLeast S answer(sorry)`, the term `answer(sInf S)` makes it provable without finding the
least element. Neither is a solution.

`checkExplicitAnswer` decides whether a filled answer is explicit. It inspects the
elaborated term, not the source text, so a namespace or notation cannot disguise a term.
The rules are:

- An answer of type `Prop` must be `True` or `False`.
- Every other constant in the answer must be in `explicitConstants`, or be allowed for the
  theorem with `@[answer_allow c₁, c₂, ...]`. The default list covers numerals, arithmetic,
  common functions and constants, intervals, set operations and limits.
- A type class instance is exempt from the allowlist. Its meaning is fixed by Mathlib and it
  is determined by the types in the statement. A `Decidable` instance must be computable,
  so that `if p then a else b` cannot branch on a proposition that has no decision procedure.
- A constant in `forbiddenConstants`, in the `Classical` namespace, an axiom, or a `sorry`
  is always rejected, even when it is listed in `answer_allow`.
- A constant defined in the same module as the theorem is rejected unless it is listed in
  `answer_allow`. This stops a helper definition from hiding a forbidden term.
- Proofs and types inside the answer are not inspected. They do not affect its value.

The check does not judge whether an explicit answer is correct or interesting. It only
rejects terms that restate the problem. The `ExplicitAnswerLinter` applies it to every
filled answer in a problem file, and `lake exe check_answers` applies it to a compiled
module.
-/

public meta section

namespace Google

open Lean Meta

/-- Constants that may appear in an explicit answer without a per-theorem allowance.

The names are not checked at elaboration time because this module does not import Mathlib.
The test file checks that every name resolves. -/
def explicitConstants : NameSet := .ofList [
  -- Logic and control
  `True, `False, `And, `Or, `Not, `Iff, `Eq, `Ne, `Exists, `ite, `dite, `Decidable.decide,
  `cond, `Bool.true, `Bool.false, `Bool.and, `Bool.or, `Bool.not,
  `LT.lt, `LE.le, `GT.gt, `GE.ge, `Dvd.dvd, `Membership.mem,
  `id, `Function.comp, `DFunLike.coe,
  -- Numerals, casts and pairs
  `OfNat.ofNat, `Nat.cast, `NatCast.natCast, `Int.cast, `IntCast.intCast, `Rat.cast,
  `RatCast.ratCast, `Int.ofNat, `Int.negSucc, `Nat.succ, `Nat.zero, `Nat.pred,
  `NNReal.toReal, `Real.toNNReal, `ENNReal.ofReal, `ENNReal.toReal,
  `Subtype.val, `Subtype.mk, `Fin.val, `Fin.mk, `Prod.mk, `Prod.fst, `Prod.snd,
  -- Arithmetic
  `HAdd.hAdd, `HSub.hSub, `HMul.hMul, `HDiv.hDiv, `HMod.hMod, `HPow.hPow, `HSMul.hSMul,
  `Neg.neg, `Inv.inv, `Add.add, `Sub.sub, `Mul.mul, `Div.div, `Mod.mod, `Pow.pow,
  `abs, `Min.min, `Max.max,
  `Nat.factorial, `Nat.choose, `Nat.sqrt, `Nat.log, `Nat.gcd, `Nat.lcm, `Nat.Prime,
  `Nat.divisors, `Nat.primeFactors, `Nat.totient, `Nat.fib, `Int.natAbs, `Int.toNat,
  `Int.floor, `Int.ceil, `Nat.floor, `Nat.ceil,
  `Finset.sum, `Finset.prod, `Finset.range, `Finset.Icc, `Finset.Ico, `Finset.card,
  `Finset.filter, `Finset.image,
  -- Real constants and functions
  `Real.sqrt, `Real.pi, `Real.exp, `Real.log, `Real.logb, `Real.sin, `Real.cos, `Real.tan,
  `Real.arctan, `Real.rpow, `Real.goldenRatio,
  -- Intervals, sets and limits
  `Set.Icc, `Set.Ico, `Set.Ioc, `Set.Ioo, `Set.Ici, `Set.Iic, `Set.Ioi, `Set.Iio,
  `Set.univ, `Set.range, `Set.image, `Set.preimage,
  `EmptyCollection.emptyCollection, `Singleton.singleton, `Insert.insert,
  `Union.union, `Inter.inter, `SDiff.sdiff, `HasCompl.compl,
  `nhds, `Filter.atTop, `Filter.atBot]

/-- Constants that may never appear in an answer, even with `answer_allow`. Each of them
defines a value by a property rather than by a construction. -/
def forbiddenConstants : NameSet := .ofList [
  `sorryAx, `Classical.choice, `Classical.choose, `Classical.epsilon,
  `Exists.choose, `Nonempty.some, `Set.Nonempty.some, `Quot.out, `Quotient.out,
  `Nat.find, `Nat.findGreatest, `InfSet.sInf, `SupSet.sSup, `iInf, `iSup,
  `Nat.card, `Set.ncard, `Set.encard, `Cardinal.mk,
  `Function.invFun, `Function.surjInv, `WellFounded.min, `Set.IsWF.min,
  `Finset.min, `Finset.max, `Finset.min', `Finset.max', `Filter.limUnder]

/-- Whether `n` may never appear in an answer. -/
def isForbiddenInAnswer (env : Environment) (n : Name) : Bool :=
  forbiddenConstants.contains n || (`Classical).isPrefixOf n || (env.find? n).any (·.isAxiom)

/-- The syntax of the `answer_allow` attribute. -/
syntax (name := answer_allow) "answer_allow " ident,+ : attr

/-- Names a constant that may appear in the answer of this theorem, in addition to
`explicitConstants`. Use it for a constant that the problem defines as the intended
answer, for instance the shape whose volume answers the moving sofa problem.

The names are resolved when the attribute is applied. A name in `forbiddenConstants`, in the
`Classical` namespace, or naming an axiom is rejected. -/
initialize answerAllowAttr : ParametricAttribute (Array Name) ←
  registerParametricAttribute {
    name := `answer_allow
    descr := "constants that may appear in the answer of this theorem"
    getParam := fun _ stx => do
      match stx with
      | `(attr| answer_allow $ids,*) =>
        ids.getElems.mapM fun id => withRef id do
          let n ← realizeGlobalConstNoOverload id
          if isForbiddenInAnswer (← getEnv) n then
            throwError "`{n}` may not appear in an answer"
          return n
      | _ => throwError "unexpected syntax for `answer_allow`"
  }

/-- The constants that `answer_allow` permits for `declName`. -/
def allowedAnswerConstants (env : Environment) (declName : Name) : NameSet :=
  .ofArray <| (answerAllowAttr.getParam? env declName).getD #[]

/-- Runs `f` on every subterm of `e` that carries the `answer` annotation, with the
binders above it in the local context. -/
partial def forEachAnswer (e : Expr) (f : Expr → MetaM Unit) : MetaM Unit :=
  match e with
  | .mdata m b => do
    if m.contains `answer then f b
    forEachAnswer b f
  | .app g a => do forEachAnswer g f; forEachAnswer a f
  | .lam n t b bi | .forallE n t b bi => do
    forEachAnswer t f
    withLocalDecl n bi t fun x => forEachAnswer (b.instantiate1 x) f
  | .letE n t v b _ => do
    forEachAnswer t f
    forEachAnswer v f
    withLetDecl n t v fun x => forEachAnswer (b.instantiate1 x) f
  | .proj _ _ b => forEachAnswer b f
  | _ => pure ()

namespace ExplicitAnswer

/-- The theorem whose answer is checked and the constants it allows. -/
structure Context where
  declName : Name
  allowed : NameSet

/-- The constants already reported, and the messages so far. -/
structure State where
  reported : NameSet := {}
  problems : Array MessageData := #[]

/-- The monad of the check. -/
abbrev CheckM := ReaderT Context (StateRefT State MetaM)

/-- Records a problem with the constant `n`, once per constant. -/
def report (n : Name) (msg : MessageData) : CheckM Unit :=
  modify fun s =>
    if s.reported.contains n then s
    else { reported := s.reported.insert n, problems := s.problems.push msg }

/-- Whether `ty` is `Decidable p`, possibly under binders such as in `DecidablePred`. -/
def isDecidableType (ty : Expr) : MetaM Bool :=
  forallTelescopeReducing ty fun _ body => return body.getAppFn.isConstOf ``Decidable

/-- Checks the constant `n`. `inst` says that it heads a registered instance in an
instance-implicit position, and `decidable` that this instance is a `Decidable`. -/
def checkConst (n : Name) (inst decidable : Bool) : CheckM Unit := do
  let env ← getEnv
  let ctx ← read
  if isForbiddenInAnswer env n then
    report n m!"`{n}` may not appear in an answer"
  else if ctx.allowed.contains n then
    return
  else if env.getModuleIdxFor? n == env.getModuleIdxFor? ctx.declName then
    report n m!"`{n}` is defined in the same file as the problem; \
      add `@[answer_allow {n}]` to the theorem if it is part of the intended answer"
  else if inst then
    if decidable && isNoncomputable env n then
      report n m!"the `Decidable` instance `{n}` is noncomputable"
  else unless explicitConstants.contains n do
    report n m!"`{n}` is not in the allowlist of explicit constants"

/-- Checks the head `f` of the application `e`. In an instance-implicit position a
registered instance is exempt from the allowlist. -/
def checkHead (f e : Expr) (inst : Bool) : CheckM Unit := do
  let .const n _ := f | return
  let inst := inst && isInstanceCore (← getEnv) n
  let decidable ← if inst then isDecidableType (← inferType e) else pure false
  checkConst n inst decidable

/-- Visits every subterm of `e` that contributes to its value. `inst` says that `e` is in
an instance-implicit position. Proofs and types are skipped, except at the top level. -/
partial def visit (e : Expr) (inst : Bool := false) (top : Bool := false) : CheckM Unit := do
  let e := e.consumeMData
  unless top do
    if ← isProof e then return
    if (← isType e) && !(← isProp e) then return
  match e with
  | .const .. => checkHead e e inst
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if f.isConst then checkHead f e inst else visit f inst
    let info ← getFunInfoNArgs f args.size
    for i in [0:args.size] do
      -- The parent projection of a class takes its instance parameters as implicit
      -- arguments, so an argument whose type is a class also counts as an instance.
      let instArg := (info.paramInfo[i]?.map (·.isInstImplicit)).getD false
        || (← isClass? (← inferType args[i]!)).isSome
      visit args[i]! instArg
  | .lam n t b bi | .forallE n t b bi =>
    withLocalDecl n bi t fun x => visit (b.instantiate1 x) inst
  | .letE n t v b _ =>
    visit v
    withLetDecl n t v fun x => visit (b.instantiate1 x) inst
  | .proj _ _ b => visit b
  | _ => pure ()

end ExplicitAnswer

/-- The reasons why the filled answer `e` of `declName` is not explicit. The answer is
explicit when the result is empty. `allowed` lists the constants that `answer_allow`
permits for the theorem. -/
def checkExplicitAnswer (declName : Name) (allowed : NameSet) (e : Expr) :
    MetaM (Array MessageData) := do
  let e := e.consumeMData
  if ← isProp e then
    if e == .const ``True [] || e == .const ``False [] then return #[]
    let msg := m!"an answer of type `Prop` must be `True` or `False`"
    if let .const n _ := e then
      return #[msg ++ m!", but this term is the constant `{n}`"]
    return #[msg]
  let (_, s) ← (ExplicitAnswer.visit e (top := true)).run { declName, allowed } |>.run {}
  return s.problems

end Google
