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
# An explicit construction of the `G₂(4)` graph

This file constructs the `G₂(4)` strongly regular graph `srg(416, 100, 36, 20)`
explicitly, following the computer program `G24CHK.PAS` accompanying Jenrich's
arXiv:1308.0206:

* work in `GF(16) = 𝔽₂[X]/(X⁴+X+1)`, with the conjugation `a ↦ a⁴` (the involution of
  `GF(16)` over `GF(4)`) and the Hermitian form
  `h(x, y) = x₁·conj y₃ + x₂·conj y₂ + x₃·conj y₁` on `GF(16)³`;
* the projective plane `PG(2, 16)` has `273` points (in normalized coordinates), of which
  `65` are isotropic (`h(x, x) = 0`, the Hermitian unital) and `208` are non-isotropic;
* every non-isotropic point is orthogonal to exactly `5` isotropic points, and there are
  exactly `416` *orthogonal bases*: unordered triples of pairwise-orthogonal
  non-isotropic points.  These are the vertices of the graph; each vertex determines the
  set of `15` isotropic points orthogonal to one of its three base points, stored below
  as a 65-bit mask;
* two vertices are adjacent iff their isotropic sets share exactly `3` points.

All definitions here are computable; the graph-theoretic facts about them are established
in `FormalConjectures/Wikipedia/Borsuk/G2Four/Facts.lean` by `native_decide`.
-/

namespace Borsuk

namespace G2Four

/-- Multiplication by `X` in `GF(16) = 𝔽₂[X]/(X⁴+X+1)`, elements encoded as `0..15`. -/
def xtime (a : Nat) : Nat :=
  let a' := a <<< 1
  if a' ≥ 16 then a' ^^^ 19 else a'

/-- Multiplication in `GF(16)`. -/
def gmul (a b : Nat) : Nat :=
  (if b &&& 1 ≠ 0 then a else 0) ^^^
  (if b &&& 2 ≠ 0 then xtime a else 0) ^^^
  (if b &&& 4 ≠ 0 then xtime (xtime a) else 0) ^^^
  (if b &&& 8 ≠ 0 then xtime (xtime (xtime a)) else 0)

/-- Conjugation `a ↦ a⁴` in `GF(16)`, the involution fixing `GF(4)`. -/
def gconj (a : Nat) : Nat :=
  let s := gmul a a
  gmul s s

/-- The Hermitian form `h(x, y) = x₁·conj y₃ + x₂·conj y₂ + x₃·conj y₁` on `GF(16)³`. -/
def herm (x y : Nat × Nat × Nat) : Nat :=
  gmul x.1 (gconj y.2.2) ^^^ gmul x.2.1 (gconj y.2.1) ^^^ gmul x.2.2 (gconj y.1)

/-- The `273` points of `PG(2, 16)` in normalized coordinates (first nonzero coordinate
equal to `1`). -/
def pts : Array (Nat × Nat × Nat) := Id.run do
  let mut r := #[]
  for a1 in [0:16] do
    for a2 in [0:16] do
      for a3 in [0:16] do
        if a1 == 1 || (a1 == 0 && (a2 == 1 || (a2 == 0 && a3 == 1))) then
          r := r.push (a1, a2, a3)
  return r

/-- The `65` isotropic points (the Hermitian unital). -/
def isoPts : Array (Nat × Nat × Nat) := pts.filter fun p => herm p p == 0

/-- The `208` non-isotropic points. -/
def nonIsoPts : Array (Nat × Nat × Nat) := pts.filter fun p => herm p p != 0

/-- The 65-bit mask of isotropic points orthogonal to a given point. -/
def orthoIsoMask (p : Nat × Nat × Nat) : Nat :=
  (isoPts.foldl (init := ((0 : Nat), (0 : Nat))) fun acc q =>
    ((if herm p q == 0 then acc.1 ||| (1 <<< acc.2) else acc.1), acc.2 + 1)).1

/-- The `416` vertices of the `G₂(4)` graph: orthogonal bases `{n₁, n₂, n₃}` of pairwise
orthogonal non-isotropic points, each stored as the 65-bit mask of the `15` isotropic
points orthogonal to one of its base points. -/
def vertexMasks : Array Nat := Id.run do
  let mut r := #[]
  for n1 in [0:nonIsoPts.size] do
    for n2 in [n1+1:nonIsoPts.size] do
      if herm nonIsoPts[n1]! nonIsoPts[n2]! == 0 then
        for n3 in [n2+1:nonIsoPts.size] do
          if herm nonIsoPts[n1]! nonIsoPts[n3]! == 0 &&
             herm nonIsoPts[n2]! nonIsoPts[n3]! == 0 then
            r := r.push (orthoIsoMask nonIsoPts[n1]! ||| orthoIsoMask nonIsoPts[n2]! |||
              orthoIsoMask nonIsoPts[n3]!)
  return r

/-- Population count of the low 65 bits. -/
def popCount65 (n : Nat) : Nat := Id.run do
  let mut c := 0
  let mut m := n
  for _ in [0:65] do
    c := c + (m &&& 1)
    m := m >>> 1
  return c

/-- The adjacency table of the `G₂(4)` graph, row-major: vertices are adjacent iff their
isotropic sets share exactly `3` points. -/
def adjTable : Array Bool := Id.run do
  let mut r := Array.mkEmpty (416 * 416)
  for i in [0:416] do
    for j in [0:416] do
      r := r.push (i != j && popCount65 (vertexMasks[i]! &&& vertexMasks[j]!) == 3)
  return r

/-- The adjacency relation of the `G₂(4)` graph on `Fin 416`. -/
def adj (i j : Fin 416) : Bool := adjTable[416 * i.val + j.val]!

/-- Boolean check that the graph contains no `6`-clique, enumerating candidate cliques in
increasing vertex order.  The `if ... then ... else true` structure ensures the compiled
check short-circuits, so `native_decide` only explores actual partial cliques. -/
def sixCliqueFreeB : Bool :=
  (List.finRange 416).all fun i =>
    (List.finRange 416).all fun j =>
      if i < j ∧ adj i j = true then
        (List.finRange 416).all fun w =>
          if j < w ∧ adj i w = true ∧ adj j w = true then
            (List.finRange 416).all fun x =>
              if w < x ∧ adj i x = true ∧ adj j x = true ∧ adj w x = true then
                (List.finRange 416).all fun y =>
                  if x < y ∧ adj i y = true ∧ adj j y = true ∧ adj w y = true ∧
                      adj x y = true then
                    (List.finRange 416).all fun z =>
                      if y < z ∧ adj i z = true ∧ adj j z = true ∧ adj w z = true ∧
                          adj x z = true ∧ adj y z = true then false else true
                  else true
              else true
          else true
      else true

end G2Four

end Borsuk
