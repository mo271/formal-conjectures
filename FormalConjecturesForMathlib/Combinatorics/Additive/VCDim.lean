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

public import FormalConjecturesForMathlib.Combinatorics.SetFamily.VCDim
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-!
# VC dimension in a group

This file defines the Vapnik–Chervonenkis (aka VC) dimension of a set in a group, defined as the
VC dimension of its family of translates.

It also defines the VCₙ dimension, which has no set family analogue.
-/

open scoped Pointwise

variable {G : Type*} [CommGroup G] {A B : Set G} {n d d' : ℕ}

variable (A d) in
/-- A set `A` in an abelian group has VC dimension at most `d` iff one cannot find two sequences
`x` and `y` of elements indexed by `[d + 1]` and `2 ^ [d + 1]` respectively such that
`y s * x i ∈ A ↔ i ∈ s` for all `i ∈ [d + 1]`, `s ⊆ [d + 1]`. -/
@[to_additive
/-- A set `A` in an abelian group has VC dimension at most `d` iff one cannot find two sequences
`x` and `y` of elements indexed by `[d + 1]` and `2 ^ [d + 1]` respectively such that
`y s + x i ∈ A ↔ i ∈ s` for all `i ∈ [d + 1]`, `s ⊆ [d + 1]`. -/]
def HasMulVCDimAtMost : Prop :=
  ∀ (x : Fin (d + 1) → G) (y : Set (Fin (d + 1)) → G), ¬ ∀ i s, y s * x i ∈ A ↔ i ∈ s

@[to_additive]
lemma HasMulVCDimAtMost.mono (h : d ≤ d') (hd : HasMulVCDimAtMost A d) :
    HasMulVCDimAtMost A d' := by
  rintro x y hxy
  replace h : d + 1 ≤ d' + 1 := by omega
  exact hd (x ∘ Fin.castLE h) (y ∘ Set.image (Fin.castLE h)) fun i s ↦ (hxy ..).trans <| by simp

@[to_additive (attr := simp)]
lemma hasMulVCDimAtMost_compl : HasMulVCDimAtMost Aᶜ d ↔ HasMulVCDimAtMost A d :=
  forall_congr' fun x ↦ (compl_involutive.toPerm.arrowCongr <| .refl _).forall_congr fun y ↦
    not_congr <| forall_congr' fun i ↦ compl_involutive.toPerm.forall_congr <| by simp; tauto

@[to_additive]
protected alias ⟨HasMulVCDimAtMost.of_compl, HasMulVCDimAtMost.compl⟩ := hasMulVCDimAtMost_compl

@[to_additive (attr := simp)]
protected lemma HasMulVCDimAtMost.empty : HasMulVCDimAtMost (∅ : Set G) d := by
  simpa [HasMulVCDimAtMost] using ⟨default, .univ, by simp⟩

@[to_additive (attr := simp)]
protected lemma HasMulVCDimAtMost.univ : HasMulVCDimAtMost (.univ : Set G) d := by
  simpa [HasMulVCDimAtMost] using ⟨default, ∅, by simp⟩

@[to_additive (attr := simp)]
lemma hasVCDimAtMost_smul : HasVCDimAtMost {t • A | t : G} d ↔ HasMulVCDimAtMost A d := by
  simpa [HasVCDimAtMost, HasMulVCDimAtMost, Classical.skolem (b := fun _ ↦ G), ← funext_iff,
    Set.mem_smul_set_iff_inv_smul_mem]
    using forall_congr' fun x ↦ (Equiv.inv _).forall_congr <| by simp

variable (A d n) in
/-- A set `A` in an abelian group has VCₙ dimension at most `d` iff one cannot find two sequences
`x` and `y` of elements indexed by `[n] × [d + 1]` and `2 ^ [d + 1]ⁿ` respectively such that
`y s * ∏ k, x (k, i k) ∈ A ↔ i ∈ s` for all `i ∈ [d + 1]ⁿ`, `s ⊆ [d + 1]ⁿ`. -/
@[to_additive
/-- A set `A` in an abelian group has VCₙ dimension at most `d` iff one cannot find two sequences
`x` and `y` of elements indexed by `[n] × [d + 1]` and `2 ^ [d + 1]ⁿ` respectively such that
`y s + ∑ k, x (k, i k) ∈ A ↔ i ∈ s` for all `i ∈ [d + 1]ⁿ`, `s ⊆ [d + 1]ⁿ`. -/]
def HasMulVCNDimAtMost : Prop :=
  ∀ (x : Fin n → Fin (d + 1) → G) (y : Set (Fin n → Fin (d + 1)) → G),
    ¬ ∀ i s, y s * ∏ k, x k (i k) ∈ A ↔ i ∈ s

@[to_additive]
lemma HasMulVCNDimAtMost.mono (h : d ≤ d') (hd : HasMulVCNDimAtMost A n d) :
    HasMulVCNDimAtMost A n d' := by
  rintro x y hxy
  replace h : d + 1 ≤ d' + 1 := by omega
  exact hd (x · ∘ Fin.castLE h) (y ∘ Set.image (Fin.castLE h ∘ ·)) fun i s ↦
    (hxy ..).trans <| by simp [funext_iff]; simp [← funext_iff]

@[to_additive (attr := simp)]
lemma hasMulVCNDimAtMost_compl : HasMulVCNDimAtMost Aᶜ n d ↔ HasMulVCNDimAtMost A n d :=
  forall_congr' fun x ↦ (compl_involutive.toPerm.arrowCongr <| .refl _).forall_congr fun y ↦
    not_congr <| forall_congr' fun i ↦ compl_involutive.toPerm.forall_congr <| by simp; tauto

@[to_additive]
protected alias ⟨HasMulVCNDimAtMost.of_compl, HasMulVCNDimAtMost.compl⟩ := hasMulVCNDimAtMost_compl

@[to_additive (attr := simp)]
protected lemma HasMulVCNDimAtMost.empty : HasMulVCNDimAtMost (∅ : Set G) n d := by
  simpa [HasMulVCNDimAtMost] using ⟨default, .univ, by simp⟩

@[to_additive (attr := simp)]
protected lemma HasMulVCNDimAtMost.univ : HasMulVCNDimAtMost (.univ : Set G) n d := by
  simpa [HasMulVCNDimAtMost] using ⟨default, ∅, by simp⟩

@[to_additive (attr := simp)]
lemma hasMulVCNDimAtMost_one : HasMulVCNDimAtMost A 1 d ↔ HasMulVCDimAtMost A d := by
  symm
  refine (Equiv.funUnique ..).symm.forall_congr fun x ↦
    ((Equiv.Set.congr <| Equiv.funUnique ..).arrowCongr <| .refl _).symm.forall_congr fun y ↦
    not_congr <| (Equiv.funUnique ..).symm.forall_congr fun i ↦
    (Equiv.Set.congr <| Equiv.funUnique ..).symm.forall_congr fun s ↦ ?_
  simp [Set.image_image, funext_iff]
