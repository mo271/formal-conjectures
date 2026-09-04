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
import FormalConjectures.Wikipedia.Borsuk.Definitions

/-!
# Borsuk's conjecture in low dimensions

This file proves Borsuk's conjecture in the trivial dimensions:

* `borsukConjecture_zero`: dimension `0` (vacuous, the space is a point);
* `borsukConjecture_one`: dimension `1` (split at the midpoint of the smallest enclosing
  interval).

Dimension `2` is proved in `FormalConjectures/Wikipedia/Borsuk/Plane/BorsukTwo.lean` and dimension `3` in
`FormalConjectures/Wikipedia/Borsuk/Space/BorsukThree.lean`.
-/

namespace Borsuk

open Metric Bornology Set

/-- Borsuk's conjecture holds vacuously in dimension `0`: the space is a single point, so
there is no bounded set with two distinct points. -/
@[category API, AMS 52]
theorem borsukConjecture_zero : BorsukConjecture 0 := by
  intro s _ hs
  obtain ⟨x, -, y, -, hxy⟩ := hs
  exact absurd (PiLp.ext fun i => i.elim0) hxy

section DimensionOne

/-- Every bounded set of reals with at least two points can be divided into two parts of
smaller diameter: split at the midpoint of `[sInf s, sSup s]`. -/
@[category API, AMS 52]
theorem Real.hasBorsukCover_two {s : Set ℝ} (hb : IsBounded s) (hs : s.Nontrivial) :
    HasBorsukCover 2 s := by
  set a := sInf s with ha
  set b := sSup s with hb'
  have hab : 0 < b - a := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hs
    have h₁ : a ≤ min x y := le_min (csInf_le hb.bddBelow hx) (csInf_le hb.bddBelow hy)
    have h₂ : max x y ≤ b := max_le (le_csSup hb.bddAbove hx) (le_csSup hb.bddAbove hy)
    have : min x y < max x y := min_lt_max.mpr hxy
    linarith
  have hdiam : ediam s = ENNReal.ofReal (b - a) := Real.ediam_eq hb
  have hmem : ∀ x ∈ s, x ∈ Icc a b := fun x hx =>
    ⟨csInf_le hb.bddBelow hx, le_csSup hb.bddAbove hx⟩
  set m := (a + b) / 2 with hm
  have hhalf : ENNReal.ofReal ((b - a) / 2) < ediam s := by
    rw [hdiam, ENNReal.ofReal_lt_ofReal_iff hab]
    linarith
  refine ⟨![s ∩ Iic m, s ∩ Ici m], fun x hx => ?_, fun i => ?_⟩
  · rcases le_total x m with h | h
    · exact mem_iUnion.mpr ⟨0, hx, h⟩
    · exact mem_iUnion.mpr ⟨1, hx, h⟩
  · fin_cases i
    · change ediam (s ∩ Iic m) < ediam s
      calc ediam (s ∩ Iic m)
          ≤ ediam (Icc a m) := ediam_mono fun x hx => ⟨(hmem x hx.1).1, hx.2⟩
        _ ≤ ENNReal.ofReal ((b - a) / 2) := by
            rw [Real.ediam_Icc]
            exact ENNReal.ofReal_le_ofReal (by rw [hm]; linarith)
        _ < ediam s := hhalf
    · change ediam (s ∩ Ici m) < ediam s
      calc ediam (s ∩ Ici m)
          ≤ ediam (Icc m b) := ediam_mono fun x hx => ⟨hx.2, (hmem x hx.1).2⟩
        _ ≤ ENNReal.ofReal ((b - a) / 2) := by
            rw [Real.ediam_Icc]
            exact ENNReal.ofReal_le_ofReal (by rw [hm]; linarith)
        _ < ediam s := hhalf

/-- The isometric equivalence between `ℝ` and one-dimensional Euclidean space. -/
noncomputable def IsometryEquiv.realEuclidean : ℝ ≃ᵢ EuclideanSpace ℝ (Fin 1) where
  toFun x := !₂[x]
  invFun x := x 0
  left_inv x := rfl
  right_inv x := PiLp.ext fun i => by fin_cases i; rfl
  isometry_toFun := Isometry.of_dist_eq fun x y => by
    rw [EuclideanSpace.dist_eq]
    simp

/-- Borsuk's conjecture holds in dimension `1`: a bounded set of reals with at least two
points splits at the midpoint of its smallest enclosing interval into two parts of smaller
diameter. -/
@[category API, AMS 52]
theorem borsukConjecture_one : BorsukConjecture 1 := by
  intro s hbs hs
  set e := IsometryEquiv.realEuclidean with he
  have hbt : IsBounded (⇑e.symm '' s) := e.symm.isometry.lipschitz.isBounded_image hbs
  have hnt : (⇑e.symm '' s).Nontrivial := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hs
    exact ⟨e.symm x, mem_image_of_mem _ hx, e.symm y, mem_image_of_mem _ hy,
      fun h => hxy (e.symm.injective h)⟩
  have h2 := (Real.hasBorsukCover_two hbt hnt).image e
  have himg : ⇑e '' (⇑e.symm '' s) = s := by
    rw [image_image]
    simp
  rwa [himg] at h2

end DimensionOne

-- Borsuk's conjecture in dimension `2` is proved in `FormalConjectures/Wikipedia/Borsuk/Plane/BorsukTwo.lean`
-- (`borsukConjecture_two`), via Jung's inequality and a rigidity analysis of
-- 120°-sectors around the Jung centre — no Pál hexagon needed.

-- Borsuk's conjecture in dimension `3` is proved in `FormalConjectures/Wikipedia/Borsuk/Space/BorsukThree.lean`
-- (`borsukConjecture_three`), via the Gale–Grünbaum octahedron cover: the set is
-- rescaled and moved into a truncated octahedron, which is dissected into four
-- certified pieces of smaller diameter.

end Borsuk
