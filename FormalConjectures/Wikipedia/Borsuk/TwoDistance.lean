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
import FormalConjectures.Wikipedia.Borsuk.Counting

/-!
# Two-distance sets and the clique reduction

All known record counterexamples to Borsuk's conjecture are *two-distance sets*: finite
sets in which only two distinct nonzero distances `r₁ < r₂` occur.  For such a set the
diameter is `r₂`, so a subset of strictly smaller diameter realises only the distance
`r₁` — it is a *clique* of the graph connecting points at distance `r₁`.  A bound on the
clique number of this graph therefore bounds the size of every piece of a Borsuk cover.

This file proves that reduction:

* `IsTwoDistSet`: exactly two distinct nonzero distances occur;
* `SmallPartsLE`: every subset of smaller diameter has at most `m` points;
* `Metric.ediam_eq_of_two_dist`: the diameter of a two-distance set is the larger
  distance;
* `smallPartsLE_of_two_dist`: the clique reduction;
* `finite_two_dist_package`: everything packaged for a finite family of vectors,
  distances measured by `dist`; this is the form the counterexample constructions will
  produce.
-/

namespace Borsuk

open Metric Bornology Set ENNReal

section EDist

variable {E : Type*} [PseudoEMetricSpace E] {T t : Set E} {d₁ d₂ : ℝ≥0∞} {m : ℕ}

/-- A two-distance set: exactly two distinct nonzero (extended) distances occur between
its points. -/
def IsTwoDistSet (s : Set E) : Prop :=
  ((Set.image2 edist s s) \ {0}).encard = 2

/-- The property making a finite point set a Borsuk counterexample by counting: every
subset of strictly smaller diameter has at most `m` points. -/
def SmallPartsLE (s : Set E) (m : ℕ) : Prop :=
  ∀ t ⊆ s, ediam t < ediam s → t.ncard ≤ m

/-- The diameter of a set realising only the distances `d₁ < d₂` between distinct points,
with `d₂` actually attained, is `d₂`. -/
@[category API, AMS 52]
theorem _root_.Metric.ediam_eq_of_two_dist (hd : d₁ < d₂)
    (h2 : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → edist x y = d₁ ∨ edist x y = d₂)
    (hfar : ∃ x ∈ T, ∃ y ∈ T, edist x y = d₂) : ediam T = d₂ := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hfar
  refine le_antisymm (ediam_le fun a ha b hb => ?_) (hxy ▸ edist_le_ediam_of_mem hx hy)
  rcases eq_or_ne a b with rfl | hab
  · rw [edist_self]
    exact zero_le
  · rcases h2 a ha b hb hab with h | h
    · exact h ▸ hd.le
    · exact h.le

/-- In a two-distance set, a subset of strictly smaller diameter realises only the
smaller distance: it is a clique of the "near" graph. -/
@[category API, AMS 52]
theorem clique_of_ediam_lt (hd : d₁ < d₂)
    (h2 : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → edist x y = d₁ ∨ edist x y = d₂)
    (hfar : ∃ x ∈ T, ∃ y ∈ T, edist x y = d₂) (ht : t ⊆ T) (hlt : ediam t < ediam T) :
    ∀ x ∈ t, ∀ y ∈ t, x ≠ y → edist x y = d₁ := by
  intro x hx y hy hxy
  rcases h2 x (ht hx) y (ht hy) hxy with h | h
  · exact h
  · exfalso
    rw [Metric.ediam_eq_of_two_dist hd h2 hfar] at hlt
    have hle : d₂ ≤ ediam t := h ▸ edist_le_ediam_of_mem hx hy
    exact absurd (hle.trans_lt hlt) (lt_irrefl d₂)

/-- The clique reduction: in a two-distance set in which every clique of the "near" graph
has at most `m` points, every subset of smaller diameter has at most `m` points. -/
@[category API, AMS 52]
theorem smallPartsLE_of_two_dist (hd : d₁ < d₂)
    (h2 : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → edist x y = d₁ ∨ edist x y = d₂)
    (hfar : ∃ x ∈ T, ∃ y ∈ T, edist x y = d₂)
    (hclique : ∀ t ⊆ T, (∀ x ∈ t, ∀ y ∈ t, x ≠ y → edist x y = d₁) → t.ncard ≤ m) :
    SmallPartsLE T m :=
  fun t ht hlt => hclique t ht (clique_of_ediam_lt hd h2 hfar ht hlt)

/-- The far-graph clique reduction, without any two-distance assumption: if all distances
in `T` are at most `d₂`, the value `d₂` is attained, and every subset avoiding the
distance `d₂` has at most `m` points, then every subset of smaller diameter has at most
`m` points.  This generalises `smallPartsLE_of_two_dist` to sets with more than two
distances, as needed for the 63-dimensional Borsuk counterexample. -/
@[category API, AMS 52]
theorem smallPartsLE_of_farGraph {d₂ : ℝ≥0∞}
    (hle : ∀ x ∈ T, ∀ y ∈ T, edist x y ≤ d₂)
    (hfar : ∃ x ∈ T, ∃ y ∈ T, edist x y = d₂)
    (hclique : ∀ t ⊆ T, (∀ x ∈ t, ∀ y ∈ t, edist x y < d₂) → t.ncard ≤ m) :
    SmallPartsLE T m := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hfar
  have hdiam : ediam T = d₂ :=
    le_antisymm (ediam_le fun a ha b hb => hle a ha b hb)
      (hxy ▸ edist_le_ediam_of_mem hx hy)
  intro t ht hlt
  rw [hdiam] at hlt
  exact hclique t ht fun a ha b hb => (edist_le_ediam_of_mem ha hb).trans_lt hlt

/-- A set realising only the two distinct nonzero distances `d₁` and `d₂` between
distinct points, both attained, is a two-distance set. -/
@[category API, AMS 52]
theorem isTwoDistSet_of_two_dist (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) (hne : d₁ ≠ d₂)
    (h2 : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → edist x y = d₁ ∨ edist x y = d₂)
    (hnear : ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ edist x y = d₁)
    (hfar : ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ edist x y = d₂) : IsTwoDistSet T := by
  have himg : (Set.image2 edist T T) \ {0} = {d₁, d₂} := by
    ext d
    constructor
    · rintro ⟨⟨x, hx, y, hy, rfl⟩, hd0⟩
      rcases eq_or_ne x y with rfl | hxy
      · exact absurd (edist_self x) hd0
      · rcases h2 x hx y hy hxy with h | h <;> simp [h]
    · rintro (rfl | rfl)
      · obtain ⟨x, hx, y, hy, -, hd⟩ := hnear
        exact ⟨⟨x, hx, y, hy, hd⟩, h₁⟩
      · obtain ⟨x, hx, y, hy, -, hd⟩ := hfar
        exact ⟨⟨x, hx, y, hy, hd⟩, h₂⟩
  rw [IsTwoDistSet, himg, encard_pair hne]

end EDist

section FarPair

variable {ι E : Type*} [Fintype ι] [MetricSpace E]

/-- If more than `m` vectors realise only the distances `r₁` and `r₂` between distinct
indices and every `r₁`-clique has at most `m` elements, then the distance `r₂` is
attained: not all pairs can be near. -/
@[category API, AMS 52]
theorem exists_far_pair (v : ι → E) {r₁ r₂ : ℝ} {m : ℕ} (hcard : m < Fintype.card ι)
    (h2 : ∀ i j, i ≠ j → dist (v i) (v j) = r₁ ∨ dist (v i) (v j) = r₂)
    (hclique : ∀ s : Finset ι,
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → dist (v i) (v j) = r₁) → s.card ≤ m) :
    ∃ i j, dist (v i) (v j) = r₂ := by
  by_contra hfar
  push Not at hfar
  have hall : ∀ i ∈ (Finset.univ : Finset ι), ∀ j ∈ (Finset.univ : Finset ι), i ≠ j →
      dist (v i) (v j) = r₁ :=
    fun i _ j _ hij => (h2 i j hij).resolve_right (hfar i j)
  have hle := hclique Finset.univ hall
  rw [Finset.card_univ] at hle
  omega

end FarPair

section Vectors

variable {ι E : Type*} [Finite ι] [MetricSpace E]

/-- Package a finite family of vectors realising exactly two distances `0 < r₁ < r₂`,
in which every `r₁`-clique has at most `m` elements, into the set-level statement used
for the Borsuk counterexamples.  This is the form the explicit constructions (Bondarenko,
Jenrich–Brouwer) naturally produce. -/
@[category API, AMS 52]
theorem finite_two_dist_package (v : ι → E) (hv : Function.Injective v) {r₁ r₂ : ℝ}
    {m : ℕ} (h0 : 0 < r₁) (hr : r₁ < r₂)
    (h2 : ∀ i j, i ≠ j → dist (v i) (v j) = r₁ ∨ dist (v i) (v j) = r₂)
    (hnear : ∃ i j, i ≠ j ∧ dist (v i) (v j) = r₁)
    (hfar : ∃ i j, dist (v i) (v j) = r₂)
    (hclique : ∀ s : Finset ι,
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → dist (v i) (v j) = r₁) → s.card ≤ m) :
    (Set.range v).Finite ∧ (Set.range v).ncard = Nat.card ι ∧
      IsTwoDistSet (Set.range v) ∧ SmallPartsLE (Set.range v) m := by
  have h0₂ : 0 < r₂ := h0.trans hr
  -- distances at the level of `edist`
  have h2' : ∀ x ∈ Set.range v, ∀ y ∈ Set.range v, x ≠ y →
      edist x y = ENNReal.ofReal r₁ ∨ edist x y = ENNReal.ofReal r₂ := by
    rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ hxy
    have hij : i ≠ j := fun h => hxy (by rw [h])
    rcases h2 i j hij with h | h <;> [left; right] <;> rw [edist_dist, h]
  have hfar' : ∃ x ∈ Set.range v, ∃ y ∈ Set.range v,
      edist x y = ENNReal.ofReal r₂ := by
    obtain ⟨i, j, hd⟩ := hfar
    exact ⟨v i, mem_range_self i, v j, mem_range_self j, by rw [edist_dist, hd]⟩
  have hlt : ENNReal.ofReal r₁ < ENNReal.ofReal r₂ :=
    (ENNReal.ofReal_lt_ofReal_iff h0₂).mpr hr
  refine ⟨finite_range v, ?_, ?_, ?_⟩
  · rw [← image_univ, ncard_image_of_injective _ hv, ncard_univ]
  · -- two-distance property
    refine isTwoDistSet_of_two_dist ?_ ?_ hlt.ne h2' ?_ ?_
    · exact (ENNReal.ofReal_pos.mpr h0).ne'
    · exact (ENNReal.ofReal_pos.mpr h0₂).ne'
    · obtain ⟨i, j, hij, hd⟩ := hnear
      exact ⟨v i, mem_range_self i, v j, mem_range_self j, hv.ne hij,
        by rw [edist_dist, hd]⟩
    · obtain ⟨i, j, hd⟩ := hfar
      have hij : i ≠ j := by
        rintro rfl
        rw [dist_self] at hd
        exact absurd hd.symm h0₂.ne'
      exact ⟨v i, mem_range_self i, v j, mem_range_self j, hv.ne hij,
        by rw [edist_dist, hd]⟩
  · -- the clique reduction, transported to `Finset ι`
    refine smallPartsLE_of_two_dist hlt h2' hfar' ?_
    intro t ht hpairs
    have htfin : (v ⁻¹' t).Finite := Set.toFinite _
    have himg : v '' (v ⁻¹' t) = t := image_preimage_eq_of_subset ht
    have hcard : t.ncard = htfin.toFinset.card := by
      conv_lhs => rw [← himg]
      rw [ncard_image_of_injective _ hv, ncard_eq_toFinset_card _ htfin]
    rw [hcard]
    refine hclique _ fun i hi j hj hij => ?_
    have hi' : v i ∈ t := htfin.mem_toFinset.mp hi
    have hj' : v j ∈ t := htfin.mem_toFinset.mp hj
    have := hpairs (v i) hi' (v j) hj' (hv.ne hij)
    rw [edist_dist] at this
    exact (ENNReal.ofReal_eq_ofReal_iff dist_nonneg h0.le).mp this

/-- Package a finite family of vectors with all distances at most `r₂ > 0`, the value
`r₂` attained, and every `r₂`-avoiding subset of size at most `m`, into the set-level
statement used for the Borsuk counterexamples.  This is the three-or-more-distance
analogue of `finite_two_dist_package`, needed for the 63-dimensional counterexample. -/
@[category API, AMS 52]
theorem finite_farGraph_package (v : ι → E) (hv : Function.Injective v) {r₂ : ℝ}
    {m : ℕ} (hle : ∀ i j, dist (v i) (v j) ≤ r₂)
    (hfar : ∃ i j, dist (v i) (v j) = r₂)
    (hclique : ∀ s : Finset ι,
      (∀ i ∈ s, ∀ j ∈ s, dist (v i) (v j) < r₂) → s.card ≤ m) :
    (Set.range v).Finite ∧ (Set.range v).ncard = Nat.card ι ∧
      SmallPartsLE (Set.range v) m := by
  refine ⟨finite_range v, ?_, ?_⟩
  · rw [← image_univ, ncard_image_of_injective _ hv, ncard_univ]
  · refine smallPartsLE_of_farGraph (d₂ := ENNReal.ofReal r₂) ?_ ?_ ?_
    · rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (hle i j)
    · obtain ⟨i, j, hd⟩ := hfar
      exact ⟨v i, mem_range_self i, v j, mem_range_self j, by rw [edist_dist, hd]⟩
    · intro t ht hpairs
      have htfin : (v ⁻¹' t).Finite := Set.toFinite _
      have himg : v '' (v ⁻¹' t) = t := image_preimage_eq_of_subset ht
      have hcard : t.ncard = htfin.toFinset.card := by
        conv_lhs => rw [← himg]
        rw [ncard_image_of_injective _ hv, ncard_eq_toFinset_card _ htfin]
      rw [hcard]
      refine hclique _ fun i hi j hj => ?_
      have := hpairs (v i) (htfin.mem_toFinset.mp hi) (v j) (htfin.mem_toFinset.mp hj)
      rw [edist_dist] at this
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mp this

end Vectors

end Borsuk
