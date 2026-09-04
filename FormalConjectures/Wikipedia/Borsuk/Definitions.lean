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
# Borsuk's conjecture: definitions and basic API

This file defines `HasBorsukCover k s` (the set `s` can be covered by `k` sets of strictly
smaller extended diameter) and `BorsukConjecture n` (every bounded subset of $\mathbb{R}^n$
with at least two points has a Borsuk cover by `n + 1` sets), together with basic API:
monotonicity in the number of pieces, restriction of the pieces to `s`, and transfer along
isometries and scalings.

We use the extended diameter `Metric.ediam` (with values in `ℝ≥0∞`) rather than
`Metric.diam`, since the latter takes the junk value `0` on unbounded sets, which would make
`Set.univ` a "small" covering set. With `Metric.ediam` no such degeneracy occurs.

The statements of the conjecture and of the known results, with references, are in
`FormalConjectures.Wikipedia.BorsukConjecture`. The proofs are in the other files of
`FormalConjectures/Wikipedia/Borsuk/`.
-/

namespace Borsuk

open Metric Bornology Set
open scoped Pointwise ENNReal EuclideanGeometry

section PseudoEMetric

variable {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]

/-- `HasBorsukCover k s` means that the set `s` can be covered by `k` sets, each of
strictly smaller (extended) diameter than `s` itself.

Note the built-in degeneracies: a set of diameter `0` (in particular a singleton) admits no
Borsuk cover at all, and an unbounded set admits no *finite* Borsuk cover, since every
covering set would have to be bounded.  This matches Borsuk's formulation, which considers
bounded sets with at least two points. -/
def HasBorsukCover (k : ℕ) (s : Set E) : Prop :=
  ∃ c : Fin k → Set E, s ⊆ ⋃ i, c i ∧ ∀ i, ediam (c i) < ediam s

/--
**Borsuk's conjecture** in dimension `n`: every bounded subset of $\mathbb{R}^n$ with at
least two points can be partitioned into $n + 1$ sets of strictly smaller diameter.
-/
def BorsukConjecture (n : ℕ) : Prop :=
  ∀ s : Set (ℝ^n), IsBounded s → s.Nontrivial → HasBorsukCover (n + 1) s

namespace HasBorsukCover

/-- A nonempty set with a Borsuk cover has positive diameter; equivalently, it is not a
subsingleton. -/
@[category API, AMS 52]
theorem ediam_pos {k : ℕ} {s : Set E} (h : HasBorsukCover k s) (hs : s.Nonempty) :
    0 < ediam s := by
  obtain ⟨c, hcov, hdiam⟩ := h
  obtain ⟨x, hx⟩ := hs
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hx)
  exact lt_of_le_of_lt zero_le (hdiam i)

/-- Monotonicity in the number of pieces: a Borsuk cover by `k` sets yields one by `l ≥ k`
sets, for nonempty `s` (the extra pieces are empty).  The nonemptiness hypothesis is needed:
the empty set is covered by zero sets, but a cover by one set would require a set of
diameter less than `0`. -/
@[category API, AMS 52]
theorem mono {k l : ℕ} {s : Set E} (h : HasBorsukCover k s) (hs : s.Nonempty)
    (hkl : k ≤ l) : HasBorsukCover l s := by
  have hpos : 0 < ediam s := h.ediam_pos hs
  obtain ⟨c, hcov, hdiam⟩ := h
  refine ⟨fun j => if hj : (j : ℕ) < k then c ⟨j, hj⟩ else ∅, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hx)
    refine mem_iUnion.mpr ⟨Fin.castLE hkl i, ?_⟩
    simpa [Fin.castLE, i.isLt] using hi
  · intro j
    dsimp only
    split
    · exact hdiam _
    · simpa [ediam_empty] using hpos

/-- The pieces of a Borsuk cover may be taken to be subsets of `s`. -/
@[category API, AMS 52]
theorem exists_subsets {k : ℕ} {s : Set E} (h : HasBorsukCover k s) :
    ∃ c : Fin k → Set E, (∀ i, c i ⊆ s) ∧ s = ⋃ i, c i ∧ ∀ i, ediam (c i) < ediam s := by
  obtain ⟨c, hcov, hdiam⟩ := h
  refine ⟨fun i => c i ∩ s, fun i => inter_subset_right, ?_, fun i =>
    lt_of_le_of_lt (ediam_mono inter_subset_left) (hdiam i)⟩
  refine Subset.antisymm (fun x hx => ?_) (iUnion_subset fun i => inter_subset_right)
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hx)
  exact mem_iUnion.mpr ⟨i, hi, hx⟩

/-- Borsuk covers are preserved by isometries (applied to the whole space).  This is the
workhorse for transferring the Borsuk problem along coordinate changes, e.g. identifying a
hyperplane in `ℝ^(n+1)` with `ℝ^n`. -/
@[category API, AMS 52]
theorem image {k : ℕ} {s : Set E} (e : E ≃ᵢ F) (h : HasBorsukCover k s) :
    HasBorsukCover k (e '' s) := by
  obtain ⟨c, hcov, hdiam⟩ := h
  refine ⟨fun i => e '' c i, ?_, fun i => ?_⟩
  · rw [← image_iUnion]
    exact image_mono hcov
  · rw [e.ediam_image, e.ediam_image]
    exact hdiam i

/-- Transfer of a Borsuk cover along an isometric equivalence, preimage version. -/
@[category API, AMS 52]
theorem preimage {k : ℕ} {s : Set F} (e : E ≃ᵢ F) (h : HasBorsukCover k (e ⁻¹' s)) :
    HasBorsukCover k s := by
  have h2 := h.image e
  rwa [image_preimage_eq s e.surjective] at h2

/-- Borsuk covers are preserved by nonzero scalar rescalings. -/
@[category API, AMS 52]
theorem smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} {s : Set E}
    {r : ℝ} (hr : r ≠ 0) (h : HasBorsukCover k s) : HasBorsukCover k (r • s) := by
  obtain ⟨c, hcov, hdiam⟩ := h
  refine ⟨fun i => r • c i, ?_, fun i => ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hx)
    exact mem_iUnion.mpr ⟨i, smul_mem_smul_set hi⟩
  · rw [ediam_smul₀, ediam_smul₀]
    have hr0 : (0 : ℝ≥0∞) < (‖r‖₊ : ℝ≥0∞) := by
      simpa [pos_iff_ne_zero] using hr
    rw [ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, mul_comm,
      mul_comm (‖r‖₊ : ℝ≥0∞)]
    exact ENNReal.mul_lt_mul_left hr0.ne' ENNReal.coe_ne_top (hdiam i)

end HasBorsukCover

end PseudoEMetric

end Borsuk
