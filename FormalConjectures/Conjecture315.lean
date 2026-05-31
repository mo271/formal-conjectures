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

import FormalConjectures.Util.ProblemImports
import FormalConjectures.Wow2_315
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Supporting lemmas for WOWII Conjecture 315

Structural lemmas about minimal total dominating sets in graphs where the independence number
equals the number of pendant vertices.
-/

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false
set_option linter.unusedVariables false

open Classical
open SimpleGraph

namespace WrittenOnTheWallII.GraphConjecture315

variable {α : Type*} [Fintype α] [DecidableEq α]



lemma N_subset_TDS (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : G.indepNum = (pendantVertices G).card)
    (D : Finset α) (hD : IsTotalDominatingSet G D) :
    pendantNeighbors G ⊆ D := by
  intro u hu
  unfold pendantNeighbors at hu
  simp only [Finset.mem_biUnion] at hu
  rcases hu with ⟨v, hv, huv⟩
  have h_dom := hD v
  rcases h_dom with ⟨w, hw, hvw⟩
  have hv1 : G.degree v = 1 := by
    simp only [pendantVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    exact hv
  have h_w_eq_u : w = u := by
    have h_card : (G.neighborFinset v).card = 1 := hv1
    rw [Finset.card_eq_one] at h_card
    rcases h_card with ⟨a, ha⟩
    have hu_in : u ∈ G.neighborFinset v := huv
    have hw_in : w ∈ G.neighborFinset v := by rwa [mem_neighborFinset]
    rw [ha] at hu_in hw_in
    simp only [Finset.mem_singleton] at hu_in hw_in
    rw [hw_in, hu_in]
  rwa [h_w_eq_u] at hw

/-- The set of vertices in N(P) that have no neighbors in N(P). -/
noncomputable def isolated_in_N (G : SimpleGraph α) [DecidableRel G.Adj] : Finset α :=
  (pendantNeighbors G).filter (fun u => Disjoint (G.neighborFinset u) (pendantNeighbors G))

lemma D_P_subset_P (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : G.indepNum = (pendantVertices G).card)
    (D : Finset α) :
    D \ pendantNeighbors G ⊆ pendantVertices G := by
  intro v hv
  simp only [Finset.mem_sdiff] at hv
  have h_univ := V_eq_P_union_N G hG h
  have hv_univ : v ∈ Finset.univ := Finset.mem_univ v
  rw [h_univ] at hv_univ
  simp only [Finset.mem_union] at hv_univ
  rcases hv_univ with hP | hN
  · exact hP
  · exfalso
    exact hv.2 hN

lemma D_P_neighbor_isolated (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : G.indepNum = (pendantVertices G).card)
    (D : Finset α) (hD : IsMinimalTotalDominatingSet G D) (v : α) (hv : v ∈ D \ pendantNeighbors G) :
    ∃ u ∈ isolated_in_N G, G.Adj v u ∧ G.neighborFinset v = {u} ∧ Disjoint (G.neighborFinset u) (D \ {v}) := by
  have hvP : v ∈ pendantVertices G := D_P_subset_P G hG h D hv
  have hv_deg : G.degree v = 1 := by
    simp only [pendantVertices, Finset.mem_filter, Finset.mem_univ, true_and] at hvP
    exact hvP
  have h_card : (G.neighborFinset v).card = 1 := hv_deg
  rw [Finset.card_eq_one] at h_card
  rcases h_card with ⟨u, hu⟩
  have huv : G.Adj v u := by
    have h_in : u ∈ G.neighborFinset v := by rw [hu, Finset.mem_singleton]
    rwa [mem_neighborFinset] at h_in
  use u
  have h_not_TDS : ¬ IsTotalDominatingSet G (D \ {v}) := by
    apply hD.2 (D \ {v})
    rw [Finset.ssubset_iff_of_subset Finset.sdiff_subset]
    use v
    constructor
    · exact (Finset.mem_sdiff.mp hv).1
    · simp only [Finset.mem_sdiff, Finset.mem_singleton, not_and, not_not]
      intro _
      trivial
  have h_not_TDS' : ∃ x, ∀ w ∈ D \ {v}, ¬ G.Adj x w := by
    unfold IsTotalDominatingSet at h_not_TDS
    push_neg at h_not_TDS
    exact h_not_TDS
  rcases h_not_TDS' with ⟨x, hx⟩
  have h_dom_x : ∃ w ∈ D, G.Adj x w := hD.1 x
  rcases h_dom_x with ⟨w, hw, hxw⟩
  have h_w_eq_v : w = v := by
    by_contra h_neq
    have h_w_in : w ∈ D \ {v} := by
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      exact ⟨hw, h_neq⟩
    exact hx w h_w_in hxw
  have h_x_eq_u : x = u := by
    have h_x_in : x ∈ G.neighborFinset v := by
      rw [mem_neighborFinset]
      rw [h_w_eq_v] at hxw
      exact G.adj_symm hxw
    rw [hu, Finset.mem_singleton] at h_x_in
    exact h_x_in
  have h_disj : Disjoint (G.neighborFinset u) (D \ {v}) := by
    rw [Finset.disjoint_iff_ne]
    intro y hy z hz
    by_contra h_eq
    rw [h_eq] at hy
    rw [mem_neighborFinset] at hy
    rw [← h_x_eq_u] at hy
    exact hx z hz hy
  have h_u_in_N : u ∈ pendantNeighbors G := by
    unfold pendantNeighbors
    simp only [Finset.mem_biUnion]
    use v
    constructor
    · exact hvP
    · rw [mem_neighborFinset]
      exact huv
  have h_iso : u ∈ isolated_in_N G := by
    unfold isolated_in_N
    simp only [Finset.mem_filter]
    constructor
    · exact h_u_in_N
    · have h_N_sub : pendantNeighbors G ⊆ D \ {v} := by
        intro y hy
        simp only [Finset.mem_sdiff, Finset.mem_singleton]
        constructor
        · exact N_subset_TDS G hG h D hD.1 hy
        · by_contra h_eq
          rw [h_eq] at hy
          exact (Finset.mem_sdiff.mp hv).2 hy
      exact Finset.disjoint_of_subset_right h_N_sub h_disj
  exact ⟨h_iso, huv, hu, h_disj⟩

lemma minimal_TDS_structure (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : G.indepNum = (pendantVertices G).card)
    (D : Finset α) (hD : IsMinimalTotalDominatingSet G D) :
    D.card = (pendantNeighbors G).card + (isolated_in_N G).card := by
  have h_N_sub : pendantNeighbors G ⊆ D := N_subset_TDS G hG h D hD.1
  have h_D_eq : D = pendantNeighbors G ∪ (D \ pendantNeighbors G) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  have h_disj : Disjoint (pendantNeighbors G) (D \ pendantNeighbors G) := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy h_eq
    rw [h_eq] at hx
    exact (Finset.mem_sdiff.mp hy).2 hx
  have h_card_D : D.card = (pendantNeighbors G).card + (D \ pendantNeighbors G).card := by
    nth_rw 1 [h_D_eq]
    exact Finset.card_union_of_disjoint h_disj
  have h_bij : (D \ pendantNeighbors G).card = (isolated_in_N G).card := by
    let f (v : α) (hv : v ∈ D \ pendantNeighbors G) : α :=
      Classical.choose (D_P_neighbor_isolated G hG h D hD v hv)
    have hf : ∀ v hv, f v hv ∈ isolated_in_N G ∧ G.Adj v (f v hv) ∧ G.neighborFinset v = {f v hv} ∧ Disjoint (G.neighborFinset (f v hv)) (D \ {v}) := by
      intro v hv
      exact Classical.choose_spec (D_P_neighbor_isolated G hG h D hD v hv)
    apply Finset.card_bij f
    · intro v hv
      exact (hf v hv).1
    · intro v1 hv1 v2 hv2 h_eq
      by_contra h_neq
      have h_disj1 := (hf v1 hv1).2.2.2
      have h_adj2 := (hf v2 hv2).2.1
      have h_in_N : v2 ∈ G.neighborFinset (f v1 hv1) := by
        rw [h_eq]
        rw [mem_neighborFinset]
        exact G.adj_symm h_adj2
      have h_in_D : v2 ∈ D \ {v1} := by
        simp only [Finset.mem_sdiff, Finset.mem_singleton]
        constructor
        · exact (Finset.mem_sdiff.mp hv2).1
        · exact Ne.symm h_neq
      have h_inter : v2 ∈ G.neighborFinset (f v1 hv1) ∩ (D \ {v1}) := by
        simp only [Finset.mem_inter]
        exact ⟨h_in_N, h_in_D⟩
      have h_empty : G.neighborFinset (f v1 hv1) ∩ (D \ {v1}) = ∅ := Finset.disjoint_iff_inter_eq_empty.mp h_disj1
      rw [h_empty] at h_inter
      revert h_inter
      simp
    · intro u hu
      have h_dom_u : ∃ w ∈ D, G.Adj u w := hD.1 u
      rcases h_dom_u with ⟨w, hw, huw⟩
      have h_w_not_in_N : w ∉ pendantNeighbors G := by
        by_contra h_in_N
        have h_iso : Disjoint (G.neighborFinset u) (pendantNeighbors G) := by
          unfold isolated_in_N at hu
          simp only [Finset.mem_filter] at hu
          exact hu.2
        have h_w_in_N_u : w ∈ G.neighborFinset u := by
          rw [mem_neighborFinset]
          exact huw
        have h_inter : w ∈ G.neighborFinset u ∩ pendantNeighbors G := by
          simp only [Finset.mem_inter]
          exact ⟨h_w_in_N_u, h_in_N⟩
        have h_empty : G.neighborFinset u ∩ pendantNeighbors G = ∅ := Finset.disjoint_iff_inter_eq_empty.mp h_iso
        rw [h_empty] at h_inter
        revert h_inter
        simp
      have hw_diff : w ∈ D \ pendantNeighbors G := by
        simp only [Finset.mem_sdiff]
        exact ⟨hw, h_w_not_in_N⟩
      use w, hw_diff
      have h_w_neigh := (hf w hw_diff).2.2.1
      have h_u_in : u ∈ G.neighborFinset w := by
        rw [mem_neighborFinset]
        exact G.adj_symm huw
      rw [h_w_neigh, Finset.mem_singleton] at h_u_in
      exact h_u_in.symm
  rw [h_bij] at h_card_D
  exact h_card_D

end WrittenOnTheWallII.GraphConjecture315
