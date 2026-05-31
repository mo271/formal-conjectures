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
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.GraphConjectures.WellTotallyDominated

/-!
# Helper definitions and lemmas for WOWII Conjecture 315

Supporting definitions and properties of pendant vertices and their neighborhoods,
used in the proof of Conjecture 315.
-/

set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false
set_option linter.style.namespace false

open Classical
open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The set of neighbors of pendant vertices. -/
noncomputable def pendantNeighbors (G : SimpleGraph α) [DecidableRel G.Adj] : Finset α :=
  (pendantVertices G).biUnion (fun v => G.neighborFinset v)

/-- P is an independent set. -/
lemma P_is_independent (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : G.indepNum = (pendantVertices G).card) :
    G.IsIndepSet (pendantVertices G) := by
  intro u hu v hv huv
  have hu1 : G.degree u = 1 := by
    simp only [pendantVertices, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact hu
  have hv1 : G.degree v = 1 := by
    simp only [pendantVertices, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    exact hv
  intro hadj
  have h_nu : G.neighborFinset u = {v} := by
    ext x
    simp only [Finset.mem_singleton]
    constructor
    · intro hx
      have hcard : (G.neighborFinset u).card = 1 := hu1
      rw [Finset.card_eq_one] at hcard
      rcases hcard with ⟨a, ha⟩
      have hx' : x ∈ G.neighborFinset u := hx
      have hv' : v ∈ G.neighborFinset u := by rwa [mem_neighborFinset]
      rw [ha] at hx' hv'
      simp only [Finset.mem_singleton] at hx' hv'
      rw [hx', hv']
    · intro hx
      subst hx
      rwa [mem_neighborFinset]
  have h_nv : G.neighborFinset v = {u} := by
    ext x
    simp only [Finset.mem_singleton]
    constructor
    · intro hx
      have hcard : (G.neighborFinset v).card = 1 := hv1
      rw [Finset.card_eq_one] at hcard
      rcases hcard with ⟨a, ha⟩
      have hx' : x ∈ G.neighborFinset v := hx
      have hu' : u ∈ G.neighborFinset v := by
        rw [mem_neighborFinset]
        exact G.adj_symm hadj
      rw [ha] at hx' hu'
      simp only [Finset.mem_singleton] at hx' hu'
      rw [hx', hu']
    · intro hx
      subst hx
      rw [mem_neighborFinset]
      exact G.adj_symm hadj
  have h_reach_uv : ∀ n (w y : α) (p : G.Walk w y), (w = u ∨ w = v) → p.length = n → y = u ∨ y = v := by
    intro n
    induction n with
    | zero =>
      intro w y p hw hp
      cases p
      · exact hw
      · contradiction
    | succ n ih =>
      intro w y p hw hp
      cases p with
      | nil => exact hw
      | cons h_adj p' =>
        rename_i v'
        have hp' : p'.length = n := by
          simp only [Walk.length_cons] at hp
          exact Nat.succ.inj hp
        have hw' : v' = u ∨ v' = v := by
          rcases hw with hw_u | hw_v
          · have hc : v' ∈ G.neighborFinset w := by rwa [mem_neighborFinset]
            rw [hw_u] at hc
            rw [h_nu, Finset.mem_singleton] at hc
            exact Or.inr hc
          · have hc : v' ∈ G.neighborFinset w := by rwa [mem_neighborFinset]
            rw [hw_v] at hc
            rw [h_nv, Finset.mem_singleton] at hc
            exact Or.inl hc
        exact ih _ _ p' hw' hp'
  have h_univ : Finset.univ = ({u, v} : Finset α) := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    have h_reach := hG u x
    rcases h_reach with ⟨p⟩
    have hx := h_reach_uv p.length u x p (Or.inl rfl) rfl
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have h_card_univ : (Finset.univ : Finset α).card = 2 := by
    rw [h_univ]
    exact Finset.card_pair huv
  have h_P_card : (pendantVertices G).card = 2 := by
    have h_P_eq : pendantVertices G = {u, v} := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro _
        have h_in : x ∈ ({u, v} : Finset α) := by
          rw [← h_univ]
          exact Finset.mem_univ x
        simp only [Finset.mem_insert, Finset.mem_singleton] at h_in
        exact h_in
      · intro hx
        rcases hx with rfl | rfl
        · exact hu
        · exact hv
    rw [h_P_eq]
    exact Finset.card_pair huv
  have h_indep : G.indepNum = 2 := by
    rw [h, h_P_card]
  have h_ex := G.exists_isNIndepSet_indepNum
  rw [h_indep] at h_ex
  rcases h_ex with ⟨S, hS⟩
  have hS_indep : G.IsIndepSet S := hS.1
  have hS_card : S.card = 2 := hS.2
  have hS_sub : S ⊆ Finset.univ := Finset.subset_univ S
  rw [h_univ] at hS_sub
  have hS_eq : S = {u, v} := by
    exact Finset.eq_of_subset_of_card_le hS_sub (by rw [hS_card, Finset.card_pair huv])
  rw [hS_eq] at hS_indep
  have h_not_adj : ¬ G.Adj u v := by
    apply hS_indep
    · exact Finset.mem_insert_self u {v}
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
    · exact huv
  exact h_not_adj hadj

/-- If α(G) = |P|, then every vertex is in P or N(P). -/
lemma V_eq_P_union_N (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected) (h : G.indepNum = (pendantVertices G).card) :
    Finset.univ = pendantVertices G ∪ pendantNeighbors G := by
  ext v
  simp only [Finset.mem_univ, Finset.mem_union, true_iff]
  by_contra h_not
  push_neg at h_not
  rcases h_not with ⟨hvP, hvN⟩
  have h_indep : G.IsIndepSet (insert v (pendantVertices G) : Set α) := by
    intro x hx y hy hxy h_adj
    simp only [Set.mem_insert_iff, Finset.mem_coe] at hx hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact hxy rfl
      · have h_in_N : x ∈ pendantNeighbors G := by
          unfold pendantNeighbors
          simp only [Finset.mem_biUnion]
          use y
          constructor
          · exact hy
          · rw [mem_neighborFinset]
            exact h_adj.symm
        exact hvN h_in_N
    · rcases hy with rfl | hy
      · have h_in_N : y ∈ pendantNeighbors G := by
          unfold pendantNeighbors
          simp only [Finset.mem_biUnion]
          use x
          constructor
          · exact hx
          · rw [mem_neighborFinset]
            exact h_adj
        exact hvN h_in_N
      · exact P_is_independent G hG h hx hy hxy h_adj
  have h_indep' : G.IsIndepSet (insert v (pendantVertices G) : Finset α) := by
    convert h_indep using 1
    ext x
    simp only [Finset.coe_insert]
  have h_card : (insert v (pendantVertices G)).card = (pendantVertices G).card + 1 := by
    exact Finset.card_insert_of_notMem hvP
  have h_le : (insert v (pendantVertices G)).card ≤ G.indepNum := by
    apply SimpleGraph.IsIndepSet.card_le_indepNum h_indep'
  rw [h, h_card] at h_le
  omega
