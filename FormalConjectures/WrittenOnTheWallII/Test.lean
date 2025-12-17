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

import FormalConjectures.Util.ProblemImports
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Domination
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Invariants
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Definitions


noncomputable def Matrix.IsHermitian.maxEigenvalue {𝕜 : Type*} [Field 𝕜] [RCLike 𝕜]
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ℝ :=
  iSup hA.eigenvalues


namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]


/-- The Wiener index of `G`, which is the sum of distances between all
pairs of vertices. -/
noncomputable def wienerIndex (G : SimpleGraph α) : ℕ :=
  ∑ uv : Sym2 α, uv.lift ⟨fun u v ↦ G.dist u v, by simp [dist_comm]⟩

/-- Auxiliary function for Szeged index: counts vertices closer to u than v. -/
noncomputable def szeged_aux (G : SimpleGraph α) (u v : α) : ℕ :=
  -- Note: this automatically excludes vertices that aren't connected to either u or v,
  -- since their distance will be 0.
  (Finset.univ.filter (fun w => G.dist w u ≠ 0 ∧ G.dist w u <= G.dist w v)).card

/-- The Szeged index of `G`.

This is define as the sum `∑_{uv ∈ E(G)} n_u(u,v) * n_v(u,v)` where
`n_u(uv)` is the number of vertices closer to `u` than `v`.
-/
noncomputable def szegedIndex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  ∑ e ∈ G.edgeFinset,
    e.lift ⟨fun u v => szeged_aux G u v * szeged_aux G v u, by simp [mul_comm]⟩

/-- The average degree of `G`. -/
noncomputable def averageDegree (G : SimpleGraph α) [DecidableRel G.Adj] : ℚ  :=
  (∑ v, (G.degree v : ℚ)) / (Fintype.card α : ℚ)

/-- The multiset of degrees of a graph. -/
def degreeMultiset (G : SimpleGraph α) [DecidableRel G.Adj] : Multiset ℕ :=
  Finset.univ.val.map fun v => G.degree v

/-- The annihilation number of a graph. This is the largest number of degrees that can be added
together without going over the total number of edges of that graph. -/
def annihilationNumber (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  -- Calculate the limit: The number of edges (Sum of degrees / 2)
  let limit := G.edgeFinset.card
  -- The set of all multisets of degrees that sum to less than or equal to `limit`
  Finset.Iic (degreeMultiset G)
    |>.filter (fun S ↦ Multiset.sum S ≤ limit)
    |>.sup Multiset.card

/--
Computes the annihilation number of a graph G.

It calculates the degree sequence, sorts it ascendingly, and finds the largest prefix length 'k'
(where `0 ≤ k ≤ |V(G)|`) such that the sum of the prefix is less than or equal to the sum of the corresponding suffix.
-/
noncomputable def annihilationNumber' (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  -- 1. Get the degree sequence sorted in ascending order.
  -- G.degree_list returns the list of degrees.
  letI degrees := (Finset.univ.image fun v => G.degree v).sort (· ≤ ·)

  -- 2. Define the condition for the annihilation number.
  -- k represents the number of smallest degrees considered (the length of the prefix).
  letI condition (k : ℕ) : Bool := (degrees.take k).sum ≤ (degrees.drop k).sum

  -- 3. Find the maximum k in {0, ..., n} satisfying the condition.
  -- List.range (n + 1) generates the list [0, 1, ..., n].
  letI candidates := (List.range (Fintype.card α + 1)).filter condition

  -- 4. Return the maximum candidate.
  -- The list of candidates is guaranteed to be non-empty because k=0 always satisfies
  -- the condition (0 ≤ sum of all degrees).
  candidates.getLast!

set_option linter.unusedSectionVars false in
-- TODO(Paul-Lez): debug the issue with the unused variable linter...
proof_wanted annihilationNumberEq (G : SimpleGraph α) [DecidableRel G.Adj] :
    annihilationNumber G = annihilationNumber' G

/-!
## Residue
The residue of a graph is the number of zeros remaining after iteratively applying the Havel-Hakimi
algorithm to the degree sequence until all remaining degrees are zero.
-/

/--
Helper function: Performs one step of the Havel-Hakimi reduction on a degree sequence.
Assumes the input list `s` is sorted descending.
Removes the first element `d`, decrements the next `d` elements by 1, and re-sorts the list descending.

Note: when `s` is the list of vertices arising from a simple graph, if the first index is `s` then
the degree list always has length at least `s+1` so this makes sense.
-/
private def havelHakimiStep (s : List ℕ) : List ℕ :=
  match s with
  | [] => []
  | d :: rest =>
    -- Split the rest into the part to decrement (first d elements) and the remaining part.
    let (to_decrement, remaining) := rest.splitAt d
    -- Decrement the elements
    let decremented := to_decrement.map (· - 1)
    -- Combine and re-sort descending.
    (decremented ++ remaining).mergeSort (· ≥ ·)

/--
Auxiliary function to calculate the residue recursively.
Applies Havel-Hakimi steps until the sequence consists only of zeros or is empty.
-/
private partial def residueAux  : List ℕ → ℕ
  | [] => 0        -- Empty sequence, residue is 0.
  | 0 :: s => 1 + s.length -- If the largest degree is 0 (and the list is sorted), all are 0.
  | s => residueAux (havelHakimiStep s) -- Apply one reduction step and recurse.

/--
Computes the residue of a graph G, ,i.e. the number of zeros remaining after iteratively applying the Havel-Hakimi
algorithm to the degree sequence until all remaining degrees are zero.
Starts with the descending degree sequence and applies the Havel-Hakimi process.
-/
noncomputable def residue (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  -- Get the degree sequence sorted in descending order and apply `residueAux`.
  residueAux ((Finset.univ.image fun v => G.degree v).sort (· ≥ ·))

/--
Fractional alpha. This is defined as
$$
\max_x \sum_{v \in V} x_v
$$
subject to $0 \le x_v \le 1$ for all $v \in V$ and
$x_u + x_v \le 1$ whenever $(u, v)$ are connected by an edge.
-/
noncomputable def fractionalAlpha (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  sSup {(∑ i, x i) | (x : α → ℝ) (_ : ∀ v, x v ∈ Set.Icc 0 1)
    (_ : ∀ u v, G.Adj u v → x u + x v ≤ 1)}

/--
Lovász Theta Function (ϑ(G))
The Lovász theta function is defined as:
ϑ(G) = min λ_max(A)
where the minimum is taken over all symmetric matrices A such that:

A_ij = 1 for all i = j (diagonal entries are 1)
A_ij = 0 for all {i,j} ∈ E (entries corresponding to edges are 0)
A is positive semidefinite

Here λ_max(A) denotes the maximum eigenvalue of A.
-/
noncomputable def lovaczThetaFunction
    (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  sInf {(Matrix.IsHermitian.maxEigenvalue hA) | (A : Matrix α α ℝ) (hA : A.IsHermitian)
      (_ : ∀ i, A i i = 1) (_ : ∀ i j, G.Adj i j → A i j = 0)}

/--
Given a simple graph `G` with adjacency matrix `A`, this is the number `n₀ + min n₊ n₋` where:
- `n₀` is the multiplicity of zero as an eigenvalue of `A`
- `n₊` is the number of positive eigenvalues of `A` (counting multiplicities)
- `n₋` is the number of negative eigenvalues of `A` (counting multiplicities)
-/
noncomputable def cvetkovic (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  letI A : Matrix α α ℝ := G.adjMatrix ℝ
  letI spectrum : Multiset ℝ := (Matrix.charpoly A).roots
  letI positive_count : ℕ := spectrum.countP (fun x => 0 < x)
  letI negative_count : ℕ := spectrum.countP (fun x => 0 > x)
  letI zero_count : ℕ := spectrum.countP (fun x => 0 = x)
  zero_count + min positive_count negative_count


end SimpleGraph
/-!
# Testing Graph Invariants

This file contains tests for graph invariants on 5 specific concrete graphs:
1. `HouseGraph`: A graph on 5 vertices.
2. `K4`: The complete graph on 4 vertices.
3. `PetersenGraph`: The Petersen graph on 10 vertices.
4. `C6`: The cycle graph on 6 vertices.
5. `Star5`: The star graph with 5 leaves (6 vertices total).

Tests cover:
independence_number, dominationNumber, average_distance, diameter, radius,
girth, order, size, szeged_index, wiener_index, min_degree, max_degree,
average_degree, matching_number, residue, annihilation_number, cvetkovic.
-/

open SimpleGraph

/-! ### Graph Definitions -/

/-- House Graph: Square 0-1-2-3-0 with roof 4 connected to 2,3. -/
def HouseGraph : SimpleGraph (Fin 5) :=
  SimpleGraph.fromEdgeSet {
    s(0, 1), s(1, 2), s(2, 3), s(3, 0),
    s(2, 4), s(3, 4)
  }
instance : DecidableRel HouseGraph.Adj := by unfold HouseGraph; infer_instance

/-- K4: Complete graph on 4 vertices. -/
def K4 : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet {
    s(0, 1), s(0, 2), s(0, 3),
    s(1, 2), s(1, 3),
    s(2, 3)
  }
instance : DecidableRel K4.Adj := by unfold K4; infer_instance

/-- Petersen Graph on 10 vertices. -/
def PetersenGraph : SimpleGraph (Fin 10) :=
  SimpleGraph.fromEdgeSet {
    -- Outer Cycle
    s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0),
    -- Spokes
    s(0, 5), s(1, 6), s(2, 7), s(3, 8), s(4, 9),
    -- Inner Star
    s(5, 7), s(7, 9), s(9, 6), s(6, 8), s(8, 5)
  }
instance : DecidableRel PetersenGraph.Adj := by unfold PetersenGraph; infer_instance
/- sorry was modified after query, providing completion as comment:
-- AlphaProof failed to close this goal
sorry
-/

/-- C6: Cycle graph on 6 vertices. -/
def C6 : SimpleGraph (Fin 6) :=
  SimpleGraph.fromEdgeSet {
    s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 5), s(5, 0)
  }
instance : DecidableRel C6.Adj := by unfold C6; infer_instance

/-- Star5: Star graph with center 0 and 5 leaves. -/
def Star5 : SimpleGraph (Fin 1 ⊕ Fin 5) := completeBipartiteGraph (Fin 1) (Fin 5)

noncomputable instance : DecidableRel Star5.Adj := by
  unfold Star5
  exact Classical.decRel (completeBipartiteGraph (Fin 1) (Fin 5)).Adj

/-! ### House Graph Tests -/

@[category test, AMS 5]
theorem house_indep : a HouseGraph = 2 := by
  by_contra
  simp_all[a]
  norm_cast at*
  apply (by assumption)
  symm
  show(2) =id _
  convert(csSup_eq_of_forall_le_of_forall_lt_exists_gt _ _ fun R M=>_).symm
  · norm_num[Set.nonempty_def]
    by_contra!
    apply this 0 ∅
    use (nofun)
    rfl
  · norm_num[IsNIndepSet]
    rintro A B@c
    bound
    contrapose! c
    repeat decide+revert
  · use(2)
    bound
    norm_num[IsNIndepSet]
    by_contra!
    use this {}<|by tauto

@[category test, AMS 5]
theorem house_dom : dominationNumber HouseGraph = 2 := by
  (inhabit ℕ)
  use le_antisymm ?_ ?_
  · apply csInf_le'
    norm_num[SimpleGraph.IsNDominatingSet]
    by_contra!
    apply this .univ
    constructor
    · aesop_cat
    norm_num[SimpleGraph.IsNDominatingSet]at*
    apply this .univ
    constructor
    · use fun and=>by simp_all
    norm_num[SimpleGraph.IsNDominatingSet]at*
    apply this .univ
    constructor
    · use fun and=>by simp_all
    norm_num[SimpleGraph.IsNDominatingSet]at*
    apply this {subst |subst % 2 =1}
    constructor
    · simp_all[SimpleGraph.IsNDominatingSet]
      intro
      obtain ⟨@c⟩ :=eq_or_ne (by valid:) 0
      · simp_all[SimpleGraph.IsNDominatingSet,Fin.exists_iff_succ]
        tauto
      obtain ⟨rfl⟩ :=eq_or_ne ‹ Fin 5› (2)
      · exact (.inr (by exists(3)))
      obtain ⟨rfl⟩ :=eq_or_ne (by valid : Fin _) (3)
      · decide
      obtain ⟨@c⟩ :=eq_or_ne ‹ Fin 5› (1)
      · bound
      · use .inr ⟨3,by decide+revert⟩
    · norm_num+decide[ Finset.card_filter, Finset.sum]
  · show(2)≤star _
    cases ↑(Classical.propDecidable _)
    · simp_rw [SimpleGraph.IsNDominatingSet,not_exists]at*
      simp_all[SimpleGraph.IsNDominatingSet]
      apply (by valid:) 5 .univ
      constructor
      · use fun and=>by simp_all
      · rfl
    norm_num[SimpleGraph.IsNDominatingSet]
    rintro(F | S|F) A B@c
    · use absurd c (show¬∀_, _ by aesop)
    · obtain ⟨c, rfl⟩:=(B.card_eq_one).1 ‹_›
      aesop
      contrapose c
      clear*-
      exact show¬ (∀_, _) by decide+revert
    · hint

@[category test, AMS 5]
theorem house_avg_dist : averageDistance HouseGraph = 7/5 := by
  -- AlphaProof failed to close this goal
  sorry

@[category test, AMS 5]
theorem house_diameter : maxEccentricity HouseGraph = 2 := by
  -- AlphaProof failed to close this goal
  sorry

@[category test, AMS 5]
theorem house_radius : minEccentricity HouseGraph = 2 := by
  -- AlphaProof failed to close this goal
  sorry

@[category test, AMS 5]
theorem house_girth : HouseGraph.girth = 3 := by
  -- AlphaProof failed to close this goal
  sorry

@[category test, AMS 5]
theorem house_order : n HouseGraph = 5 := by
  constructor

@[category test, AMS 5]
theorem house_size : HouseGraph.edgeFinset.card = 6 := by
  norm_num +decide

@[category test, AMS 5]
theorem house_szeged : szegedIndex HouseGraph = 24 := by
  -- AlphaProof failed to close this goal
  sorry

@[category test, AMS 5]
theorem house_wiener : wienerIndex HouseGraph = 14 := by
  -- AlphaProof failed to close this goal
  sorry

@[category test, AMS 5]
theorem house_min_deg : HouseGraph.minDegree = 2 := by
  borelize( Fin 03)
  norm_num+decide[SimpleGraph.minDegree,SimpleGraph.degree,← Fintype.card_coe]

@[category test, AMS 5]
theorem house_max_deg : HouseGraph.maxDegree = 3 := by
  (inhabit Int)
  norm_num+decide[SimpleGraph.maxDegree, true,SimpleGraph.degree, true, ← Fintype.card_coe]

@[category test, AMS 5]
theorem house_avg_deg : averageDegree HouseGraph = 12/5 := by
  change (star _) = _
  norm_num+decide[div_eq_mul_inv,SimpleGraph.degree,← Fintype.card_coe]
  exact (congr_arg₂ _) (( Fintype.sum_congr _ _ fun and=>congr_arg _ (Fintype.card_subtype _)).trans (by norm_cast)) rfl

@[category test, AMS 5]
theorem house_matching : m HouseGraph = 2 := by
  -- AlphaProof failed to close this goal
  sorry

@[category test, AMS 5]
theorem house_residue : residue HouseGraph = 2 := by
  sorry

--annihilationNumber HouseGraph

@[category test, AMS 5]
theorem house_annihilation : ¬ (annihilationNumber' HouseGraph = 3) := by
  apply((lt_of_le_of_lt _) (by constructor)).ne
  inhabit Real
  apply Nat.cast_le.2 (show _≤2 from _)
  rw[ Fintype.card_fin,Finset.sort]
  simp_rw [ Finset.image_val,Finset.univ,Multiset.sort]
  norm_num[List.range_succ,Fintype.elems,List.mergeSort_eq_insertionSort]
  simp_all!+decide-contextual[SimpleGraph.degree,← Fintype.card_coe, (Fin.sum_univ_five), (List.finRange_succ)]


@[category test, AMS 5]
theorem house_cvetkovic : cvetkovic HouseGraph = 3 := by
  sorry


/-! ### K4 Tests -/

@[category test, AMS 5]
theorem K4_indep : a K4 = 1 := by
  sorry

@[category test, AMS 5]
theorem K4_dom : dominationNumber K4 = 1 := by
  sorry
  -- (inhabit Int)
  -- delta dominationNumber
  -- norm_num[SimpleGraph.IsNDominatingSet,Fin.eq_zero,Set.setOf_exists,IsLeast.csInf_eq<|Nat.isLeast_find ⟨1, _⟩]
  -- norm_num[SimpleGraph.IsNDominatingSet, true,Set.iUnion_setOf]
  -- convert IsLeast.csInf_eq ⟨_, _⟩
  -- · norm_num[SimpleGraph.IsNDominatingSet]
  --   by_contra!
  --   apply this .univ
  --   constructor
  --   · aesop_cat
  --   norm_num[Finset.card_eq_one,Finset.ext_iff]
  --   apply this .univ
  --   use fun and=>?_
  --   · norm_num[SimpleGraph.IsNDominatingSet, Finset.card_eq_one, Finset.ext_iff]at*
  --     apply this {0}
  --     constructor
  --     · norm_num[K4,SimpleGraph.IsNDominatingSet]at*
  --       norm_num+decide[SimpleGraph.IsDominating]
  --     · rfl
  --   · bound
  -- · norm_num[SimpleGraph.IsNDominatingSet, mem_lowerBounds]
  --   norm_num[SimpleGraph.IsNDominatingSet,Nat.one_le_iff_ne_zero]
  --   rintro-h h@c
  --   cases h
  --   aesop
  --   revert‹_›
  --   apply not_forall.2
  --   norm_num


@[category test, AMS 5]
theorem K4_avg_dist : averageDistance K4 = 1 := by
  sorry

@[category test, AMS 5]
theorem K4_diameter : maxEccentricity K4 = 1 := by
  sorry

@[category test, AMS 5]
theorem K4_radius : minEccentricity K4 = 1 := by
  sorry

@[category test, AMS 5]
theorem K4_girth : K4.girth = 3 := by
  sorry

@[category test, AMS 5]
theorem K4_order : n K4 = 4 := by
  subsingleton

@[category test, AMS 5]
theorem K4_size : K4.edgeFinset.card = 6 := by
  delta K4
  (simp_all+decide-contextual)

@[category test, AMS 5]
theorem K4_szeged : szegedIndex K4 = 6 := by
  sorry

@[category test, AMS 5]
theorem K4_wiener : wienerIndex K4 = 6 := by
  sorry

@[category test, AMS 5]
theorem K4_min_deg : K4.minDegree = 3 := by
  sorry

@[category test, AMS 5]
theorem K4_max_deg : K4.maxDegree = 3 := by
  sorry

@[category test, AMS 5]
theorem K4_avg_deg : averageDegree K4 = 3 := by
  sorry

@[category test, AMS 5]
theorem K4_matching : m K4 = 2 := by
  sorry

@[category test, AMS 5]
theorem K4_residue : residue K4 = 1 := by
  sorry

@[category test, AMS 5]
theorem K4_annihilation : annihilationNumber K4 = 2 := by
  sorry

@[category test, AMS 5]
theorem K4_cvetkovic : cvetkovic K4 = 1 := by
  sorry


/-! ### Petersen Graph Tests -/

@[category test, AMS 5]
theorem petersen_indep : a PetersenGraph = 4 := by
  sorry

@[category test, AMS 5]
theorem petersen_dom : dominationNumber PetersenGraph = 3 := by
  sorry

@[category test, AMS 5]
theorem petersen_avg_dist : averageDistance PetersenGraph = 5/3 := by
  sorry

@[category test, AMS 5]
theorem petersen_diameter : maxEccentricity PetersenGraph = 2 := by
  sorry

@[category test, AMS 5]
theorem petersen_radius : minEccentricity PetersenGraph = 2 := by
  sorry

@[category test, AMS 5]
theorem petersen_girth : PetersenGraph.girth = 5 := by
  sorry

@[category test, AMS 5]
theorem petersen_order : n PetersenGraph = 10 := by
  sorry

@[category test, AMS 5]
theorem petersen_size : PetersenGraph.edgeFinset.card = 15 := by
  sorry

@[category test, AMS 5]
theorem petersen_szeged : szegedIndex PetersenGraph = 135 := by
  sorry

@[category test, AMS 5]
theorem petersen_wiener : wienerIndex PetersenGraph = 75 := by
  sorry

@[category test, AMS 5]
theorem petersen_min_deg : PetersenGraph.minDegree = 3 := by
  sorry

@[category test, AMS 5]
theorem petersen_max_deg : PetersenGraph.maxDegree = 3 := by
  sorry

@[category test, AMS 5]
theorem petersen_avg_deg : averageDegree PetersenGraph = 3 := by
  sorry

@[category test, AMS 5]
theorem petersen_matching : m PetersenGraph = 5 := by
  sorry

@[category test, AMS 5]
theorem petersen_residue : residue PetersenGraph = 3 := by
  sorry

@[category test, AMS 5]
theorem petersen_annihilation : annihilationNumber PetersenGraph = 5 := by
  sorry

@[category test, AMS 5]
theorem petersen_cvetkovic : cvetkovic PetersenGraph = 4 := by
  sorry


/-! ### C6 Tests -/

@[category test, AMS 5]
theorem C6_indep : a C6 = 3 := by
  sorry

@[category test, AMS 5]
theorem C6_dom : dominationNumber C6 = 2 := by
  sorry --could be solved before

@[category test, AMS 5]
theorem C6_avg_dist : averageDistance C6 = 9/5 := by
  sorry

@[category test, AMS 5]
theorem C6_diameter : maxEccentricity C6 = 3 := by
  sorry

@[category test, AMS 5]
theorem C6_radius : minEccentricity C6 = 3 := by
  sorry

@[category test, AMS 5]
theorem C6_girth : C6.girth = 6 := by
  sorry

@[category test, AMS 5]
theorem C6_order : n C6 = 6 := by
  sorry

@[category test, AMS 5]
theorem C6_size : C6.edgeFinset.card = 6 := by push_cast +decide[C6.edgeFinset_card]

@[category test, AMS 5]
theorem C6_szeged : szegedIndex C6 = 54 := by
  sorry

@[category test, AMS 5]
theorem C6_wiener : wienerIndex C6 = 27 := by
  sorry

@[category test, AMS 5]
theorem C6_min_deg : C6.minDegree = 2 := by constructor

@[category test, AMS 5]
theorem C6_max_deg : C6.maxDegree = 2 := by (inhabit ℕ)
                                            norm_num[C6, maxDegree]
                                            rw[le_antisymm_iff]
                                            bound

@[category test, AMS 5]
theorem C6_avg_deg : averageDegree C6 = 2 := by inhabit Real
                                                apply(mul_comm _ _).trans
                                                exact (inv_mul_eq_iff_eq_mul₀ (by decide)).mpr (by norm_cast)

@[category test, AMS 5]
theorem C6_matching : m C6 = 3 := by
  sorry

@[category test, AMS 5]
theorem C6_residue : residue C6 = 2 := by
  sorry

@[category test, AMS 5]
theorem C6_annihilation : annihilationNumber C6 = 3 := by
  sorry

@[category test, AMS 5]
theorem C6_cvetkovic : cvetkovic C6 = 3 := by
  sorry


/-! ### Star5 Tests -/

@[category test, AMS 5]
theorem Star5_indep : a Star5 = 5 := by
  sorry

@[category test, AMS 5]
theorem Star5_dom : dominationNumber Star5 = 1 := by
  sorry

@[category test, AMS 5]
theorem Star5_avg_dist : averageDistance Star5 = 5/3 := by
  sorry

@[category test, AMS 5]
theorem Star5_diameter : maxEccentricity Star5 = 2 := by
  sorry

@[category test, AMS 5]
theorem Star5_radius : minEccentricity Star5 = 1 := by
  sorry

@[category test, AMS 5]
theorem Star5_girth : Star5.egirth = ⊤ := by
  sorry

@[category test, AMS 5]
theorem Star5_order : n Star5 = 6 := by
  sorry

@[category test, AMS 5]
theorem Star5_size : Star5.edgeFinset.card = 5 := by
  sorry

@[category test, AMS 5]
theorem Star5_szeged : szegedIndex Star5 = 25 := by
  sorry

@[category test, AMS 5]
theorem Star5_wiener : wienerIndex Star5 = 25 := by
  sorry

@[category test, AMS 5]
theorem Star5_min_deg : Star5.minDegree = 1 := by
  sorry

@[category test, AMS 5]
theorem Star5_max_deg : Star5.maxDegree = 5 := by
  sorry

@[category test, AMS 5]
theorem Star5_avg_deg : averageDegree Star5 = 5/3 := by
  unfold averageDegree
  norm_num+decide[ZMod,SimpleGraph.degree, ←↑ Fintype.card_coe]
  norm_num+decide[Star5, Fintype.card_subtype,Finset.card_filter, Fintype.sum_sum_type _, Fin.sum_univ_five _,id]

@[category test, AMS 5]
theorem Star5_matching : m Star5 = 1 := by
  sorry

@[category test, AMS 5]
theorem Star5_residue : residue Star5 = 5 := by
  sorry

@[category test, AMS 5]
theorem Star5_annihilation : annihilationNumber Star5 = 5 := by
  sorry

@[category test, AMS 5]
theorem Star5_cvetkovic : cvetkovic Star5 = 5 := by
  sorry
