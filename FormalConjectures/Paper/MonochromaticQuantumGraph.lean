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

/-!
# Monochromatic quantum graphs (inherited vertex colorings)

This file studies the existence of *monochromatic quantum graphs*: edge-coloured, edge-weighted
complete graphs whose perfect matchings induce vertex colourings, with the property that

- every **non-monochromatic** inherited vertex colouring has total weight `0`, while
- each of the `D` **monochromatic** colourings has total weight `1`.

In the quantum-optics motivation, such a construction corresponds to generating high-dimensional
multipartite GHZ-type states using probabilistic pair sources and linear optics (without additional
resources), where interference patterns can be expressed as weighted sums over perfect matchings.

## Main questions (informal)

- For `N = 4` and `D ≥ 4`, does there exist such a graph/weighting?
- For even `N ≥ 6` and `D ≥ 3`, does there exist such a graph/weighting?

## Formalisation sketch

A quantum graph with `N` vertices and `D` colours can be encoded by a weight function
`W : EdgeN N D α → α` (for a coefficient domain `α`).

For each assignment of vertex indices `ι : V N → Fin D`, we define a perfect-matching sum
`pmSumN N D W ι` (a sum over perfect matchings, where each matching contributes the product of the
corresponding edge weights determined by `ι`). The equation system `EqSystemN N D W` requires

`pmSumN N D W ι = 1` iff `ι` is constant (all entries equal), and `0` otherwise.

The open conjectures in this file ask for non-existence/existence of such `W` over various
coefficient domains (e.g. `ℂ`, `ℝ`, `ℤ`, and restricted integer weights).

## References

* [Krenn2017] M. Krenn, X. Gu, A. Zeilinger,
  "Quantum Experiments and Graphs: Multiparty States as Coherent Superpositions of Perfect Matchings",
  *Physical Review Letters* 119(24), 240403 (2017).

* [MO2018] [Vertex coloring inherited from perfect matchings (motivated by quantum physics)](https://mathoverflow.net/questions/311325),
  MathOverflow question 311325.

* [Gu2019] X. Gu, M. Erhard, A. Zeilinger, M. Krenn,
  "Quantum experiments and graphs II: Quantum interference, computation, and state generation",
  *PNAS* 116(10), 4147–4155 (2019).

* [Krenn2019] [Questions on the Structure of Perfect Matchings inspired by Quantum Physics](https://arxiv.org/abs/1902.06023)
  by *M. Krenn, X. Gu, U. Soltész*,
  Proc. 2nd Croatian Combinatorial Days, 57–70 (2019).

* [Chandran2022] [Edge-coloured graphs with only monochromatic perfect matchings and their connection to quantum physics](https://arxiv.org/abs/2202.05562)
  by *N. Chandran, S. Gajjala* (2022).

* [Chandran2024] [Krenn–Gu conjecture for sparse graphs](https://arxiv.org/abs/2407.00303)
  by *N. Chandran, S. Gajjala, S. Illickan, M. Krenn*, MFCS 2024.
-/

open scoped Matrix
open scoped NNReal

namespace MonochromaticQuantumGraph

/-- Vertices of $K_N$. -/
abbrev V (N : Nat) := Fin N

/-- Edge label for $K_N$ with endpoint indices in `Fin D`.

We *intend* to build edges only with `u < v` (so undirected edges are represented once),
and our enumeration always pairs the first vertex in an ordered list with a later vertex.
-/
structure EdgeN (N D : Nat) where
  u : V N
  v : V N
  i : Fin D
  j : Fin D
deriving DecidableEq

/-- Weights on edges. -/
abbrev WeightsN (N D : Nat) (α : Type) := EdgeN N D → α

/-- Helper: build an `EdgeN` from endpoints and endpoint indices. -/
def mkEdge {N D : Nat} (u v : V N) (i j : Fin D) : EdgeN N D :=
  ⟨u, v, i, j⟩

/-- Ordered vertex list $[0, 1, \ldots, N-1]$. -/
def vertices : (N : Nat) → List (V N)
  | 0 => []
  | N + 1 =>
      (0 : Fin (N + 1)) :: (vertices N).map Fin.succ

/-
## `allEqual`: "all indices are equal"

We package the property "all indices `ι v` are equal" as a chain condition along a vertex list.

Concretely, `allEqualList ι L` means that the relation `ι v = ι w` holds between adjacent elements
of `L`. We implement this with `List.IsChain`, which is convenient for later reasoning and provides
good simp/decidability support.
-/

/-- Chain-equality along a list of vertices. -/
def allEqualList {N D : Nat} (ι : V N → Fin D) (L : List (V N)) : Prop :=
  List.IsChain (fun v w => ι v = ι w) L

/-- All indices equal on `Fin N` (using the canonical ordered vertex list). -/
def allEqual {N D : Nat} (ι : V N → Fin D) : Prop :=
  allEqualList ι (vertices N)

/-- Instance: `allEqualList ι L` is decidable. -/
instance {N D : Nat} (ι : V N → Fin D) (L : List (V N)) :
    Decidable (allEqualList ι L) := by
  letI : DecidableRel (fun v w : V N => ι v = ι w) := fun v w => inferInstance
  unfold allEqualList
  infer_instance

/-- Instance: `allEqual ι` is decidable. -/
instance {N D : Nat} (ι : V N → Fin D) : Decidable (allEqual ι) := by
  unfold allEqual
  infer_instance

/-
## Perfect matching sum, general `N`

Fix a semiring `α`, a weight function `W : WeightsN N D α`, and an index assignment
`ι : V N → Fin D`. The next definitions compute the sum over perfect matchings of the complete graph
on `N` vertices, where each edge is selected with the endpoint indices given by `ι`.

We define an auxiliary function `pmSumListAux W ι n L` with a decreasing fuel parameter `n`
(used only for termination). In the intended use, we call it with `n = L.length`.

Intuition (when `n = L.length`):

* `n = 0` : the empty matching contributes `1` (empty product).
* `n = 1` : odd number of vertices, so no perfect matchings; value `0`.
* `n = n' + 2` and `L = v :: vs`:
  pair `v` with each `u ∈ vs`, multiply the edge weight by the recursive contribution on the
  remaining vertices `vs.erase u`, and sum over `u`.
-/

/-- Auxiliary perfect-matching sum on a vertex list, using a fuel parameter `n` for termination.

When called as `pmSumListAux W ι L.length L`, this computes the weighted sum over all perfect
matchings on the vertices in `L`. The recursion pairs the head vertex with each later vertex and
recurses on the remaining vertices.

For lists of odd length, there are no perfect matchings and the value is `0`. -/
def pmSumListAux {α : Type} [Semiring α] {N D : Nat}
    (W : WeightsN N D α) (ι : V N → Fin D) :
    Nat → List (V N) → α
  | 0, _ => 1
  | 1, _ => 0
  | _ + 2, [] => 1
  | _ + 2, [_] => 0
  | n + 2, v :: vs =>
      (vs.map (fun u =>
          W (mkEdge v u (ι v) (ι u)) *
            pmSumListAux W ι n (vs.erase u)
        )).sum

/-- Perfect-matching sum on a list: run `pmSumListAux` with `fuel = L.length`. -/
def pmSumList {α : Type} [Semiring α] {N D : Nat}
    (W : WeightsN N D α) (ι : V N → Fin D) (L : List (V N)) : α :=
  pmSumListAux W ι L.length L

/-- The perfect-matching sum for $K_N$: use the canonical ordered vertex list `vertices N`. -/
def pmSumN {α : Type} [Semiring α] (N D : Nat)
    (W : WeightsN N D α) (ι : V N → Fin D) : α :=
  pmSumList W ι (vertices N)

/-- The monochromatic quantum graph equation system for $K_N$.

For every index assignment $\iota : V_N \to \mathrm{Fin}\, D$, the perfect-matching sum equals $1$
if $\iota$ is constant (monochromatic inherited vertex colouring), and equals $0$ otherwise. -/
def EqSystemN {α : Type} [Semiring α] (N D : Nat) (W : WeightsN N D α) : Prop :=
  ∀ ι : V N → Fin D,
    pmSumN N D W ι =
      (if allEqual ι then (1 : α) else (0 : α))

/-
# Witnesses & theorems (sanity checks)

These proofs are computation-heavy (`fin_cases` + `simp`), so we increase the heartbeat limit locally.
-/

/- ## N = 4, D = 2 (works over any semiring α): witness & proof -/
section N4_D2
variable {α : Type} [Semiring α]

def Witness4_d2 : WeightsN 4 2 α :=
  fun e =>
    if e = mkEdge 0 1 0 0 then (1 : α) else
    if e = mkEdge 2 3 0 0 then (1 : α) else
    if e = mkEdge 0 2 1 1 then (1 : α) else
    if e = mkEdge 1 3 1 1 then (1 : α) else
    (0 : α)

set_option maxHeartbeats 5000000 in
@[category test, AMS 5 14 81]
theorem eqSystem4_has_solution_d2 :
    ∃ W : WeightsN 4 2 α, EqSystemN 4 2 W := by
  classical
  refine ⟨Witness4_d2 (α := α), ?_⟩
  intro ι

  have h :
      ∀ a b c d : Fin 2,
        pmSumN 4 2 (W := Witness4_d2 (α := α)) ![a, b, c, d] =
          (if allEqual ![a, b, c, d] then (1 : α) else (0 : α)) := by
    intro a b c d
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [pmSumN, pmSumList, pmSumListAux, vertices,
        allEqual, allEqualList, Witness4_d2, mkEdge]

  have hι : ι = ![ι 0, ι 1, ι 2, ι 3] := by
    funext k
    fin_cases k <;> simp

  rw [hι]
  exact h (ι 0) (ι 1) (ι 2) (ι 3)

end N4_D2

/- ## N = 4, D = 3 over ℂ: witness & proof -/

def Witness4_d3 : WeightsN 4 3 ℂ :=
  fun e =>
    if e = mkEdge 0 1 0 0 then (1 : ℂ) else
    if e = mkEdge 2 3 0 0 then (1 : ℂ) else
    if e = mkEdge 0 2 1 1 then (1 : ℂ) else
    if e = mkEdge 1 3 1 1 then (1 : ℂ) else
    if e = mkEdge 0 3 2 2 then (1 : ℂ) else
    if e = mkEdge 1 2 2 2 then (1 : ℂ) else
    (0 : ℂ)

set_option maxHeartbeats 5000000 in
@[category test, AMS 5 14 81]
theorem eqSystem4_has_solution_d3 :
    ∃ W : WeightsN 4 3 ℂ, EqSystemN 4 3 W := by
  classical
  refine ⟨Witness4_d3, ?_⟩
  intro ι

  have h :
      ∀ a b c d : Fin 3,
        pmSumN 4 3 (W := Witness4_d3) ![a, b, c, d] =
          (if allEqual ![a, b, c, d] then (1 : ℂ) else (0 : ℂ)) := by
    intro a b c d
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [pmSumN, pmSumList, pmSumListAux, vertices,
        allEqual, allEqualList, Witness4_d3, mkEdge]

  have hι : ι = ![ι 0, ι 1, ι 2, ι 3] := by
    funext k
    fin_cases k <;> simp

  rw [hι]
  exact h (ι 0) (ι 1) (ι 2) (ι 3)

/- ## N = 6, D = 2 (works over any semiring α): witness & proof -/
section N6_D2
variable {α : Type} [Semiring α]

def Witness6_d2 : WeightsN 6 2 α :=
  fun e =>
    if e = mkEdge 0 1 0 0 then (1 : α) else
    if e = mkEdge 2 3 0 0 then (1 : α) else
    if e = mkEdge 4 5 0 0 then (1 : α) else
    if e = mkEdge 0 5 1 1 then (1 : α) else
    if e = mkEdge 1 2 1 1 then (1 : α) else
    if e = mkEdge 3 4 1 1 then (1 : α) else
    (0 : α)

set_option maxHeartbeats 5000000 in
@[category test, AMS 5 14 81]
theorem eqSystem6_has_solution_d2 :
    ∃ W : WeightsN 6 2 α, EqSystemN 6 2 W := by
  classical
  refine ⟨Witness6_d2 (α := α), ?_⟩
  intro ι

  have h :
      ∀ a b c d e f : Fin 2,
        pmSumN 6 2 (W := Witness6_d2 (α := α)) ![a, b, c, d, e, f] =
          (if allEqual ![a, b, c, d, e, f] then (1 : α) else (0 : α)) := by
    intro a b c d e f
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
    fin_cases d <;> fin_cases e <;> fin_cases f <;>
      simp [pmSumN, pmSumList, pmSumListAux, vertices,
        allEqual, allEqualList, Witness6_d2, mkEdge]

  have hι : ι = ![ι 0, ι 1, ι 2, ι 3, ι 4, ι 5] := by
    funext k
    fin_cases k <;> simp

  rw [hι]
  exact h (ι 0) (ι 1) (ι 2) (ι 3) (ι 4) (ι 5)

end N6_D2

/-
# Known obstruction for nonnegative real weights (Bogdanov)

Informal proof ("Bogdanov's lemma"): see
[MathOverflow answer](https://mathoverflow.net/a/311021/531914).

We record it as `research solved` statements over `ℝ≥0`, without formalizing the proof here.
-/

/-- Bogdanov: for $N = 4$ and all $D \geq 4$, no solution exists over $\mathbb{R}_{\geq 0}$. -/
@[category research solved, AMS 5 14 81]
theorem eqSystem4_no_solution_nnreal_ge4 :
    ∀ D : Nat, D ≥ 4 →
      ¬ ∃ W : WeightsN 4 D ℝ≥0, EqSystemN 4 D W := by
  sorry

/-- Bogdanov: for all even $N \geq 6$ and $D \geq 3$, no solution exists over $\mathbb{R}_{\geq 0}$. -/
@[category research solved, AMS 5 14 81]
theorem eqSystem_no_solution_nnreal_even_ge6_ge3 :
    ∀ N D : Nat,
      N ≥ 6 → Even N → D ≥ 3 →
        ¬ ∃ W : WeightsN N D ℝ≥0, EqSystemN N D W := by
  sorry

/-
# Open conjectures

We state the same family of "no-solution" conjectures for multiple coefficient domains:

* `ℂ` (complex)
* `ℝ` (real)
* `ℤ` (integers)
* `{-1,0,1} ⊆ ℤ` (integer weights restricted pointwise to -1/0/1)

All "general" conjectures are restricted to even `N`.
-/

/- ## Open conjectures over ℂ -/

def A (W : WeightsN 4 4 ℂ) (i j : Fin 4) : ℂ := W (mkEdge 0 1 i j)
def B (W : WeightsN 4 4 ℂ) (k l : Fin 4) : ℂ := W (mkEdge 2 3 k l)
def C (W : WeightsN 4 4 ℂ) (i k : Fin 4) : ℂ := W (mkEdge 0 2 i k)
def D (W : WeightsN 4 4 ℂ) (j l : Fin 4) : ℂ := W (mkEdge 1 3 j l)
def E (W : WeightsN 4 4 ℂ) (i l : Fin 4) : ℂ := W (mkEdge 0 3 i l)
def F (W : WeightsN 4 4 ℂ) (j k : Fin 4) : ℂ := W (mkEdge 1 2 j k)

noncomputable def b (W : WeightsN 4 4 ℂ) (k : Fin 4) : ℂ := ∑ l : Fin 4, B W k l
noncomputable def d (W : WeightsN 4 4 ℂ) (j : Fin 4) : ℂ := ∑ l : Fin 4, D W j l
noncomputable def e (W : WeightsN 4 4 ℂ) (i : Fin 4) : ℂ := ∑ l : Fin 4, E W i l

lemma pmSum_eq (W : WeightsN 4 4 ℂ) (i j k l : Fin 4) :
  let ι : V 4 → Fin 4 := fun x => if x = 0 then i else if x = 1 then j else if x = 2 then k else l;
  pmSumN 4 4 W ι = A W i j * B W k l + C W i k * D W j l + E W i l * F W j k := by
  delta pmSumN V A B C D E F
  simp_all +decide -contextual[pmSumList, true,vertices, false,↑ ky /em']
  simp_all! -contextual [add_assoc]

lemma delta_eq (i j k l : Fin 4) :
  let ι : V 4 → Fin 4 := fun x => if x = 0 then i else if x = 1 then j else if x = 2 then k else l;
  (if allEqual ι then (1 : ℂ) else 0) =
  if i = j ∧ j = k ∧ k = l then 1 else 0 := by
  delta allEqual V
  simp_all-contextual[vertices,allEqualList, Fin.forall_fin_succ]

lemma sum_l_eq (W : WeightsN 4 4 ℂ) (hW : EqSystemN 4 4 W) (i j k : Fin 4) :
  A W i j * b W k + C W i k * d W j + e W i * F W j k =
  if i = j ∧ j = k then 1 else 0 := by
  have h1 : ∑ l : Fin 4, pmSumN 4 4 W (fun x => if x = 0 then i else if x = 1 then j else if x = 2 then k else l) =
            ∑ l : Fin 4, (if i = j ∧ j = k ∧ k = l then (1 : ℂ) else 0) := by
    push_cast[pmSumN, V,EqSystemN]at*
    simp_all!-contextual[allEqual,Fin.forall_iff_succ]
    norm_num+decide[allEqualList,and_assoc]
  delta V pmSumN EqSystemN e F A b C d at*
  linear_combination2(norm:=norm_num+decide[iInf,pmSumList,B,D,E,vertices, Fin.sum_univ_four, Finset.sum_mul, Finset.mul_sum,ite_and, Finset.sum_add_distrib])h1
  clear *-
  simp_all! -contextual
  ring

lemma exists_v (e_vec : Fin 4 → ℂ) :
  ∃ v : Fin 4 → ℂ, (∑ i, v i * e_vec i) = 0 ∧
  ((v 0 = 1 ∧ v 1 = 1 ∧ v 2 = 1) ∨
   (v 0 = 1 ∧ v 1 = 1 ∧ v 3 = 1) ∨
   (v 0 = 1 ∧ v 2 = 1 ∧ v 3 = 1) ∨
   (v 1 = 1 ∧ v 2 = 1 ∧ v 3 = 1)) := by
  by_cases h0 : e_vec 0 ≠ 0
  · use fun i => if i = 0 then -(e_vec 1 + e_vec 2 + e_vec 3) / e_vec 0 else 1
    simp_all[ Fin.sum_univ_four, add_assoc]
  · by_cases h1 : e_vec 1 ≠ 0
    · use fun i => if i = 1 then -(e_vec 0 + e_vec 2 + e_vec 3) / e_vec 1 else 1
      simp_all[ Fin.sum_univ_four, add_assoc]
    · by_cases h2 : e_vec 2 ≠ 0
      · use fun i => if i = 2 then -(e_vec 0 + e_vec 1 + e_vec 3) / e_vec 2 else 1
        simp_all[ Fin.sum_univ_four]
      · by_cases h3 : e_vec 3 ≠ 0
        · use fun i => if i = 3 then -(e_vec 0 + e_vec 1 + e_vec 2) / e_vec 3 else 1
          simp_all [ Fin.sum_univ_four]
        · use fun _ => 1
          simp_all[ Fin.sum_univ_four]

noncomputable def x_vec (W : WeightsN 4 4 ℂ) (v : Fin 4 → ℂ) (j : Fin 4) : ℂ := ∑ i, v i * A W i j
noncomputable def y_vec (W : WeightsN 4 4 ℂ) (v : Fin 4 → ℂ) (k : Fin 4) : ℂ := ∑ i, v i * C W i k

lemma sum_i_eq (W : WeightsN 4 4 ℂ) (hW : EqSystemN 4 4 W) (v : Fin 4 → ℂ)
  (hv : ∑ i, v i * e W i = 0) (j k : Fin 4) :
  x_vec W v j * b W k + d W j * y_vec W v k = if j = k then v j else 0 := by
  have h1 : (∑ i, v i * (A W i j * b W k + C W i k * d W j + e W i * F W j k)) =
            ∑ i, v i * (if i = j ∧ j = k then (1 : ℂ) else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [sum_l_eq W hW i j k]
  have h3 : (∑ i, v i * (A W i j * b W k + C W i k * d W j + e W i * F W j k)) =
            x_vec W v j * b W k + d W j * y_vec W v k := by
    calc
      _ = ∑ i, (v i * A W i j * b W k + v i * C W i k * d W j + v i * e W i * F W j k) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, v i * A W i j * b W k) + (∑ i, v i * C W i k * d W j) + (∑ i, v i * e W i * F W j k) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = (∑ i, v i * A W i j) * b W k + (∑ i, v i * C W i k) * d W j + (∑ i, v i * e W i) * F W j k := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
      _ = x_vec W v j * b W k + y_vec W v k * d W j + 0 * F W j k := by
        rw [hv]
        rfl
      _ = x_vec W v j * b W k + d W j * y_vec W v k := by ring
  norm_num[h3▸(h1),ite_and]

lemma det_rank_2_zero_fin4 (x b_vec d_vec y : Fin 4 → ℂ) (j0 j1 j2 : Fin 4) :
  let M := fun j k => x j * b_vec k + d_vec j * y k;
  M j0 j0 * M j1 j1 * M j2 j2 + M j0 j1 * M j1 j2 * M j2 j0 + M j0 j2 * M j1 j0 * M j2 j1
  - M j0 j2 * M j1 j1 * M j2 j0 - M j0 j1 * M j1 j0 * M j2 j2 - M j0 j0 * M j1 j2 * M j2 j1 = 0 := by
  intros M
  ring

lemma det_eval (v : Fin 4 → ℂ) (j0 j1 j2 : Fin 4)
  (hj01 : j0 ≠ j1) (hj02 : j0 ≠ j2) (hj12 : j1 ≠ j2) :
  let M := fun j k => if j = k then v j else (0 : ℂ);
  M j0 j0 * M j1 j1 * M j2 j2 + M j0 j1 * M j1 j2 * M j2 j0 + M j0 j2 * M j1 j0 * M j2 j1
  - M j0 j2 * M j1 j1 * M j2 j0 - M j0 j1 * M j1 j0 * M j2 j2 - M j0 j0 * M j1 j2 * M j2 j1 =
  v j0 * v j1 * v j2 := by
  simp_all[]

lemma v_prod_zero (W : WeightsN 4 4 ℂ) (hW : EqSystemN 4 4 W) (v : Fin 4 → ℂ)
  (hv : ∑ i, v i * e W i = 0) (j0 j1 j2 : Fin 4)
  (hj01 : j0 ≠ j1) (hj02 : j0 ≠ j2) (hj12 : j1 ≠ j2) :
  v j0 * v j1 * v j2 = 0 := by
  have h_eq : ∀ j k, (if j = k then v j else (0 : ℂ)) = x_vec W v j * b W k + d W j * y_vec W v k := by
    intros j k
    have h_sum := sum_i_eq W hW v hv j k
    gcongr with S
  have h_det1 := det_rank_2_zero_fin4 (x_vec W v) (b W) (d W) (y_vec W v) j0 j1 j2
  have h_det2 := det_eval v j0 j1 j2 hj01 hj02 hj12
  rwa[←h_det2,funext₂ h_eq]

lemma contradiction_from_v (W : WeightsN 4 4 ℂ) (hW : EqSystemN 4 4 W) : False := by
  have hex := exists_v (e W)
  rcases hex with ⟨v, hv, hcases⟩
  have h_prod := v_prod_zero W hW v hv
  rcases hcases with h | h | h | h
  · have hz := h_prod 0 1 2 (by decide) (by decide) (by decide)
    rcases h with ⟨h0, h1, h2⟩
    rw [h0, h1, h2] at hz
    norm_num at hz
  · have hz := h_prod 0 1 3 (by decide) (by decide) (by decide)
    rcases h with ⟨h0, h1, h3⟩
    rw [h0, h1, h3] at hz
    norm_num at hz
  · have hz := h_prod 0 2 3 (by decide) (by decide) (by decide)
    rcases h with ⟨h0, h2, h3⟩
    rw [h0, h2, h3] at hz
    norm_num at hz
  · have hz := h_prod 1 2 3 (by decide) (by decide) (by decide)
    rcases h with ⟨h1, h2, h3⟩
    rw [h1, h2, h3] at hz
    norm_num at hz

/-- For $N = 4$ and $D = 4$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem4_no_solution_d4 :
    answer(True) ↔
      ¬ ∃ W : WeightsN 4 4 ℂ, EqSystemN 4 4 W := by
  simp only [true_iff]
  intro ⟨W, hW⟩
  exact contradiction_from_v W hW

/-- For $N = 4$ and all $D \geq 4$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem4_no_solution_ge4 :
    answer(sorry) ↔
      ∀ D : Nat, D ≥ 4 →
        ¬ ∃ W : WeightsN 4 D ℂ, EqSystemN 4 D W := by
  sorry

/-- For $N = 6$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem6_no_solution_d3 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 6 3 ℂ, EqSystemN 6 3 W := by
  sorry

/-- For $N = 6$ and all $D \geq 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem6_no_solution_ge3 :
    answer(sorry) ↔
      ∀ D : Nat, D ≥ 3 →
        ¬ ∃ W : WeightsN 6 D ℂ, EqSystemN 6 D W := by
  sorry

/-- For $N = 8$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem8_no_solution_d3 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 8 3 ℂ, EqSystemN 8 3 W := by
  sorry

/-- For $N = 8$ and $D = 10$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem8_no_solution_d10 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 8 10 ℂ, EqSystemN 8 10 W := by
  sorry

/-- For $N = 10$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem10_no_solution_d3 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 10 3 ℂ, EqSystemN 10 3 W := by
  sorry

/-- For $N = 10$ and $D = 10$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem10_no_solution_d10 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 10 10 ℂ, EqSystemN 10 10 W := by
  sorry

/-- For $N = 12$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem12_no_solution_d3 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 12 3 ℂ, EqSystemN 12 3 W := by
  sorry

/-- For $N = 14$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem14_no_solution_d3 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 14 3 ℂ, EqSystemN 14 3 W := by
  sorry

/-- For $N = 16$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem16_no_solution_d3 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 16 3 ℂ, EqSystemN 16 3 W := by
  sorry

/-- For all even $N \geq 6$ and $D \geq 3$, does there exist no solution to the monochromatic
quantum graph equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem_no_solution_ge6_ge3 :
    answer(sorry) ↔
      ∀ N D : Nat, N ≥ 6 → Even N → D ≥ 3 →
        ¬ ∃ W : WeightsN N D ℂ, EqSystemN N D W := by
  sorry

/- ## Open conjectures over ℝ -/

/-- For $N = 4$ and $D = 4$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{R}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem4_no_solution_d4_real :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 4 4 ℝ, EqSystemN 4 4 W := by
  sorry

/-- For $N = 4$ and all $D \geq 4$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{R}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem4_no_solution_ge4_real :
    answer(sorry) ↔
      ∀ D : Nat, D ≥ 4 →
        ¬ ∃ W : WeightsN 4 D ℝ, EqSystemN 4 D W := by
  sorry

/-- For $N = 6$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{R}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem6_no_solution_d3_real :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 6 3 ℝ, EqSystemN 6 3 W := by
  sorry

/-- For $N = 6$ and all $D \geq 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{R}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem6_no_solution_ge3_real :
    answer(sorry) ↔
      ∀ D : Nat, D ≥ 3 →
        ¬ ∃ W : WeightsN 6 D ℝ, EqSystemN 6 D W := by
  sorry

/-- For $N = 8$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{R}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem8_no_solution_d3_real :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 8 3 ℝ, EqSystemN 8 3 W := by
  sorry

/-- For $N = 8$ and $D = 10$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{R}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem8_no_solution_d10_real :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 8 10 ℝ, EqSystemN 8 10 W := by
  sorry

/-- For $N = 10$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{R}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem10_no_solution_d3_real :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 10 3 ℝ, EqSystemN 10 3 W := by
  sorry

/-- For $N = 10$ and $D = 10$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{R}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem10_no_solution_d10_real :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 10 10 ℝ, EqSystemN 10 10 W := by
  sorry

/-- For all even $N \geq 6$ and $D \geq 3$, does there exist no solution to the monochromatic
quantum graph equation system over $\mathbb{R}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem_no_solution_ge6_ge3_real :
    answer(sorry) ↔
      ∀ N D : Nat, N ≥ 6 → Even N → D ≥ 3 →
        ¬ ∃ W : WeightsN N D ℝ, EqSystemN N D W := by
  sorry

/- ## Open conjectures over ℤ -/

/-- For $N = 4$ and $D = 4$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem4_no_solution_d4_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 4 4 ℤ, EqSystemN 4 4 W := by
  sorry

/-- For $N = 4$ and all $D \geq 4$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem4_no_solution_ge4_int :
    answer(sorry) ↔
      ∀ D : Nat, D ≥ 4 →
        ¬ ∃ W : WeightsN 4 D ℤ, EqSystemN 4 D W := by
  sorry

/-- For $N = 6$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem6_no_solution_d3_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 6 3 ℤ, EqSystemN 6 3 W := by
  sorry

/-- For $N = 6$ and all $D \geq 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem6_no_solution_ge3_int :
    answer(sorry) ↔
      ∀ D : Nat, D ≥ 3 →
        ¬ ∃ W : WeightsN 6 D ℤ, EqSystemN 6 D W := by
  sorry

/-- For $N = 8$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem8_no_solution_d3_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 8 3 ℤ, EqSystemN 8 3 W := by
  sorry

/-- For $N = 8$ and $D = 10$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem8_no_solution_d10_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 8 10 ℤ, EqSystemN 8 10 W := by
  sorry

/-- For $N = 10$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem10_no_solution_d3_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 10 3 ℤ, EqSystemN 10 3 W := by
  sorry

/-- For $N = 10$ and $D = 10$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem10_no_solution_d10_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 10 10 ℤ, EqSystemN 10 10 W := by
  sorry

/-- For all even $N \geq 6$ and $D \geq 3$, does there exist no solution to the monochromatic
quantum graph equation system over $\mathbb{Z}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem_no_solution_ge6_ge3_int :
    answer(sorry) ↔
      ∀ N D : Nat, N ≥ 6 → Even N → D ≥ 3 →
        ¬ ∃ W : WeightsN N D ℤ, EqSystemN N D W := by
  sorry

/- ## Open conjectures over {-1,0,1} ⊆ ℤ
   (implemented as ℤ-valued weights with a pointwise restriction) -/

/-- For $N = 4$ and $D = 4$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$ with weights in $\{-1, 0, 1\}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem4_no_solution_d4_trinary_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 4 4 ℤ,
          (∀ e, W e = (-1 : ℤ) ∨ W e = 0 ∨ W e = 1) ∧
            EqSystemN 4 4 W := by
  sorry

/-- For $N = 4$ and all $D \geq 4$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$ with weights in $\{-1, 0, 1\}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem4_no_solution_ge4_trinary_int :
    answer(sorry) ↔
      ∀ D : Nat, D ≥ 4 →
        ¬ ∃ W : WeightsN 4 D ℤ,
            (∀ e, W e = (-1 : ℤ) ∨ W e = 0 ∨ W e = 1) ∧
              EqSystemN 4 D W := by
  sorry

/-- For $N = 6$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$ with weights in $\{-1, 0, 1\}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem6_no_solution_d3_trinary_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 6 3 ℤ,
          (∀ e, W e = (-1 : ℤ) ∨ W e = 0 ∨ W e = 1) ∧
            EqSystemN 6 3 W := by
  sorry

/-- For $N = 6$ and all $D \geq 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$ with weights in $\{-1, 0, 1\}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem6_no_solution_ge3_trinary_int :
    answer(sorry) ↔
      ∀ D : Nat, D ≥ 3 →
        ¬ ∃ W : WeightsN 6 D ℤ,
            (∀ e, W e = (-1 : ℤ) ∨ W e = 0 ∨ W e = 1) ∧
              EqSystemN 6 D W := by
  sorry

/-- For $N = 8$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$ with weights in $\{-1, 0, 1\}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem8_no_solution_d3_trinary_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 8 3 ℤ,
          (∀ e, W e = (-1 : ℤ) ∨ W e = 0 ∨ W e = 1) ∧
            EqSystemN 8 3 W := by
  sorry

/-- For $N = 8$ and $D = 10$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$ with weights in $\{-1, 0, 1\}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem8_no_solution_d10_trinary_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 8 10 ℤ,
          (∀ e, W e = (-1 : ℤ) ∨ W e = 0 ∨ W e = 1) ∧
            EqSystemN 8 10 W := by
  sorry

/-- For $N = 10$ and $D = 3$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$ with weights in $\{-1, 0, 1\}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem10_no_solution_d3_trinary_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 10 3 ℤ,
          (∀ e, W e = (-1 : ℤ) ∨ W e = 0 ∨ W e = 1) ∧
            EqSystemN 10 3 W := by
  sorry

/-- For $N = 10$ and $D = 10$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{Z}$ with weights in $\{-1, 0, 1\}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem10_no_solution_d10_trinary_int :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 10 10 ℤ,
          (∀ e, W e = (-1 : ℤ) ∨ W e = 0 ∨ W e = 1) ∧
            EqSystemN 10 10 W := by
  sorry

/-- For all even $N \geq 6$ and $D \geq 3$, does there exist no solution to the monochromatic
quantum graph equation system over $\mathbb{Z}$ with weights in $\{-1, 0, 1\}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem_no_solution_ge6_ge3_trinary_int :
    answer(sorry) ↔
      ∀ N D : Nat, N ≥ 6 → Even N → D ≥ 3 →
        ¬ ∃ W : WeightsN N D ℤ,
            (∀ e, W e = (-1 : ℤ) ∨ W e = 0 ∨ W e = 1) ∧
              EqSystemN N D W := by
  sorry

end MonochromaticQuantumGraph
