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

/-- For $N = 4$ and $D = 4$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research open, AMS 5 14 81]
theorem eqSystem4_no_solution_d4 :
    answer(sorry) ↔
      ¬ ∃ W : WeightsN 4 4 ℂ, EqSystemN 4 4 W := by
  sorry

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



def valid_d (B : Fin 9 → Fin 10 → ℂ) (c_star : Fin 10) (v : Fin 9) (dv : Fin 10) : Prop :=
  dv ≠ c_star ∧ (B v ≠ 0 → B v dv ≠ 0)

lemma exists_c_star (B : Fin 9 → Fin 10 → ℂ) :
  ∃ c_star : Fin 10, ∀ v, ∃ dv, valid_d B c_star v dv := by
  refine show∃ _,∀ R, ∃a, a ∈{s |_} from (by_contra fun and=>? _)
  simp_all[imp_iff_not_or,exists_or, and_or_left]
  choose R L using and
  use (by decide ∘ Fintype.card_le_of_injective R) fun and R M=>symm (by_contra ((L _).1.resolve_left.comp ( fun and U=>and (U _).symm) · (funext (by cases M▸(L _).2 · with cases(L R).2 (by valid) with simp_all))))

lemma exists_sequence_or_case1 (B : Fin 9 → Fin 10 → ℂ) (c_star : Fin 10)
  (h_valid : ∀ v, ∃ dv, valid_d B c_star v dv) :
  (∃ d : Fin 9 → Fin 10, (∀ v, valid_d B c_star v (d v)) ∧ ¬ ∀ v, d v = d 0) ∨
  (∃ k, k ≠ c_star ∧ ∀ v i, i ≠ c_star → i ≠ k → B v i = 0) := by
  choose R L using h_valid
  delta valid_d at *
  use or_iff_not_imp_left.2 fun and=>⟨ _,(L 0).1,fun a s _ _=>by_contra fun and' =>and ⟨ (if. = a then(s)else R (by valid)),?_⟩⟩
  use (by cases eq_or_ne · a with grind),fun H=>and ⟨ (if. = a then R a else s), (by cases eq_or_ne · a with grind),by grind ∘ fun and=>And.intro (and a) (and (a + 1))⟩

noncomputable def make_y_from_d (B : Fin 9 → Fin 10 → ℂ) (c_star : Fin 10) (d : Fin 9 → Fin 10) (v : Fin 9) (i : Fin 10) : ℂ :=
  if B v = 0 then
    if i = c_star then 1 else 0
  else
    if i = c_star then B v (d v) else if i = d v then -B v c_star else 0

lemma make_y_from_d_orth (B : Fin 9 → Fin 10 → ℂ) (c_star : Fin 10) (d : Fin 9 → Fin 10) (v : Fin 9)
  (hd_not_c : d v ≠ c_star) :
  ∑ i, B v i * make_y_from_d B c_star d v i = 0 := by
  unfold make_y_from_d
  split_ifs with hB
  · apply Finset.sum_eq_zero
    intro i _
    have hBi : B v i = 0 := by
      have : B v = 0 := hB
      exact congr_fun this i
    rw [hBi, MulZeroClass.zero_mul]
  · have h_sum : (∑ i : Fin 10, B v i * if i = c_star then B v (d v) else if i = d v then -B v c_star else 0) =
      B v c_star * B v (d v) + B v (d v) * (-B v c_star) := by
      norm_num[*,Finset.sum_ite, Finset.filter_eq']
    rw [h_sum]
    ring

lemma make_y_from_d_nonzero (B : Fin 9 → Fin 10 → ℂ) (c_star : Fin 10) (d : Fin 9 → Fin 10)
  (hd_not_c : ∀ v, d v ≠ c_star)
  (hd_not_const : ¬ ∀ v, d v = d 0)
  (hB_d : ∀ v, B v ≠ 0 → B v (d v) ≠ 0) :
  (∑ c, ∏ v, make_y_from_d B c_star d v c) ≠ 0 := by
  show∑y,∏ M,ite _ _ _≠00
  rw[not_forall, Fintype.sum_eq_single c_star]at*
  · use Finset.prod_ne_zero_iff.2 fun and y=> if a:_ then (by norm_num[a])else (if_neg a▸if_pos rfl▸hB_d and a)
  · use hd_not_const.elim fun and R L i=> Finset.prod_eq_zero_iff.2 (if j:L = d and then⟨0,by norm_num[*, Ne.symm R]⟩else⟨and,by norm_num[*]⟩)

lemma exists_orth_case1 (B : Fin 9 → Fin 10 → ℂ) (c1 c2 : Fin 10) (hc : c1 ≠ c2)
  (hB : ∀ v i, i ≠ c1 → i ≠ c2 → B v i = 0) :
  ∃ y : Fin 9 → Fin 10 → ℂ, (∀ v, ∑ d, B v d * y v d = 0) ∧ (∑ c, ∏ v, y v c) ≠ 0 := by
  let y : Fin 9 → Fin 10 → ℂ := fun _ i => if i = c1 ∨ i = c2 then 0 else 1
  use y
  constructor
  · intro v
    apply Finset.sum_eq_zero
    intro d _
    by_cases hd : d = c1 ∨ d = c2
    · rcases hd with h1 | h2
      · subst h1
        have : y v d = 0 := if_pos (Or.inl rfl)
        rw [this, mul_zero]
      · subst h2
        have : y v d = 0 := if_pos (Or.inr rfl)
        rw [this, mul_zero]
    · push_neg at hd
      have : B v d = 0 := hB v d hd.1 hd.2
      rw [this, MulZeroClass.zero_mul]
  · have h_sum : (∑ c : Fin 10, ∏ v : Fin 9, y v c) = 8 := by
      norm_num[*,y,ite_or, Finset.sum_ite, Finset.filter_ne']
      norm_num[hc.symm]
    rw [h_sum]
    exact by norm_num

lemma slice_rank_obstruction (a : Fin 9 → Fin 10 → ℂ) :
    ∃ X : Fin 9 → Fin 10 → ℂ, (∀ v, ∑ c, a v c * X v c = 0) ∧ (∑ c, ∏ v, X v c ≠ 0) := by
  have ⟨c_star, hc⟩ := exists_c_star a
  rcases exists_sequence_or_case1 a c_star hc with ⟨d, hd_valid, hd_not_const⟩ | ⟨k, hk_neq, hB_case1⟩
  · use make_y_from_d a c_star d
    constructor
    · intro v
      exact make_y_from_d_orth a c_star d v (hd_valid v).1
    · apply make_y_from_d_nonzero a c_star d
      · intro v; exact (hd_valid v).1
      · exact hd_not_const
      · intro v; exact (hd_valid v).2
  · exact exists_orth_case1 a c_star k hk_neq.symm hB_case1

noncomputable def L_form (W : WeightsN 10 10 ℂ) (v : V 10) (y : Fin 10 → ℂ) : ℂ :=
  ∑ c : Fin 10, ∑ d : Fin 10, W (mkEdge 0 v c d) * 1 * y d

lemma pmSumN_10_eq (W : WeightsN 10 10 ℂ) (ι : V 10 → Fin 10) :
    pmSumN 10 10 W ι = ([1, 2, 3, 4, 5, 6, 7, 8, 9].map (fun u : V 10 => W (mkEdge 0 u (ι 0) (ι u)) * pmSumListAux W ι 8 ([1, 2, 3, 4, 5, 6, 7, 8, 9].erase u))).sum := by
  rfl

lemma sum_factor_zero (u : V 10) (hu : u ≠ 0) (F : Fin 10 → Fin 10 → ℂ) (G : (V 10 → Fin 10) → ℂ)
  (hG : ∀ ι₁ ι₂, (∀ v, v ≠ 0 → v ≠ u → ι₁ v = ι₂ v) → G ι₁ = G ι₂)
  (hF : (∑ c : Fin 10, ∑ d : Fin 10, F c d) = 0) :
  (∑ ι : V 10 → Fin 10, F (ι 0) (ι u) * G ι) = 0 := by
  have h_rw : (∑ ι : V 10 → Fin 10, F (ι 0) (ι u) * G ι) =
    ∑ c : Fin 10, ∑ d : Fin 10, ∑ ι ∈ Finset.filter (fun i => i 0 = c ∧ i u = d) Finset.univ, F (ι 0) (ι u) * G ι := by
    have h1 : (∑ ι : V 10 → Fin 10, F (ι 0) (ι u) * G ι) =
      ∑ c : Fin 10, ∑ ι ∈ Finset.filter (fun i => i 0 = c) Finset.univ, F (ι 0) (ι u) * G ι := by
      exact (Finset.sum_fiberwise Finset.univ (fun i => i 0) (fun i => F (i 0) (i u) * G i)).symm
    rw [h1]
    apply Finset.sum_congr rfl
    intro c _
    have h2 : (∑ ι ∈ Finset.filter (fun i => i 0 = c) Finset.univ, F (ι 0) (ι u) * G ι) =
      ∑ d : Fin 10, ∑ ι ∈ Finset.filter (fun i => i u = d) (Finset.filter (fun i => i 0 = c) Finset.univ), F (ι 0) (ι u) * G ι := by
      exact (Finset.sum_fiberwise (Finset.filter (fun i => i 0 = c) Finset.univ) (fun i => i u) (fun i => F (i 0) (i u) * G i)).symm
    rw [h2]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr
    · ext ι
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · intro _ _
      rfl
  have h_rw2 : (∑ c : Fin 10, ∑ d : Fin 10, ∑ ι ∈ Finset.filter (fun i => i 0 = c ∧ i u = d) Finset.univ, F (ι 0) (ι u) * G ι) =
    ∑ c : Fin 10, ∑ d : Fin 10, F c d * ∑ ι ∈ Finset.filter (fun i => i 0 = c ∧ i u = d) Finset.univ, G ι := by
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ι h_ι
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h_ι
    rw [h_ι.1, h_ι.2]
  have h_G_indep : ∀ c d, ∑ ι ∈ Finset.filter (fun i => i 0 = c ∧ i u = d) Finset.univ, G ι =
    ∑ ι ∈ Finset.filter (fun i => i 0 = 0 ∧ i u = 0) Finset.univ, G ι := by
    intro c d
    let e : (V 10 → Fin 10) → (V 10 → Fin 10) := fun ι v =>
      if v = 0 then 0 else if v = u then 0 else ι v
    let e_inv : (V 10 → Fin 10) → (V 10 → Fin 10) := fun ι v =>
      if v = 0 then c else if v = u then d else ι v
    apply Finset.sum_bij (fun ι _ => e ι)
    · intro ι _
      simp [e]
    · intro ι1 h_ι1 ι2 h_ι2 h_eq
      ext v
      by_cases hv0 : v = 0
      · subst hv0
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h_ι1 h_ι2
        rw [h_ι1.1, h_ι2.1]
      · by_cases hvu : v = u
        · subst hvu
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h_ι1 h_ι2
          rw [h_ι1.2, h_ι2.2]
        · have h1 : e ι1 v = ι1 v := by simp [e, hv0, hvu]
          have h2 : e ι2 v = ι2 v := by simp [e, hv0, hvu]
          have h_eq_v : e ι1 v = e ι2 v := congr_fun h_eq v
          have h_final : ι1 v = ι2 v := by
            calc
              ι1 v = e ι1 v := h1.symm
              _ = e ι2 v := h_eq_v
              _ = ι2 v := h2
          rw [h_final]
    · intro ι' h_ι'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h_ι'
      use e_inv ι'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨rfl, ?_⟩, ?_⟩
      · dsimp [e_inv]
        rw [if_neg hu, if_pos rfl]
      · ext v
        have H : e (e_inv ι') v = ι' v := by
          by_cases hv0 : v = 0
          · subst hv0
            have h1 : e (e_inv ι') 0 = 0 := rfl
            have h2 : ι' 0 = 0 := h_ι'.1
            rw [h1, h2]
          · by_cases hvu : v = u
            · have h1 : e (e_inv ι') v = 0 := by dsimp [e]; rw [if_neg hv0, if_pos hvu]
              have h2 : ι' v = 0 := by rw [hvu, h_ι'.2]
              rw [h1, h2]
            · dsimp [e, e_inv]
              rw [if_neg hv0, if_neg hvu, if_neg hv0, if_neg hvu]
        rw [H]
    · intro ι h_ι
      exact hG ι (e ι) (fun v hv_0 hv_u => by simp [e, hv_0, hv_u])
  have h_rw3 : (∑ c : Fin 10, ∑ d : Fin 10, F c d * ∑ ι ∈ Finset.filter (fun i => i 0 = c ∧ i u = d) Finset.univ, G ι) =
    (∑ c : Fin 10, ∑ d : Fin 10, F c d) * (∑ ι ∈ Finset.filter (fun i => i 0 = 0 ∧ i u = 0) Finset.univ, G ι) := by
    have h1 : (∑ c : Fin 10, ∑ d : Fin 10, F c d * ∑ ι ∈ Finset.filter (fun i => i 0 = c ∧ i u = d) Finset.univ, G ι) =
      ∑ c : Fin 10, ∑ d : Fin 10, F c d * (∑ ι ∈ Finset.filter (fun i => i 0 = 0 ∧ i u = 0) Finset.univ, G ι) := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      rw [h_G_indep c d]
    rw [h1]
    have h2 : (∑ c : Fin 10, ∑ d : Fin 10, F c d * (∑ ι ∈ Finset.filter (fun i => i 0 = 0 ∧ i u = 0) Finset.univ, G ι)) =
      ∑ c : Fin 10, (∑ d : Fin 10, F c d) * (∑ ι ∈ Finset.filter (fun i => i 0 = 0 ∧ i u = 0) Finset.univ, G ι) := by
      apply Finset.sum_congr rfl
      intro c _
      exact Finset.sum_mul _ _ _ |>.symm
    rw [h2]
    exact Finset.sum_mul _ _ _ |>.symm
  rw [h_rw, h_rw2, h_rw3, hF, MulZeroClass.zero_mul]

lemma pmSumListAux_indep_gen (W : WeightsN 10 10 ℂ) (ι₁ ι₂ : V 10 → Fin 10) (n : Nat) :
  ∀ L : List (V 10), (∀ v ∈ L, ι₁ v = ι₂ v) → pmSumListAux W ι₁ n L = pmSumListAux W ι₂ n L := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro L h_eq
    cases n with
    | zero => rfl
    | succ n1 =>
      cases n1 with
      | zero => rfl
      | succ n2 =>
        cases L with
        | nil => rfl
        | cons head tail =>
          cases tail with
          | nil => rfl
          | cons th tt =>
            change ((th :: tt).map (fun u => W (mkEdge head u (ι₁ head) (ι₁ u)) * pmSumListAux W ι₁ n2 ((th :: tt).erase u))).sum = ((th :: tt).map (fun u => W (mkEdge head u (ι₂ head) (ι₂ u)) * pmSumListAux W ι₂ n2 ((th :: tt).erase u))).sum
            apply congrArg
            apply List.map_congr_left
            intro x hx
            have h_head : ι₁ head = ι₂ head := h_eq head (List.Mem.head _)
            have h_x : ι₁ x = ι₂ x := h_eq x (List.Mem.tail _ hx)
            rw [h_head, h_x]
            have h_rec : pmSumListAux W ι₁ n2 ((th :: tt).erase x) = pmSumListAux W ι₂ n2 ((th :: tt).erase x) := by
              apply ih n2 (by omega)
              intro y hy
              apply h_eq y
              apply List.Mem.tail
              exact List.mem_of_mem_erase hy
            rw [h_rec]

lemma pmSumListAux_indep (W : WeightsN 10 10 ℂ) (u : V 10) (ι₁ ι₂ : V 10 → Fin 10)
  (h_eq : ∀ v, v ≠ 0 → v ≠ u → ι₁ v = ι₂ v) :
  pmSumListAux W ι₁ 8 ([1, 2, 3, 4, 5, 6, 7, 8, 9].erase u) = pmSumListAux W ι₂ 8 ([1, 2, 3, 4, 5, 6, 7, 8, 9].erase u) := by
  apply pmSumListAux_indep_gen
  intro v hv
  apply h_eq v
  · rintro rfl
    have h_not : (0 : V 10) ∉ [ (1 : V 10), 2, 3, 4, 5, 6, 7, 8, 9 ] := by decide
    have h_in : (0 : V 10) ∈ [ (1 : V 10), 2, 3, 4, 5, 6, 7, 8, 9 ] := List.mem_of_mem_erase hv
    contradiction
  · rintro rfl
    have h_not : v ∉ ([ (1 : V 10), 2, 3, 4, 5, 6, 7, 8, 9 ].erase v) := by clear hv h_eq; revert v; decide
    contradiction

lemma list_sum_mul_eq (l : List (V 10)) (f : V 10 → ℂ) (c : ℂ) :
  (l.map f).sum * c = (l.map (fun u => f u * c)).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp [add_mul, ih]

lemma sum_list_sum_comm (l : List (V 10)) (f : V 10 → (V 10 → Fin 10) → ℂ) :
  (∑ ι : V 10 → Fin 10, (l.map (fun u => f u ι)).sum) = (l.map (fun u => ∑ ι : V 10 → Fin 10, f u ι)).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp [Finset.sum_add_distrib, ih]

lemma eval_poly_zero_u (W : WeightsN 10 10 ℂ) (X : V 10 → Fin 10 → ℂ)
  (h_X0 : ∀ c, X 0 c = 1)
  (h_ker : ∀ (u : V 10) (hu : u ≠ 0), L_form W u (X u) = 0)
  (u : V 10) (hu_list : u ∈ [ (1:V 10), 2, 3, 4, 5, 6, 7, 8, 9 ]) :
  (∑ ι : V 10 → Fin 10, W (mkEdge 0 u (ι 0) (ι u)) * pmSumListAux W ι 8 ([1, 2, 3, 4, 5, 6, 7, 8, 9].erase u) * ∏ v : V 10, X v (ι v)) = 0 := by
  have hu : u ≠ 0 := by
    rintro rfl
    revert hu_list
    decide
  let F := fun c d => W (mkEdge 0 u c d) * X 0 c * X u d
  let G := fun ι => pmSumListAux W ι 8 ([1, 2, 3, 4, 5, 6, 7, 8, 9].erase u) * ∏ v ∈ (Finset.univ.erase 0).erase u, X v (ι v)
  have h_rewrite : ∀ ι, W (mkEdge 0 u (ι 0) (ι u)) * pmSumListAux W ι 8 ([1, 2, 3, 4, 5, 6, 7, 8, 9].erase u) * ∏ v : V 10, X v (ι v) = F (ι 0) (ι u) * G ι := by
    intro ι
    dsimp [F, G]
    have h1 : ∏ v : V 10, X v (ι v) = X 0 (ι 0) * ∏ v ∈ Finset.univ.erase 0, X v (ι v) := by
      exact Finset.mul_prod_erase Finset.univ (fun v => X v (ι v)) (Finset.mem_univ 0)
    have h2 : ∏ v ∈ Finset.univ.erase 0, X v (ι v) = X u (ι u) * ∏ v ∈ (Finset.univ.erase 0).erase u, X v (ι v) := by
      have h3 : X u (ι u) * ∏ v ∈ (Finset.univ.erase 0).erase u, X v (ι v) = ∏ v ∈ Finset.univ.erase 0, X v (ι v) := by
        exact Finset.mul_prod_erase (Finset.univ.erase 0) (fun v => X v (ι v)) (by simp [hu])
      exact h3.symm
    rw [h1, h2]
    ring
  have h_sum_rw : (∑ ι : V 10 → Fin 10, W (mkEdge 0 u (ι 0) (ι u)) * pmSumListAux W ι 8 ([1, 2, 3, 4, 5, 6, 7, 8, 9].erase u) * ∏ v : V 10, X v (ι v)) =
    ∑ ι : V 10 → Fin 10, F (ι 0) (ι u) * G ι := by
    apply Finset.sum_congr rfl
    intro ι _
    exact h_rewrite ι
  rw [h_sum_rw]
  apply sum_factor_zero u hu F G
  · intro ι₁ ι₂ h_eq
    dsimp [G]
    have h_pm : pmSumListAux W ι₁ 8 ([1, 2, 3, 4, 5, 6, 7, 8, 9].erase u) = pmSumListAux W ι₂ 8 ([1, 2, 3, 4, 5, 6, 7, 8, 9].erase u) := by
      apply pmSumListAux_indep W u ι₁ ι₂ h_eq
    have h_prod2 : ∏ v ∈ (Finset.univ.erase 0).erase u, X v (ι₁ v) = ∏ v ∈ (Finset.univ.erase 0).erase u, X v (ι₂ v) := by
      apply Finset.prod_congr rfl
      intro v hv
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hv
      rw [h_eq v hv.2 hv.1]
    rw [h_pm, h_prod2]
  · dsimp [F]
    have h_F : (∑ c : Fin 10, ∑ d : Fin 10, W (mkEdge 0 u c d) * X 0 c * X u d) = L_form W u (X u) := by
      unfold L_form
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      rw [h_X0 c]
    rw [h_F]
    exact h_ker u hu

lemma eval_poly_zero_if_kernel (W : WeightsN 10 10 ℂ) (X : V 10 → Fin 10 → ℂ)
  (h_X0 : ∀ c, X 0 c = 1)
  (h_ker : ∀ (u : V 10) (hu : u ≠ 0), L_form W u (X u) = 0) :
  (∑ ι : V 10 → Fin 10, pmSumN 10 10 W ι * ∏ v : V 10, X v (ι v)) = 0 := by
  have h_eq1 : (∑ ι : V 10 → Fin 10, pmSumN 10 10 W ι * ∏ v : V 10, X v (ι v)) =
    ∑ ι : V 10 → Fin 10, ([1, 2, 3, 4, 5, 6, 7, 8, 9].map (fun u : V 10 => W (mkEdge 0 u (ι 0) (ι u)) * pmSumListAux W ι 8 ([1, 2, 3, 4, 5, 6, 7, 8, 9].erase u) * ∏ v : V 10, X v (ι v))).sum := by
    apply Finset.sum_congr rfl
    intro ι _
    rw [pmSumN_10_eq W ι]
    have h_mul_sum : ([1, 2, 3, 4, 5, 6, 7, 8, 9].map (fun u : V 10 => W (mkEdge 0 u (ι 0) (ι u)) * pmSumListAux W ι 8 ([1, 2, 3, 4, 5, 6, 7, 8, 9].erase u))).sum * ∏ v : V 10, X v (ι v) =
      ([1, 2, 3, 4, 5, 6, 7, 8, 9].map (fun u : V 10 => W (mkEdge 0 u (ι 0) (ι u)) * pmSumListAux W ι 8 ([1, 2, 3, 4, 5, 6, 7, 8, 9].erase u) * ∏ v : V 10, X v (ι v))).sum := by
      exact list_sum_mul_eq [1, 2, 3, 4, 5, 6, 7, 8, 9] _ _
    rw [h_mul_sum]
  rw [h_eq1]
  have h_comm : (∑ ι : V 10 → Fin 10, ([1, 2, 3, 4, 5, 6, 7, 8, 9].map (fun u : V 10 => W (mkEdge 0 u (ι 0) (ι u)) * pmSumListAux W ι 8 ([1, 2, 3, 4, 5, 6, 7, 8, 9].erase u) * ∏ v : V 10, X v (ι v))).sum) =
    ([1, 2, 3, 4, 5, 6, 7, 8, 9].map (fun u : V 10 => ∑ ι : V 10 → Fin 10, W (mkEdge 0 u (ι 0) (ι u)) * pmSumListAux W ι 8 ([1, 2, 3, 4, 5, 6, 7, 8, 9].erase u) * ∏ v : V 10, X v (ι v))).sum := by
    exact sum_list_sum_comm [1, 2, 3, 4, 5, 6, 7, 8, 9] _
  rw [h_comm]
  have h_map_zero : ([1, 2, 3, 4, 5, 6, 7, 8, 9].map (fun u : V 10 => ∑ ι : V 10 → Fin 10, W (mkEdge 0 u (ι 0) (ι u)) * pmSumListAux W ι 8 ([1, 2, 3, 4, 5, 6, 7, 8, 9].erase u) * ∏ v : V 10, X v (ι v))) =
    ([1, 2, 3, 4, 5, 6, 7, 8, 9].map (fun _ : V 10 => (0 : ℂ))) := by
    apply List.map_congr_left
    intro u hu
    exact eval_poly_zero_u W X h_X0 h_ker u hu
  rw [h_map_zero]
  simp

lemma eval_poly_eq_ghz (W : WeightsN 10 10 ℂ) (hW : EqSystemN 10 10 W) (X : V 10 → Fin 10 → ℂ) :
  (∑ ι : V 10 → Fin 10, pmSumN 10 10 W ι * ∏ v : V 10, X v (ι v)) = ∑ c : Fin 10, ∏ v : V 10, X v c := by
  have h_sum_eq : (∑ ι : V 10 → Fin 10, pmSumN 10 10 W ι * ∏ v : V 10, X v (ι v)) =
    ∑ ι : V 10 → Fin 10, (if allEqual ι then (1 : ℂ) else 0) * ∏ v : V 10, X v (ι v) := by
    apply Finset.sum_congr rfl
    intro ι _
    rw [hW ι]
  rw [h_sum_eq]
  delta allEqual V EqSystemN pmSumN at*
  simp_all[allEqualList,vertices]
  exact ( Finset.sum_subset (Finset.subset_univ (.image (fun a s=>a) ⊤)) fun and a s=>if_neg (s.comp (by simp_all[←List.ofFn_inj]))).symm.trans (.trans ( Finset.sum_image fun and _ _ _=>(congrFun · 0)) (congr_arg _ (by norm_num)))

lemma ghz_nz_of_tail (X_tail : Fin 9 → Fin 10 → ℂ) (h_nz : (∑ c, ∏ v, X_tail v c) ≠ 0)
  (X : V 10 → Fin 10 → ℂ) (hX0 : ∀ c, X 0 c = 1)
  (hX_tail : ∀ v : Fin 9, X v.succ = X_tail v) :
  (∑ c : Fin 10, ∏ v : V 10, X v c) ≠ 0 := by
  exact (funext fun and=> Fin.prod_univ_succ (X · _)).symm▸by·norm_num[ *]

lemma no_witness_10_10_with_X (W : WeightsN 10 10 ℂ) (hW : EqSystemN 10 10 W)
  (a : Fin 9 → Fin 10 → ℂ)
  (ha : ∀ v d, a v d = ∑ c, W (mkEdge 0 v.succ c d))
  (X_tail : Fin 9 → Fin 10 → ℂ)
  (h_ker : ∀ v, ∑ c, a v c * X_tail v c = 0)
  (h_nz : (∑ c, ∏ v, X_tail v c) ≠ 0) : False := by
  let X : V 10 → Fin 10 → ℂ := fun v =>
    match v with
    | ⟨0, _⟩ => (fun _ => 1)
    | ⟨v_val + 1, h_lt⟩ => X_tail ⟨v_val, Nat.lt_of_succ_lt_succ h_lt⟩
  have h_X0 : ∀ c, X 0 c = 1 := by
    intro c
    rfl
  have h_X_tail : ∀ v : Fin 9, X v.succ = X_tail v := by
    intro v
    cases v with
    | mk v_val h_lt =>
      rfl
  have h_ker_X : ∀ (u : V 10) (hu : u ≠ 0), L_form W u (X u) = 0 := by
    intro u hu
    cases u with
    | mk u_val u_lt =>
      cases u_val with
      | zero =>
        contradiction
      | succ v_val =>
        have h_v_lt : v_val < 9 := Nat.lt_of_succ_lt_succ u_lt
        let v : Fin 9 := ⟨v_val, h_v_lt⟩
        have h_X_eq : X v.succ = X_tail v := rfl
        change L_form W v.succ (X v.succ) = 0
        rw [h_X_eq]
        unfold L_form
        have hk := h_ker v
        have h_rw : (∑ c : Fin 10, a v c * X_tail v c) =
          ∑ c : Fin 10, ∑ d : Fin 10, W (mkEdge 0 v.succ c d) * 1 * X_tail v d := by
          have h1 : (∑ c : Fin 10, a v c * X_tail v c) =
                    ∑ c : Fin 10, (∑ c_1 : Fin 10, W (mkEdge 0 v.succ c_1 c)) * X_tail v c := by
            apply Finset.sum_congr rfl
            intro c _
            rw [ha v c]
          rw [h1]
          have h2 : (∑ c : Fin 10, (∑ c_1 : Fin 10, W (mkEdge 0 v.succ c_1 c)) * X_tail v c) =
                    ∑ c : Fin 10, ∑ c_1 : Fin 10, W (mkEdge 0 v.succ c_1 c) * X_tail v c := by
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.sum_mul]
          rw [h2, Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro c_1 _
          apply Finset.sum_congr rfl
          intro c _
          ring
        rw [← h_rw]
        exact hk
  have h_eval_ghz := eval_poly_eq_ghz W hW X
  have h_ghz_nz := ghz_nz_of_tail X_tail h_nz X h_X0 h_X_tail
  apply h_ghz_nz
  rw [← h_eval_ghz]
  exact eval_poly_zero_if_kernel W X h_X0 h_ker_X

lemma no_witness_10_10 : ¬∃ W : WeightsN 10 10 ℂ, EqSystemN 10 10 W := by
  intro ⟨W, hW⟩
  let a := fun (v : Fin 9) (d : Fin 10) => ∑ c : Fin 10, W (mkEdge 0 v.succ c d)
  have ha : ∀ v d, a v d = ∑ c, W (mkEdge 0 v.succ c d) := by
    intro v d
    rfl
  have ⟨X_tail, h_ker, h_nz⟩ := slice_rank_obstruction a
  exact no_witness_10_10_with_X W hW a ha X_tail h_ker h_nz

/-- For $N = 10$ and $D = 10$, does there exist no solution to the monochromatic quantum graph
equation system over $\mathbb{C}$? -/
@[category research solved, AMS 5 14 81]
theorem eqSystem10_no_solution_d10 :
    answer(True) ↔
      ¬ ∃ W : WeightsN 10 10 ℂ, EqSystemN 10 10 W := by
  constructor
  · intro _
    exact no_witness_10_10
  · intro _
    trivial

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
