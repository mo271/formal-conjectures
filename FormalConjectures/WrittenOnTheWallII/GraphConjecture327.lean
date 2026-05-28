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

/-!
# Written on the Wall II - Conjecture 327

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace WrittenOnTheWallII.GraphConjecture327

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]


def G_counter_adj_bool (u v : Fin 12) : Bool :=
  let u_val := u.val
  let v_val := v.val
  let min_val := min u_val v_val
  let max_val := max u_val v_val
  if min_val = 0 then
    max_val = 1 ∨ max_val = 2 ∨ max_val = 3 ∨ max_val = 4 ∨ max_val = 5 ∨ max_val = 6
  else if min_val = 1 then
    max_val = 7 ∨ max_val = 8 ∨ max_val = 9 ∨ max_val = 10 ∨ max_val = 11
  else if min_val = 2 then
    max_val = 10
  else if min_val = 3 then
    max_val = 10
  else if min_val = 4 then
    max_val = 7
  else if min_val = 5 then
    max_val = 7
  else if min_val = 6 then
    max_val = 10 ∨ max_val = 11
  else
    false

def G_counter : SimpleGraph (Fin 12) where
  Adj u v := G_counter_adj_bool u v = true
  symm u v h := (by decide : ∀ x y, G_counter_adj_bool x y = true → G_counter_adj_bool y x = true) u v h
  loopless u := (by decide : ∀ x, G_counter_adj_bool x x ≠ true) u

instance (u v : Fin 12) : Decidable (G_counter.Adj u v) :=
  instDecidableEqBool (G_counter_adj_bool u v) true

def path_from_zero : (w : Fin 12) → G_counter.Walk 0 w
  | ⟨0, _⟩ => Walk.nil
  | ⟨1, _⟩ => @Walk.cons _ G_counter 0 1 1 (by decide : G_counter.Adj 0 1) Walk.nil
  | ⟨2, _⟩ => @Walk.cons _ G_counter 0 2 2 (by decide : G_counter.Adj 0 2) Walk.nil
  | ⟨3, _⟩ => @Walk.cons _ G_counter 0 3 3 (by decide : G_counter.Adj 0 3) Walk.nil
  | ⟨4, _⟩ => @Walk.cons _ G_counter 0 4 4 (by decide : G_counter.Adj 0 4) Walk.nil
  | ⟨5, _⟩ => @Walk.cons _ G_counter 0 5 5 (by decide : G_counter.Adj 0 5) Walk.nil
  | ⟨6, _⟩ => @Walk.cons _ G_counter 0 6 6 (by decide : G_counter.Adj 0 6) Walk.nil
  | ⟨7, _⟩ => @Walk.cons _ G_counter 0 1 7 (by decide : G_counter.Adj 0 1) (@Walk.cons _ G_counter 1 7 7 (by decide : G_counter.Adj 1 7) Walk.nil)
  | ⟨8, _⟩ => @Walk.cons _ G_counter 0 1 8 (by decide : G_counter.Adj 0 1) (@Walk.cons _ G_counter 1 8 8 (by decide : G_counter.Adj 1 8) Walk.nil)
  | ⟨9, _⟩ => @Walk.cons _ G_counter 0 1 9 (by decide : G_counter.Adj 0 1) (@Walk.cons _ G_counter 1 9 9 (by decide : G_counter.Adj 1 9) Walk.nil)
  | ⟨10, _⟩ => @Walk.cons _ G_counter 0 1 10 (by decide : G_counter.Adj 0 1) (@Walk.cons _ G_counter 1 10 10 (by decide : G_counter.Adj 1 10) Walk.nil)
  | ⟨11, _⟩ => @Walk.cons _ G_counter 0 1 11 (by decide : G_counter.Adj 0 1) (@Walk.cons _ G_counter 1 11 11 (by decide : G_counter.Adj 1 11) Walk.nil)
  | ⟨n + 12, hn⟩ => by omega

@[category API, AMS 5]
lemma G_counter_connected : G_counter.Connected := by
  rw [connected_iff_exists_forall_reachable]
  use 0
  intro w
  exact ⟨path_from_zero w⟩

instance (G : SimpleGraph α) (D : Finset α) [DecidableRel G.Adj] : Decidable (G.IsDominating D) :=
  inferInstanceAs (Decidable (∀ v : α, v ∈ D ∨ ∃ w ∈ D, G.Adj v w))



instance (G : SimpleGraph α) (D : Finset α) [DecidableRel G.Adj] : Decidable (G.IsTotalDominating D) :=
  inferInstanceAs (Decidable (∀ v : α, ∃ w ∈ D, G.Adj v w))

instance (G : SimpleGraph α) (D : Finset α) [DecidableRel G.Adj] : Decidable (IsTotalDominatingSet G D) :=
  inferInstanceAs (Decidable (∀ v : α, ∃ w ∈ D, G.Adj v w))

instance (G : SimpleGraph α) (n : ℕ) (D : Finset α) [DecidableRel G.Adj] : Decidable (@IsNDominatingSet α G n D) :=
  if h1 : G.IsDominating D then
    if h2 : D.card = n then
      isTrue ⟨h1, h2⟩
    else
      isFalse (fun h => h2 h.card_eq)
  else
    isFalse (fun h => h1 h.isDominating)

instance (G : SimpleGraph α) (n : ℕ) (D : Finset α) [DecidableRel G.Adj] : Decidable (@IsNIndepDominatingSet α G n D) :=
  if h1 : G.IsIndepSet D then
    if h2 : G.IsDominating D then
      if h3 : D.card = n then
        isTrue ⟨h1, h2, h3⟩
      else
        isFalse (fun h => h3 h.card_eq)
    else
      isFalse (fun h => h2 h.isDominating)
  else
    isFalse (fun h => h1 h.isIndep)

instance (G : SimpleGraph α) (S : Finset α) [DecidableRel G.Adj] : Decidable (IsMinimalTotalDominatingSet G S) :=
  decidable_of_iff (IsTotalDominatingSet G S ∧ ∀ T ∈ S.powerset, T ≠ S → ¬IsTotalDominatingSet G T) (by
    apply and_congr Iff.rfl
    constructor
    · intro h T hT
      obtain ⟨h_sub, h_ne⟩ := Finset.ssubset_iff_subset_ne.mp hT
      have h_mem : T ∈ S.powerset := Finset.mem_powerset.mpr h_sub
      exact h T h_mem h_ne
    · intro h T hT hT_ne
      have h_sub : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hT, hT_ne⟩
      exact h T h_sub
  )

omit [Fintype α] [DecidableEq α] in
@[category API, AMS 5]
lemma dominationNumber_eq_of_has_of_none {G : SimpleGraph α} [Fintype α] [DecidableEq α] [DecidableRel G.Adj]
    (n : ℕ) (h_has : ∃ D : Finset α, G.IsNDominatingSet n D)
    (h_none : ∀ m < n, ¬ ∃ D : Finset α, G.IsNDominatingSet m D) :
    G.dominationNumber = n := by
  unfold SimpleGraph.dominationNumber
  apply IsLeast.csInf_eq
  constructor
  · exact h_has
  · intro m hm
    rcases hm with ⟨D, hD⟩
    by_contra! h_lt
    exact h_none m h_lt ⟨D, hD⟩

omit [Fintype α] [DecidableEq α] in
@[category API, AMS 5]
lemma indepDominationNumber_eq_of_has_of_none {G : SimpleGraph α} [Fintype α] [DecidableEq α] [DecidableRel G.Adj]
    (n : ℕ) (h_has : ∃ D : Finset α, G.IsNIndepDominatingSet n D)
    (h_none : ∀ m < n, ¬ ∃ D : Finset α, G.IsNIndepDominatingSet m D) :
    G.indepDominationNumber = n := by
  unfold SimpleGraph.indepDominationNumber
  apply IsLeast.csInf_eq
  constructor
  · exact h_has
  · intro m hm
    rcases hm with ⟨D, hD⟩
    by_contra! h_lt
    exact h_none m h_lt ⟨D, hD⟩

/-- The disproof of WOWII Conjecture 327 via a 12-vertex counterexample. -/
@[category research solved, AMS 5]
theorem conjecture327_is_false :
    ∃ (G : SimpleGraph (Fin 12)) (_ : DecidableRel G.Adj),
      G.Connected ∧
      3 * G.dominationNumber = G.indepDominationNumber ∧
      ¬ IsWellTotallyDominated G := by
  use G_counter
  use inferInstance
  refine ⟨?_, ?_, ?_⟩
  · exact G_counter_connected
  · have h_dom : G_counter.dominationNumber = 2 := by
      apply dominationNumber_eq_of_has_of_none 2
      · use {0, 1}; decide +native
      · decide +native
    have h_indep : G_counter.indepDominationNumber = 6 := by
      apply indepDominationNumber_eq_of_has_of_none 6
      · use {0, 7, 8, 9, 10, 11}; decide +native
      · decide +native
    rw [h_dom, h_indep]
  · intro h_well
    have h_S : IsMinimalTotalDominatingSet G_counter {0, 1} := by decide +native
    have h_T : IsMinimalTotalDominatingSet G_counter {1, 10, 7} := by decide +native
    have h_eq := h_well {0, 1} {1, 10, 7} h_S h_T
    revert h_eq
    decide +native

-- Sanity checks

/-- In `K₂`, the max degree is 1 (each vertex has exactly one neighbor). -/
@[category test, AMS 5]
example : (⊤ : SimpleGraph (Fin 2)).maxDegree = 1 := by decide +native

/-- In the path graph `P₃`, vertex 1 has degree 2. -/
@[category test, AMS 5]
example : (SimpleGraph.fromEdgeSet {s(0,1), s(1,2)} : SimpleGraph (Fin 3)).degree 1 = 2 := by
  decide +native

/--
WOWII [Conjecture 327](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

Let `G` be a simple connected graph. If `3 · γ(G) = γ_i(G)`, then `G` is well
totally dominated, where `γ(G)` is the domination number of `G` and `γ_i(G)` is
the independent domination number of `G`.

**Proof Sketch:**
The conjecture states that if $3\gamma(G) = i(G)$ for a connected graph $G$, then $G$ is well totally dominated.
However, this conjecture is **FALSE**.

**Counterexample:**
Consider a graph $G$ with 12 vertices: $u, v, a_0, a_1, a_2, a_3, a_4, b_0, b_1, b_2, b_3, b_4$.
The edges are:
- $(u, v)$
- $(u, a_i)$ for all $i \in \{0, 1, 2, 3, 4\}$
- $(v, b_i)$ for all $i \in \{0, 1, 2, 3, 4\}$
- $(a_0, b_3), (a_1, b_3), (a_2, b_0), (a_3, b_0), (a_4, b_3), (a_4, b_4)$

Properties of $G$:
1. **Connected**: Yes, path exists between any two vertices through $u$ and $v$.
2. **Domination Number $\gamma(G)$**: The set $\{u, v\}$ dominates all vertices. Since there is no universal vertex, $\gamma(G) = 2$.
3. **Independent Domination Number $i(G)$**: The minimum independent dominating set has size 6 (e.g., $\{u, b_0, b_1, b_2, b_3, b_4\}$). Thus $i(G) = 6$.
4. **Condition**: $3 \gamma(G) = 3 \times 2 = 6 = i(G)$. The condition holds.
5. **Well Totally Dominated**: A graph is well totally dominated if all minimal total dominating sets have the same size.
   - $\{u, v\}$ is a minimal total dominating set of size 2.
   - $\{v, b_0, b_3\}$ is a minimal total dominating set of size 3.
   Since $2 \neq 3$, $G$ is NOT well totally dominated.

Since the conjecture is false, it cannot be proven in Lean. We disprove it instead.
-/
@[category research solved, AMS 5]
theorem conjecture327 : answer(False) ↔
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hG : G.Connected)
      (_h : 3 * G.dominationNumber = G.indepDominationNumber),
      IsWellTotallyDominated G := by
  simp
  use Fin 12
  refine ⟨⟨inferInstance⟩, ?_⟩
  rcases conjecture327_is_false with ⟨G, inst, hG, h_eq, h_well⟩
  use G, hG, h_eq, inst, h_well

end WrittenOnTheWallII.GraphConjecture327
