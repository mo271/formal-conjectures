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
# Erdős Problem 701

*Reference:* [erdosproblems.com/701](https://www.erdosproblems.com/701)
-/

namespace Erdos701

open Cardinal


set_option linter.style.ams_attribute false
set_option linter.style.category_attribute false
/--
The set $A_n$ is the set of pairs $(n, i)$ where $i < n$.
-/
def A (n : ℕ) : Set (ℕ × ℕ) := { x | x.1 = n ∧ x.2 < n }
/--
The counterexample family $\mathcal{F}$ is the set of all subsets of $A_n$ for some $n$.
-/
def F_ce : Set (Set (ℕ × ℕ)) := { B | ∃ n, B ⊆ A n }
/--
The family $\mathcal{F}$ is a lower set.
-/
lemma F_ce_lower : IsLowerSet F_ce :=
  /-
  If $B \subseteq C \in \mathcal{F}$, then $C \subseteq A_n$ for some $n$.
  Thus $B \subseteq A_n$, so $B \in \mathcal{F}$.
  -/
  by
  intro B C hBC hC
  rcases hC with ⟨n, hn⟩
  exact ⟨n, hBC.trans hn⟩
/--
A pair $(x_1, x_2)$ is in $A_n$ if and only if $x_1 = n$ and $x_2 < n$.
-/
lemma mem_A_iff {n : ℕ} {x : ℕ × ℕ} : x ∈ A n ↔ x.1 = n ∧ x.2 < n :=
  /-
  This follows directly from the definition of $A_n$.
  -/
  Iff.rfl
/--
The set $A_n$ is finite.
-/
lemma A_finite (n : ℕ) : (A n).Finite :=
  /-
  $A_n$ is a subset of the image of the finite set $\{0, 1, \dots, n-1\}$ under the map $i \mapsto (n, i)$.
  -/
  by
  have : A n ⊆ (Finset.range n).image (fun i => (n, i)) := by
    intro x hx
    simp only [A, Set.mem_setOf_eq] at hx
    simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_range]
    exact ⟨x.2, hx.2, by ext <;> simp [hx.1]⟩
  exact Set.Finite.subset (Finset.finite_toSet _) this
/--
The conjecture is false for infinite types.
-/
theorem erdos_701_false :
    ¬ (∀ (F : Set (Set (ℕ × ℕ))), IsLowerSet F →
      ∃ x : ℕ × ℕ, ∀ᵉ (F' ⊆ F),
        F'.Intersecting →
          (#F' ≤ #{ A : Set (ℕ × ℕ) | A ∈ F ∧ x ∈ A })) :=
  /-
  We use the counterexample family $\mathcal{F}$.
  For any $x = (n, m)$, the star at $x$ has size $2^{n-1}$.
  We can pick an intersecting family $\mathcal{F}'$ consisting of all subsets of $A_{n+1}$ containing $(n+1, 0)$.
  The size of $\mathcal{F}'$ is $2^n$, which is strictly greater than $2^{n-1}$.
  Thus, no such $x$ exists.
  -/
  by
  intro h
  rcases h F_ce F_ce_lower with ⟨x, hx⟩
  let n := x.1
  let k := n + 1
  let F' : Set (Set (ℕ × ℕ)) := { B | B ⊆ A k ∧ (k, 0) ∈ B }
  have hF' : F' ⊆ F_ce := by
    intro B hB
    exact ⟨k, hB.1⟩
  have hInt : F'.Intersecting := by
    intro B hB C hC
    rw [Set.not_disjoint_iff]
    exact ⟨(k, 0), hB.2, hC.2⟩
  have h_le := hx F' hF' hInt
  let F_x : Set (Set (ℕ × ℕ)) := { B | B ⊆ A n ∧ x ∈ B }
  have hFx : { B : Set (ℕ × ℕ) | B ∈ F_ce ∧ x ∈ B } = F_x := by
    ext B
    simp only [Set.mem_setOf_eq, F_ce, F_x]
    constructor
    · rintro ⟨⟨m, hm⟩, hxB⟩
      have hxAm : x ∈ A m := hm hxB
      have hmn : m = n := hxAm.1.symm
      subst hmn
      exact ⟨hm, hxB⟩
    · rintro ⟨hBn, hxB⟩
      exact ⟨⟨n, hBn⟩, hxB⟩
  rw [hFx] at h_le

  let g : ℕ × ℕ → ℕ × ℕ := fun y => (k, y.2 + 1)
  let f : Set (ℕ × ℕ) → Set (ℕ × ℕ) := fun B => (g '' B) ∪ {(k, 0)}

  have hg_inj : ∀ y z, y ∈ A n → z ∈ A n → g y = g z → y = z := by
    intro y z hy hz h_eq
    have h_eq2 : (g y).2 = (g z).2 := by rw [h_eq]
    have : y.2 + 1 = z.2 + 1 := h_eq2
    have hy2_eq_z2 : y.2 = z.2 := by omega
    ext
    · rw [hy.1, hz.1]
    · exact hy2_eq_z2

  have hf : ∀ B ∈ F_x, f B ∈ F' := by
    intro B hB
    simp only [F_x, F', Set.mem_setOf_eq] at hB ⊢
    constructor
    · intro y hy
      rcases hy with ⟨z, hz, rfl⟩ | hy
      · have hzA : z ∈ A n := hB.1 hz
        have : z.2 < n := hzA.2
        have h_y_eq : g z = (k, z.2 + 1) := rfl
        rw [h_y_eq]
        exact ⟨rfl, by omega⟩
      · simp only [Set.mem_singleton_iff] at hy
        subst hy
        exact ⟨rfl, by omega⟩
    · exact Set.mem_union_right _ (Set.mem_singleton _)

  have hf_inj : ∀ B ∈ F_x, ∀ C ∈ F_x, f B = f C → B = C := by
    intro B hB C hC heq
    have h1 : g '' B = f B \ {(k, 0)} := by
      ext y
      simp only [f, Set.mem_diff, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨z, hz, rfl⟩
        have h_neq : g z ≠ (k, 0) := by
          intro h_eq
          have : (g z).2 = 0 := by rw [h_eq]
          have : z.2 + 1 = 0 := this
          omega
        exact ⟨Or.inl ⟨z, hz, rfl⟩, h_neq⟩
      · rintro ⟨h | h, h_neq⟩
        · exact h
        · contradiction
    have h2 : g '' C = f C \ {(k, 0)} := by
      ext y
      simp only [f, Set.mem_diff, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨z, hz, rfl⟩
        have h_neq : g z ≠ (k, 0) := by
          intro h_eq
          have : (g z).2 = 0 := by rw [h_eq]
          have : z.2 + 1 = 0 := this
          omega
        exact ⟨Or.inl ⟨z, hz, rfl⟩, h_neq⟩
      · rintro ⟨h | h, h_neq⟩
        · exact h
        · contradiction
    have h3 : g '' B = g '' C := by rw [h1, h2, heq]
    ext y
    constructor
    · intro hy
      have : g y ∈ g '' C := by rw [← h3]; exact Set.mem_image_of_mem g hy
      rcases this with ⟨z, hz, h_eq⟩
      have : y = z := hg_inj y z (hB.1 hy) (hC.1 hz) h_eq.symm
      rwa [this]
    · intro hy
      have : g y ∈ g '' B := by rw [h3]; exact Set.mem_image_of_mem g hy
      rcases this with ⟨z, hz, h_eq⟩
      have : y = z := hg_inj y z (hC.1 hy) (hB.1 hz) h_eq.symm
      rwa [this]

  have h_not_surj : {(k, 0)} ∈ F' ∧ ∀ B ∈ F_x, f B ≠ {(k, 0)} := by
    constructor
    · simp only [F', Set.mem_setOf_eq]
      constructor
      · intro y hy
        simp only [Set.mem_singleton_iff] at hy
        subst hy
        exact ⟨rfl, by omega⟩
      · exact Set.mem_singleton _
    · intro B hB h_eq
      have h_x_in : x ∈ B := hB.2
      have h_gx_in : g x ∈ f B := by
        simp only [f, Set.mem_union]
        exact Or.inl (Set.mem_image_of_mem g h_x_in)
      rw [h_eq] at h_gx_in
      simp only [Set.mem_singleton_iff] at h_gx_in
      have : (g x).2 = 0 := by rw [h_gx_in]
      have : x.2 + 1 = 0 := this
      omega

  let F_x_type := F_x
  let F'_type := F'
  haveI : Fintype F_x_type := by
    have : F_x ⊆ (A n).powerset := fun B hB => hB.1
    have h_fin : F_x.Finite := Set.Finite.subset (Set.Finite.powerset (A_finite n)) this
    exact Set.Finite.fintype h_fin
  haveI : Fintype F'_type := by
    have : F' ⊆ (A k).powerset := fun B hB => hB.1
    have h_fin : F'.Finite := Set.Finite.subset (Set.Finite.powerset (A_finite k)) this
    exact Set.Finite.fintype h_fin

  let f_type : F_x_type → F'_type := fun B => ⟨f B.1, hf B.1 B.2⟩

  have h_inj_type : Function.Injective f_type := by
    intro B C h_eq
    have : f B.1 = f C.1 := by
      have h_eq2 := congr_arg Subtype.val h_eq
      exact h_eq2
    have : B.1 = C.1 := hf_inj B.1 B.2 C.1 C.2 this
    exact Subtype.ext this

  have h_not_surj_type : ¬ Function.Surjective f_type := by
    intro h_surj
    have h_k0 : {(k, 0)} ∈ F' := h_not_surj.1
    let B_k0 : F'_type := ⟨{(k, 0)}, h_k0⟩
    rcases h_surj B_k0 with ⟨B, h_eq⟩
    have : f B.1 = {(k, 0)} := by
      have h_eq2 := congr_arg Subtype.val h_eq
      exact h_eq2
    exact h_not_surj.2 B.1 B.2 this

  have h_lt : Fintype.card F_x_type < Fintype.card F'_type :=
    Fintype.card_lt_of_injective_not_surjective f_type h_inj_type h_not_surj_type

  have h_lt2 : (Fintype.card F_x_type : Cardinal) < (Fintype.card F'_type : Cardinal) :=
    Nat.cast_lt.mpr h_lt

  have h_mk_Fx : #F_x = (Fintype.card F_x_type : Cardinal) := Cardinal.mk_fintype F_x_type
  have h_mk_F' : #F' = (Fintype.card F'_type : Cardinal) := Cardinal.mk_fintype F'_type

  rw [h_mk_Fx, h_mk_F'] at h_le

  exact lt_irrefl _ (h_le.trans_lt h_lt2)

/--
Let $\mathcal{F}$ be a family of sets closed under taking subsets (i.e. if
$B\subseteq A\in\mathcal{F}$ then $B\in \mathcal{F}$). There exists some element $x$ such that
whenever $\mathcal{F}'\subseteq \mathcal{F}$ is an intersecting subfamily we have
$$\lvert \mathcal{F}'\rvert \leq \lvert \{ A\in \mathcal{F} : x\in A\}\rvert.$$
-/
@[category research solved, AMS 5]
theorem erdos_701 : answer(False) ↔ ∀ {X : Type} [Nonempty X],
    ∀ (F : Set (Set X)), IsLowerSet F →
      ∃ x : X, ∀ᵉ (F' ⊆ F),
        F'.Intersecting →
          (#F' ≤ #{ A : Set X | A ∈ F ∧ x ∈ A }) := by
  exact ⟨False.elim, fun h => erdos_701_false fun F hF => h F hF⟩

end Erdos701
