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
module


public import FormalConjecturesForMathlib.Combinatorics.AP.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Order.CompletePartialOrder

open Function Set
open scoped Pointwise

variable {α : Type*} [AddCommMonoid α]

/--
A set $A$ is said to be sum-free if the sumset $A + A$ is disjoint from $A$, i.e.
if the equation $a + b = c$ has no solution with $a, b, c \in A$.
-/
def IsSumFree (A : Set α) : Prop := Disjoint (A + A) A

/-- A set $A$ of natural numbers is said to have bounded gaps if there exists an integer $p$ such
that $A ∩ [n, n + 1, ..., n + p]$ is nonempty for all $n$. -/
def IsSyndetic (A : Set ℕ) : Prop := ∃ p, ∀ n, (A ∩ .Icc n (n + p)).Nonempty

/-- A Sidon set is a set, such that such that all pairwise sums of elements are distinct apart from
coincidences forced by the commutativity of addition. -/
def IsSidon (A : Set α) : Prop := ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

namespace Set

lemma IsSidon.avoids_isAPOfLength_three {A : Set ℕ} (hA : IsSidon A)
    {Y : Set ℕ} (hY : Y.IsAPOfLength 3) :
    (A ∩ Y).ncard ≤ 2 := by
  simp [IsAPOfLength, IsAPOfLengthWith] at hY
  obtain ⟨hc, ⟨a, d, hY⟩⟩ := hY
  have hY_card : Y.ncard = 3 := by simp [ncard, hc]
  by_contra! h
  have hss : Y ⊆ A ∩ Y := by
    have hY_fin : Finite Y := finite_of_ncard_ne_zero (by linarith)
    rw [Set.eq_of_subset_of_ncard_le (Set.inter_subset_right) (by linarith)]
  have ha : a ∈ A := mem_of_mem_inter_left <| hss (hY ▸ ⟨0, by norm_num, by simp⟩)
  have ha₁ : a + d ∈ A := mem_of_mem_inter_left <| hss (hY ▸ ⟨1, by norm_num, by simp⟩)
  have ha₂ : a + 2 • d ∈ A := mem_of_mem_inter_left <| hss (hY ▸ ⟨2, by norm_num, by simp⟩)
  have := hA _ ha _ ha₁ _ ha₂ _ ha₁ (by simp; omega)
  simp at this
  simp [hY, this.1, setOf_and] at hY_card
  linarith [ncard_singleton _ ▸ ncard_inter_le_ncard_right {a | ∃ x, x < 3} {a}]

theorem IsSidon.subset {A B : Set α} (hB : IsSidon B) (hAB : A ⊆ B) : IsSidon A :=
  fun _ _ _ _ _ _ _ _ _ ↦ hB _ (hAB ‹_›) _ (hAB ‹_›) _ (hAB ‹_›) _ (hAB ‹_›) ‹_›

theorem IsSidon.insert {A : Set α} {m : α} [IsRightCancelAdd α] [IsLeftCancelAdd α]
    (hA : IsSidon A) :
    IsSidon (A ∪ {m}) ↔ (m ∈ A ∨ ∀ᵉ (a ∈ A) (b ∈ A), m + m ≠ a + b ∧ ∀ c ∈ A, m + a ≠ b + c) := by
  by_cases h_mem : m ∈ A
  · exact ⟨fun _ ↦ .inl h_mem, fun _ ↦ by rwa [union_singleton, insert_eq_of_mem h_mem]⟩
  refine ⟨fun h ↦ .inr fun a ha b hb ↦ ⟨fun hc ↦ ?_, fun c hc h_contr ↦ ?_⟩, fun hm ↦ ?_⟩
  · exact h m (by simp) a (by simp [ha]) m (by simp) b (by simp [hb]) hc
      |>.elim (fun _ ↦ by simp_all) (fun _ ↦ by simp_all)
  · exact h m (by simp) b (by simp [hb]) a (by simp [ha]) c (by simp [hc]) h_contr
      |>.elim (fun _ ↦ by simp_all) (fun _ ↦ by simp_all)
  · intro i₁ hi₁
    rcases hi₁ with (hi₁ | hi₁)
    · intro j₁ hj₁
      rcases hj₁ with (hj₁ | hj₁)
      · intro i₂ hi₂
        rcases hi₂ with (hi₂ | hi₂)
        · intro j₂ hj₂
          rcases hj₂ with (hj₂ | hj₂)
          · exact fun h ↦ hA i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ h
          · simp_all
            exact fun h ↦ by cases (hm j₁ hj₁ i₁ hi₁).2 i₂ hi₂ (add_comm j₁ m ▸ h.symm)
        · simp_all
          exact fun a ha h ↦ by cases (hm i₁ hi₁ j₁ hj₁).2 a ha (add_comm i₁ m ▸ h)
      · simp_all
        refine ⟨fun b hb h ↦ .inr <| by simp_all [add_comm], fun b hb ↦ ⟨fun h ↦ ?_, ?_⟩⟩
        · cases (hm i₁ hi₁ b hb).1 h.symm
        · exact fun c hc h ↦ by cases ((hm c hc i₁ hi₁).2 b hb) h.symm
    · simp_all
      exact fun _ _ _ _ _ ↦ by simp_all [add_comm]


/-!
Maximal Sidon sets in an interval.

We follow the convention that `IsMaximalSidonSetIn A N` means `A ⊆ {1, …, N}` is Sidon and
is inclusion-maximal among subsets of `Set.Icc 1 N` with the Sidon property.
-/

/-- `IsMaximalSidonSetIn A N` means `A ⊆ {1, …, N}` is Sidon and cannot be extended within
`{1, …, N}` while remaining Sidon. -/
def IsMaximalSidonSetIn (A : Set ℕ) (N : ℕ) : Prop :=
  A ⊆ Set.Icc 1 N ∧ IsSidon A ∧
    ∀ ⦃x : ℕ⦄, x ∈ Set.Icc 1 N → x ∉ A → ¬ IsSidon (A ∪ {x})

namespace IsMaximalSidonSetIn

/-- If `A` is a maximal Sidon set in `{1, …, N}`, then `A ⊆ {1, …, N}`. -/
theorem subset {A : Set ℕ} {N : ℕ} (hA : IsMaximalSidonSetIn A N) :
    A ⊆ Set.Icc 1 N := hA.1

/-- If `A` is a maximal Sidon set in `{1, …, N}`, then `A` is Sidon. -/
theorem isSidon {A : Set ℕ} {N : ℕ} (hA : IsMaximalSidonSetIn A N) : IsSidon A := hA.2.1

/-- Maximality condition unpacked. -/
theorem maximal {A : Set ℕ} {N : ℕ} (hA : IsMaximalSidonSetIn A N) {x : ℕ}
    (hx : x ∈ Set.Icc 1 N) (hxA : x ∉ A) : ¬ IsSidon (A ∪ {x}) := hA.2.2 hx hxA

end IsMaximalSidonSetIn

end Set

namespace Finset

instance (A : Finset α) [DecidableEq α] : Decidable (IsSidon (A : Set α)) :=
  decidable_of_iff (∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A), _) <| by rfl

/-- The maximum size of a Sidon set in the supplied `Finset`. -/
def maxSidonSubsetCard (A : Finset α) [DecidableEq α] : ℕ :=
  (A.powerset.filter fun B : Finset α ↦ IsSidon (B : Set α)).sup Finset.card

/-- If `A` is finite Sidon, then `A ∪ {s}` is also Sidon provided `s ≥ A.max + 1`. -/
theorem IsSidon.insert_ge_max' {A : Finset ℕ} (h : A.Nonempty) (hA : IsSidon (A : Set ℕ)) {s : ℕ}
    (hs : 2 * A.max' h + 1 ≤ s) :
    IsSidon (A ∪ {s}) := by
  have h₁ {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) :
        a + b < 2 * A.max' h + 1 + c := by linarith [A.le_max' _ ha, A.le_max' _ hb]
  have : s ∉ A := by
    exact mt (A.le_max' _) <| not_le.2 <| Finset.max'_lt_iff _ ‹_› |>.2 fun a ha ↦ by
      linarith [A.le_max' _ ha]
  exact (IsSidon.insert hA).2 <| by simpa [this] using fun a ha b hb ↦
    ⟨by linarith [A.le_max' _ ha, A.le_max' _ hb], fun c hc ↦ by linarith [h₁ hc hb ha]⟩

theorem IsSidon.exists_insert {A : Finset ℕ} (h : A.Nonempty) (hA : IsSidon (A : Set ℕ)) :
    ∃ m ∉ A, IsSidon (A ∪ {m}) := by
  refine ⟨2 * A.max' h + 1, ?_, insert_ge_max' h hA le_rfl⟩
  exact mt (A.le_max' _) <| not_le.2 <| Finset.max'_lt_iff _ ‹_› |>.2 fun a ha ↦ by
    linarith [A.le_max' _ ha]

theorem IsSidon.exists_insert_ge {A : Finset ℕ} (h : A.Nonempty) (hA : IsSidon (A : Set ℕ)) (s : ℕ) :
    ∃ m ≥ s, m ∉ A ∧ IsSidon (A ∪ {m}) := by
  refine ⟨if s ≥ 2 * A.max' h + 1 then s else 2 * A.max' h + 1, ?_, ?_, ?_⟩
  · split_ifs <;> linarith
  · split_ifs <;>
    exact mt (A.le_max' _) <| not_le.2 <| Finset.max'_lt_iff _ ‹_› |>.2 fun a ha ↦ by
      linarith [A.le_max' _ ha]
  · split_ifs with hs
    · exact insert_ge_max' h hA hs
    · exact insert_ge_max' h hA le_rfl

end Finset
