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
# Erdős Problem 152

#TODO: Formalize the corresponding conjecture for infinite Sidon sets.

*References:*
 - [erdosproblems.com/152](https://www.erdosproblems.com/152)
 - [ESS94] Erdős, P. and Sárközy, A. and Sós, T., On Sum Sets of Sidon Sets, I. Journal of Number
    Theory (1994), 329-347.
-/

open scoped Pointwise Asymptotics
open Filter

namespace Erdos152

/-- Define `f n` to be the minimum of `|{s | s - 1 ∉ A + A, s ∈ A + A, s + 1 ∉ A + A}|` as `A`
ranges over all Sidon sets of size `n`. -/
noncomputable def f (n : ℕ) : ℕ :=
  ⨅ A : {A : Set ℕ | A.ncard = n ∧ IsSidon A},
  {s : ℕ | s - 1 ∉ A.1 + A.1 ∧ s ∈ A.1 + A.1 ∧ s + 1 ∉ A.1 + A.1}.ncard



open scoped Classical



open Set Finset

noncomputable def num_isolated (A : Set ℕ) : ℕ :=
  {s : ℕ | s - 1 ∉ A + A ∧ s ∈ A + A ∧ s + 1 ∉ A + A}.ncard

noncomputable def N_k_N (X : Set ℕ) (k : ℕ) : ℕ := {x ∈ X | x + k ∈ X}.ncard
noncomputable def N_k_Z (X : Set ℤ) (k : ℤ) : ℕ := {x ∈ X | x + k ∈ X}.ncard
noncomputable def V_2_N (X : Set ℕ) : ℕ := {x ∈ X | x - 1 ∈ X ∧ x + 1 ∈ X}.ncard
noncomputable def I_N (X : Set ℕ) : ℕ := {x ∈ X | x - 1 ∉ X ∧ x + 1 ∉ X}.ncard

noncomputable def D_set (A : Set ℕ) : Set ℤ :=
  {z : ℤ | ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ z = (a : ℤ) - (b : ℤ)}

noncomputable def ind (X : Set ℤ) (x : ℤ) : ℤ := if x ∈ X then 1 else 0

lemma H_val (X : Set ℤ) (x : ℤ) :
  let a := ind X x; let b := ind X (x+1); let c := ind X (x+2); let d := ind X (x+3)
  a + b + c + a * c + b * d ≥ a * b + 2 * b * c + c * d + a * d := by
  dsimp [ind]; split_ifs <;> omega

lemma sum_H (X : Set ℤ) (S : Finset ℤ) :
  ∑ x ∈ S, (ind X x + ind X (x+1) + ind X (x+2) + ind X x * ind X (x+2) + ind X (x+1) * ind X (x+3)) ≥
  ∑ x ∈ S, (ind X x * ind X (x+1) + 2 * ind X (x+1) * ind X (x+2) + ind X (x+2) * ind X (x+3) + ind X x * ind X (x+3)) := by
  apply sum_le_sum
  intro x _
  exact H_val X x

lemma universal_parity_3 (X : Set ℤ) (hX : X.Finite) :
  4 * N_k_Z X 1 + N_k_Z X 3 ≤ 3 * X.ncard + 2 * N_k_Z X 2 := by
  simp_rw [NNReal.coe_zero.dvd.elim fun and x => X.ncard_eq_toFinset_card hX, N_k_Z]
  trans(4)*.card (hX.toFinset.filter (.+1 ∈hX.toFinset))+.card (hX.toFinset.filter (·+3 ∈hX.toFinset))
  · exact (congr_arg₂ ↑_ ((congr_arg _).comp (congr_arg _) ↑(by simp_all) ) ((congr_arg _) ↑(by simp_all))).le
  trans(3)*hX.toFinset.card+2 * ( hX.toFinset.filter ( ·+2 ∈ (hX.toFinset))).card
  · have:{ a ∈hX.toFinset|a+1 ∈hX.toFinset}∪.image (.+1) { a ∈hX.toFinset|a+1 ∈hX.toFinset} ⊆hX.toFinset:= fun and=> by aesop
    have:= (hX.toFinset.filter ( ·+3 ∈hX.toFinset)).card_le_card ↑( Finset.filter_subset _ _)
    have := ( Finset.card_union _ _).ge.trans ( Finset.card_mono (by valid))
    simp_rw [tsub_le_iff_right, Finset.card_image_of_injective @_ ↑(add_left_injective _),Nat.card_eq_finsetCard] at this⊢
    use (by valid ∘this.trans) (Nat.add_le_add_left (Finset.card_le_card_of_surjOn (.+1) fun and=>by norm_num+contextual[comm, add_assoc]:_≤{ a ∈hX.toFinset|a+2 ∈hX.toFinset}.card) _)
  · exact (congr_arg ↑_ ((congr_arg _) ((Nat.card_eq_finsetCard _)▸congr_arg @_ ↑(by simp_all)))).le

noncomputable def Z_S (X : Set ℕ) : Set ℤ := (fun x : ℕ => (x : ℤ)) '' X

noncomputable def I_Z (X : Set ℤ) : ℕ := {x ∈ X | x - 1 ∉ X ∧ x + 1 ∉ X}.ncard
noncomputable def V_2_Z (X : Set ℤ) : ℕ := {x ∈ X | x - 1 ∈ X ∧ x + 1 ∈ X}.ncard
def C_set_Z (X : Set ℤ) := {x ∈ X | x + 1 ∉ X ∧ x + 2 ∈ X}

lemma I_identity_Z (X : Set ℤ) (hX : X.Finite) :
  I_Z X + 2 * N_k_Z X 1 = X.ncard + V_2_Z X := by
  rw [←eq_comm, I_Z, two_mul,N_k_Z, V_2_Z,(X).ncard_eq_toFinset_card (hX)]
  norm_num[←not_or, add_assoc,←hX.toFinset.filter_card_add_filter_neg_card_eq_card fun and=>and-1 ∈X ∨and+1 ∈X,Set.setOf_and,Set.ncard_eq_toFinset_card _ (hX.sep _),id]
  use(add_left_comm _ _ _).trans ((congr_arg₂ _) ((Nat.card_eq_finsetCard _)▸congr_arg _ (by aesop)) ((congr_arg (.+ _) ((by rw [ Finset.filter_or, Finset.card_union]))).trans ?_))
  apply((congr_arg _).comp (Nat.card_congr ((.subtypeEquiv (.refl Int) ((by simp_all))))).trans (Nat.card_eq_finsetCard _)).trans.comp (Nat.sub_add_cancel.comp (le_add_right) (Finset.card_filter_le _ _)).trans
  exact (congr_arg₂ _) ((Nat.card_eq_finsetCard _)▸Nat.card_congr (.subtypeEquiv (.subRight (1)) (by simp_all [and_comm]))) (Nat.card_eq_finsetCard @_▸congr_arg @_ ((congr_arg _) ((funext ((by simp_all))))))

def C1 (X : Set ℤ) := {x ∈ C_set_Z X | x - 1 ∉ X}
def C2 (X : Set ℤ) := {x ∈ C_set_Z X | x + 3 ∉ X}
def C3 (X : Set ℤ) := {x ∈ C_set_Z X | x - 1 ∈ X}
def C4 (X : Set ℤ) := {x ∈ C_set_Z X | x + 3 ∈ X}

lemma C_bound (X : Set ℤ) (hX : X.Finite) :
  (C_set_Z X).ncard ≤ (C1 X).ncard + (C3 X).ncard ∧
  (C_set_Z X).ncard ≤ (C2 X).ncard + (C4 X).ncard := by
  delta C1 and C4 C3 C2 and C_set_Z
  repeat use(Set.ncard_inter_add_ncard_diff_eq_ncard _ _ (hX.sep _)).ge.trans_eq<|add_comm _ _

lemma C1_bound (X : Set ℤ) (hX : X.Finite) : (C1 X).ncard ≤ I_Z X := by show Nat.card {s |_}≤.card {s |_}
                                                                        exact (Nat.card_mono) (hX.sep _) fun and=>.rec fun ⟨a, _⟩M=>by grind
lemma C2_bound (X : Set ℤ) (hX : X.Finite) : (C2 X).ncard ≤ I_Z X := by show (@Nat.card {s |_}) ≤.card {s |_}
                                                                        push_cast[Set.setOf_and, C_set_Z,Nat.card_eq_fintype_card, Fintype.card_ofFinset]
                                                                        exact (Nat.card_image_of_injective (add_left_injective 2) _).ge.trans (Nat.card_mono (hX.sep _) (@Set.image_subset_iff.2 fun and=>.symm ∘by simp_all[add_sub_assoc, add_assoc]))
lemma C34_bound (X : Set ℤ) (hX : X.Finite) : (C3 X).ncard + (C4 X).ncard ≤ N_k_Z X 3 := by delta C4 and N_k_Z and C3
                                                                                            norm_num[uniformContinuous_iff,C_set_Z]
                                                                                            by_cases h:{ c | ((c ∈X∧c+1 ∉X) ∧c ∈X∧c+2 ∈X) ∧c-1 ∈X}.Finite∧{a | ((a ∈X∧a+1 ∉X) ∧ a ∈X∧a+2 ∈X) ∧a+3 ∈ X}.Finite
                                                                                            · trans(h.1.toFinset.image (.-1)∪h.2.toFinset).card
                                                                                              · rw [Set.ncard_eq_toFinset_card @_ (h.1),Set.ncard_eq_toFinset_card (@ _) h.2, Finset.card_union_of_disjoint (Finset.disjoint_left.mpr.comp Finset.forall_mem_image.mpr (by simp_all)), Finset.card_image_of_injective @_]
                                                                                                use sub_left_injective
                                                                                              · exact (Nat.card_eq_finsetCard _)▸Nat.card_mono (hX.sep _) (Finset.forall_mem_union.2 ⟨ Finset.forall_mem_image.2 (by simp_all[sub_add]), fun and=>.imp_left (·.2.1) ∘h.2.mem_toFinset.1⟩)
                                                                                            · rcases h ⟨hX.subset fun and true => true.1.1.1,hX.subset fun and true => true.1.2.1⟩

lemma local_pattern_C_Z (X : Set ℤ) (hX : X.Finite) :
  2 * (C_set_Z X).ncard ≤ N_k_Z X 3 + 2 * I_Z X := by
  have h1 := C_bound X hX
  have h2 := C1_bound X hX
  have h3 := C2_bound X hX
  have h4 := C34_bound X hX
  omega

lemma local_pattern_bound_Z_hN (X : Set ℤ) (hX : X.Finite) :
  N_k_Z X 2 = V_2_Z X + (C_set_Z X).ncard := by
  unfold N_k_Z V_2_Z C_set_Z
  set A := {x ∈ X | x + 1 ∈ X ∧ x + 2 ∈ X}
  set B := {x ∈ X | x + 1 ∉ X ∧ x + 2 ∈ X}
  have hA_fin : A.Finite := Set.Finite.subset hX (fun x hx => hx.1)
  have hB_fin : B.Finite := Set.Finite.subset hX (fun x hx => hx.1)
  have h_union : A ∪ B = {x ∈ X | x + 2 ∈ X} := by
    ext x
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (⟨hx, hx1, hx2⟩ | ⟨hx, hx1, hx2⟩) <;> exact ⟨hx, hx2⟩
    · intro ⟨hx, hx2⟩
      by_cases h : x + 1 ∈ X
      · left; exact ⟨hx, h, hx2⟩
      · right; exact ⟨hx, h, hx2⟩
  have h_disj : Disjoint A B := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false]
    constructor
    · rintro ⟨⟨hx, hx1, hx2⟩, ⟨hy, hy1, hy2⟩⟩
      exact hy1 hx1
    · exact False.elim
  have h_A_card : A.ncard = {x ∈ X | x - 1 ∈ X ∧ x + 1 ∈ X}.ncard := by
    have h_inj : InjOn (fun x => x + 1) A := by
      intro x _ y _ h_eq
      dsimp only at h_eq
      omega
    have h_im : (fun x => x + 1) '' A = {x ∈ X | x - 1 ∈ X ∧ x + 1 ∈ X} := by
      ext y
      simp only [Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨hx.2.1, ?_, ?_⟩
        · have : x + 1 - 1 = x := by omega
          rw [this]
          exact hx.1
        · have : x + 1 + 1 = x + 2 := by omega
          rw [this]
          exact hx.2.2
      · intro hy
        use y - 1
        constructor
        · refine ⟨hy.2.1, ?_, ?_⟩
          · have : y - 1 + 1 = y := by omega
            rw [this]
            exact hy.1
          · have : y - 1 + 2 = y + 1 := by omega
            rw [this]
            exact hy.2.2
        · exact sub_add_cancel y 1
    rw [← h_im]
    exact (ncard_image_of_injOn h_inj).symm
  have h_card_union : {x ∈ X | x + 2 ∈ X}.ncard = A.ncard + B.ncard := by
    rw [← h_union]
    apply ncard_union_eq h_disj hA_fin hB_fin
  omega

lemma local_pattern_bound_Z (X : Set ℤ) (hX : X.Finite) :
  2 * N_k_Z X 2 ≤ N_k_Z X 3 + 2 * V_2_Z X + 2 * I_Z X := by
  have hC := local_pattern_C_Z X hX
  have hN := local_pattern_bound_Z_hN X hX
  omega

lemma num_isolated_Z_rel (A : Set ℕ) :
  I_Z (Z_S (A + A)) ≤ num_isolated A + 1 := by
  norm_num(config := {singlePass := 1})[I_Z, false,num_isolated, true, Z_S]
  by_cases h:{M|M-1 ∉A+A∧M ∈A+A∧M+1 ∉A+A}.Finite
  · use(Nat.card_mono (h.image (↑) |>.insert 0) ? _).trans (.trans (Set.ncard_insert_le _ _) (by rw [Set.ncard_image_of_injective _ Nat.cast_injective]))
    refine fun and⟨ ⟨a, A, I⟩,R, L⟩=>by cases I with use a.eq_zero_or_pos.imp ↑(congr_arg _) (by use a, ⟨ fun and=>(R _) ⟨and,Nat.cast_pred ·⟩,A,(L _ ⟨ ·, rfl⟩)⟩)
  · exact (Set.Infinite.ncard (h.comp (·.preimage Nat.cast_injective.injOn|>.insert 0|>.subset ↑ fun and⟨A, B, C⟩=>and.eq_zero_or_pos.imp_right fun and' =>⟨⟨ _,B, rfl⟩,by grind⟩))).trans_le bot_le

lemma N_k_Z_rel_1 (A : Set ℕ) : N_k_Z (Z_S (A + A)) (1 : ℤ) = N_k_N (A + A) 1 := by
  delta N_k_N and N_k_Z Z_S
  exact (congr_arg ↑_ ↑(Set.ext (by·grind))).trans (Set.ncard_image_of_injective ↑_ Nat.cast_injective)

lemma N_k_Z_rel_2 (A : Set ℕ) : N_k_Z (Z_S (A + A)) (2 : ℤ) = N_k_N (A + A) 2 := by
  norm_num (config := {singlePass :=1}) [N_k_Z, N_k_N, Z_S]
  exact (congr_arg _ (Set.ext fun and=>by use And.elim (·.elim fun and true => true.2▸mod_cast by aesop), by aesop)).trans (Set.ncard_image_of_injective _ Nat.cast_injective)

lemma N_k_Z_rel_3 (A : Set ℕ) : N_k_Z (Z_S (A + A)) (3 : ℤ) = N_k_N (A + A) 3 := by
  delta N_k_N and N_k_Z Z_S
  refine ((congr_arg _) ↑(Set.ext fun and=>? _)).trans.comp (Set.ncard_image_of_injective _) Nat.cast_injective
  use fun⟨ ⟨a, C, H⟩,b,A, B⟩=> (by use a, ⟨ C,by cases H with cases B with valid⟩),fun ⟨a, C, H⟩=>H▸⟨ ⟨a, C.1, rfl⟩,_, C.2, rfl⟩

lemma Z_S_card (A : Set ℕ) :
  (Z_S (A + A)).ncard = (A + A).ncard := by
  delta Z_S
  exact (Set.ncard_image_of_injective _) Nat.cast_injective

def quad_k_N (A : Set ℕ) (k : ℕ) : Set (ℕ × ℕ × ℕ × ℕ) :=
  {q | q.1 ∈ A ∧ q.2.1 ∈ A ∧ q.2.2.1 ∈ A ∧ q.2.2.2 ∈ A ∧ q.1 + q.2.1 + k = q.2.2.1 + q.2.2.2}

lemma quad_upper_Q0 (A : Set ℕ) (k : ℕ) (_ : IsSidon A) (hA : A.Finite) (hk : k > 0) :
  {q ∈ quad_k_N A k | (q.1 : ℤ) - q.2.2.1 = 0}.ncard ≤ A.ncard := by show{ a ∈{s |_}|_}.ncard≤_
                                                                     simp_all[IsSidon,add_assoc, sub_eq_zero]
                                                                     use Nat.card_image_of_injOn ( fun and=>? _)|>.ge.trans (Nat.card_mono hA (Set.image_subset_iff.2 fun and=>And.left ∘And.left))
                                                                     use fun a s R L=>by cases‹∀ _ _ _ _ _ _ _ _ C,_› _ R.1.2.1 _ (by use a.1.2.1) ( _) (by use a.1.2.2.2.1) ( _) (by use R.1.2.2.2.1) (by use a.elim (R.elim (by valid))) with grind

lemma quad_upper_Qk_inj (A : Set ℕ) (k : ℕ) (_ : IsSidon A) (hk : k > 0) :
  InjOn (fun q : ℕ × ℕ × ℕ × ℕ => q.2.1) {q ∈ quad_k_N A k | (q.1 : ℤ) - q.2.2.1 = -k} := by
  use show{ a ∈{s |_}|_}.InjOn _ from fun and a s R L=>Prod.ext_iff.2 (a.1.elim (R.1.elim fun and _ _ _=>?_))
  simp_all[IsSidon, add_right_comm, sub_right_injective.eq_iff' (sub_sub_self _ _),Prod.ext_iff]
  cases‹∀ (x _ _ _ _ _ _ _ _),_› _ (by valid) ( _) (by use and) ( s).2.2.1 (by bound) ( _) (by use (by valid:).1) (by valid) with valid

lemma quad_upper_Qk_im (A : Set ℕ) (k : ℕ) (_ : IsSidon A) (hk : k > 0) :
  (fun q : ℕ × ℕ × ℕ × ℕ => q.2.1) '' {q ∈ quad_k_N A k | (q.1 : ℤ) - q.2.2.1 = -k} ⊆ A := by
  exact (Set.image_subset_iff.mpr fun and' =>And.elim (by cases · with tauto))

lemma quad_upper_Qk (A : Set ℕ) (k : ℕ) (hSidon : IsSidon A) (hA : A.Finite) (hk : k > 0) :
  {q ∈ quad_k_N A k | (q.1 : ℤ) - q.2.2.1 = -k}.ncard ≤ A.ncard := by
  have h_inj := quad_upper_Qk_inj A k hSidon hk
  have h_im := quad_upper_Qk_im A k hSidon hk
  have h_fin : {q ∈ quad_k_N A k | (q.1 : ℤ) - q.2.2.1 = -k}.Finite := by apply_rules[(hA.of_injOn)]
                                                                          rwa[Set.image_subset_iff]at*
  have h_card := ncard_image_of_injOn h_inj
  have h_le := ncard_le_ncard h_im hA
  omega

lemma quad_upper_other_inj (A : Set ℕ) (k : ℕ) (_ : IsSidon A) :
  InjOn (fun q : ℕ × ℕ × ℕ × ℕ => (q.1 : ℤ) - q.2.2.1) {q ∈ quad_k_N A k | (q.1 : ℤ) - q.2.2.1 ≠ 0 ∧ (q.1 : ℤ) - q.2.2.1 ≠ -k} := by
  refine show (Set.InjOn _) { a ∈ {s |_}|_} from fun and ⟨ ⟨a, _⟩,R, _⟩b ⟨ ⟨a, _⟩, _⟩p=>?_
  simp_all[IsSidon, sub_eq_sub_iff_add_eq_add, add_assoc, add_left_comm,Prod.ext_iff]
  cases eq_or_ne and.1 b.1
  · cases‹∀ _ _ _ _ _ _ _ _ C,_› and.2.1 (by bound) b.2.1 (by bound) b.2.2.2 (by bound) and.2.2.2 (by bound) (by valid) with valid
  · exact absurd (‹∀ _ _ _ _ _ _ _ __, _› and.1 · b.1 · b.2.2.1 · and.2.2.fst) (by norm_num[*,Nat.cast_injective p,Nat.cast_injective.ne_iff.1 (sub_ne_zero.1 R)])

lemma quad_upper_other_im (A : Set ℕ) (k : ℕ) (_ : IsSidon A) :
  (fun q : ℕ × ℕ × ℕ × ℕ => (q.1 : ℤ) - q.2.2.1) '' {q ∈ quad_k_N A k | (q.1 : ℤ) - q.2.2.1 ≠ 0 ∧ (q.1 : ℤ) - q.2.2.1 ≠ -k} ⊆ {x ∈ D_set A | x + k ∈ D_set A} := by
  show _ ''{ a ∈{s |_}|_} ⊆_
  simp_all (config := {singlePass:= true}) -contextual[ Erdos152.D_set, IsSidon]
  use fun and A B a s R L K V _ _=>⟨⟨ _,s,B,L, rfl⟩,a,K,A,R,by valid⟩

lemma quad_upper_other (A : Set ℕ) (k : ℕ) (hSidon : IsSidon A) (_ : A.Finite) :
  {q ∈ quad_k_N A k | (q.1 : ℤ) - q.2.2.1 ≠ 0 ∧ (q.1 : ℤ) - q.2.2.1 ≠ -k}.ncard ≤ N_k_Z (D_set A) k := by
  have h_inj := quad_upper_other_inj A k hSidon
  have h_im := quad_upper_other_im A k hSidon
  have h_fin : {x ∈ D_set A | x + k ∈ D_set A}.Finite := by delta D_set
                                                            exact (.sep ↑(.subset (.image (Prod.rec _) ↑(.prod (by assumption) (by assumption))) fun and ⟨x,y,A, B, e⟩=>by use(x, y), ⟨A, B⟩,e.symm) _)
  have h_card := ncard_image_of_injOn h_inj
  have h_le := ncard_le_ncard h_im h_fin
  unfold N_k_Z
  omega

lemma quad_upper_part (A : Set ℕ) (k : ℕ) (_ : A.Finite) :
  (quad_k_N A k).ncard ≤
  {q ∈ quad_k_N A k | (q.1 : ℤ) - q.2.2.1 = 0}.ncard +
  {q ∈ quad_k_N A k | (q.1 : ℤ) - q.2.2.1 = -k}.ncard +
  {q ∈ quad_k_N A k | (q.1 : ℤ) - q.2.2.1 ≠ 0 ∧ (q.1 : ℤ) - q.2.2.1 ≠ -k}.ncard := by exact (congr_arg _ (Set.ext (by grind))).trans_le.comp (Set.ncard_union_le _ _).trans (Nat.add_le_add_right (Set.ncard_union_le _ _) _)

lemma quad_upper (A : Set ℕ) (k : ℕ) (hSidon : IsSidon A) (hA : A.Finite) (hk : k > 0) :
  (quad_k_N A k).ncard ≤ N_k_Z (D_set A) k + 2 * A.ncard := by
  have h1 := quad_upper_part A k hA
  have h2 := quad_upper_Q0 A k hSidon hA hk
  have h3 := quad_upper_Qk A k hSidon hA hk
  have h4 := quad_upper_other A k hSidon hA
  omega

def S_good (A : Set ℕ) (k : ℕ) := {s ∈ A + A | s + k ∈ A + A ∧ ¬(∃ a ∈ A, s = 2 * a) ∧ ¬(∃ a ∈ A, s + k = 2 * a)}

noncomputable def quad_fiber (A : Set ℕ) (s k : ℕ) : Set (ℕ × ℕ × ℕ × ℕ) :=
  {q ∈ A ×ˢ (A ×ˢ (A ×ˢ A)) | q.1 + q.2.1 = s ∧ q.2.2.1 + q.2.2.2 = s + k}

lemma quad_fiber_subset (A : Set ℕ) (hA : A.Finite) (s k : ℕ) :
  quad_fiber A s k ⊆ quad_k_N A k := by use show{s |_} ⊆{s |_} from fun and ⟨a, _⟩=>Set.mem_setOf.2 ?_
                                        norm_num[*, a.2.1, a.1, a.2.2.1, a.2.2.2]

lemma quad_fiber_card (A : Set ℕ) (hA : A.Finite) (k : ℕ) (s : ℕ) (hs : s ∈ S_good A k) :
  4 ≤ (quad_fiber A s k).ncard := by change(4)≤ {s |_}.ncard
                                     obtain ⟨a, rfl⟩:= (hA).exists_finset_coe
                                     simp_all-contextual[ Erdos152.S_good,Set.setOf_and,Set.ncard_eq_toFinset_card']
                                     trans {S ∈a ×ˢa ×ˢa ×ˢa | S.1+S.2.1 = s∧S.2.2.1+S.2.2.2 = s+k}.card
                                     · use hs.1.1.elim fun and⟨i,A, B, _⟩=>hs.1.2.elim fun x⟨R, L, M, _⟩=> if I:and = A then(? _)else if I:x =L then(? _)else(? _)
                                       · rcases hs.2.1.2 A B (by (bound ) )
                                       · rcases hs.right.2.right L M (by (fin_omega))
                                       · exact ( Finset.card_mono (by simp_all -contextual[ Finset.insert_subset_iff,add_comm]:{ (and,A,x,L),(A, and,x,L), (and,A,L,x),(A, and, L,x)} ⊆(_: Finset _))).trans' (by norm_num[*])
                                     · exact (Nat.card_eq_finsetCard _)▸((congr_arg _) (by norm_num [Set.inter_def])).le

lemma quad_fiber_disjoint (A : Set ℕ) (hA : A.Finite) (k : ℕ) (s1 s2 : ℕ) (h : s1 ≠ s2) :
  Disjoint (quad_fiber A s1 k) (quad_fiber A s2 k) := by change Disjoint {s |_} {s |_ ∈{s |_}}
                                                         exact (Set.disjoint_left.2 fun and R L=>h (R.2.1▸L.2.1))

lemma quad_lower_sub_fin (A : Set ℕ) (k : ℕ) (hA : A.Finite) :
  (S_good A k).Finite := by show({s |_ ∈{s |_}}).Finite
                            apply (hA.add (hA)).sep

lemma quad_lower_sub (A : Set ℕ) (k : ℕ) (hA : A.Finite) :
  4 * (S_good A k).ncard ≤ (quad_k_N A k).ncard := by
  have hS_fin := quad_lower_sub_fin A k hA
  set Q := ⋃ s ∈ S_good A k, quad_fiber A s k
  have h_Q_sub : Q ⊆ quad_k_N A k := by refine iSup₂_le fun and R M ⟨a, _⟩ =>Set.mem_setOf.2 ?_
                                        simp_all
  have h_Q_card : Q.ncard = ∑ s ∈ hS_fin.toFinset, (quad_fiber A s k).ncard := by change (star _)=(∑ a ∈ _,Nat.card {s |_})
                                                                                  lift A to Finset (↑ ℕ) using(hA) with R L
                                                                                  trans∑ a ∈hS_fin.toFinset,.card {S ∈R ×ˢR ×ˢR ×ˢR | S.1+S.2.1 = a ∧S.2.2.1+S.2.2.2 = a+k}
                                                                                  · simp_rw [id,Q, L.symm,Nat.card_eq_finsetCard] at hS_fin⊢
                                                                                    show star (ENat.toNat (Set.encard (⋃ a ∈ _,{s |_}))) = _
                                                                                    exact (congr_arg star ((congr_arg _) ((congr_arg _ (by aesop)).trans (.trans (Set.encard_coe_eq_coe_finsetCard _) ((congr_arg _) (Finset.card_biUnion fun and _ _ _ _=> Finset.disjoint_filter.2 (by valid)))))))
                                                                                  · simp_rw [Set.coe_setOf,Set.mem_prod, R.mem_coe, Finset.mem_filter, R.mem_product]
  have h_sum_le : ∑ s ∈ hS_fin.toFinset, 4 ≤ Q.ncard := by refine (by valid▸ Finset.sum_le_sum fun and μ=> show (4 ≤Nat.card {s |_} ) from(hS_fin.mem_toFinset.mp μ).elim fun and j=>? _)
                                                           revert‹ℕ›μ Q hS_fin h_Q_sub h_Q_card
                                                           use hA.coe_toFinset▸ fun and I I R M ⟨a, C, d, E, _⟩⟨⟨x,y,A, B, _⟩,k, _⟩=>(? _)
                                                           trans .card ({(a, d,x,A), (d,a,x,A), ( a, d, A, x), (d, a, A,x)}: Finset _)
                                                           · exact (Nat.card_eq_fintype_card.trans (by norm_num[show a≠d∧x≠A by repeat use fun and=>k ⟨a, C,by_contra (by valid ∘ fun and=>by use x,y,by (fin_omega))⟩])).ge
                                                           · exact (Nat.card_mono) (.of_fintype _) ((by simp_all-contextual[add_comm,Set.insert_subset_iff]))
  have h_sum_eq : ∑ s ∈ hS_fin.toFinset, 4 = 4 * (S_good A k).ncard := by exact (Set.ncard_eq_toFinset_card ↑_ hS_fin▸ Finset.sum_const _).trans (mul_comm _ _)
  have hQk_fin : (quad_k_N A k).Finite := by refine show {s |_}.Finite from hA.exists_le.elim fun and x =>BddAbove.finite ⟨ (and, and, and, and),fun R L=>?_⟩
                                             exact L.imp (x _) ↑(.imp (x _) ↑(.imp (x _) (x @_ ·.1)))
  have h_Q_le : Q.ncard ≤ (quad_k_N A k).ncard := by iterate gcongr
  omega

lemma quad_lower_edges (A : Set ℕ) (k : ℕ) (hA : A.Finite) :
  N_k_N (A + A) k ≤ (S_good A k).ncard + 2 * A.ncard := by rw[two_mul,N_k_N,S_good]
                                                           trans{ a ∈A+A|a+k ∈A+A∧¬(∃S ∈A,a=2* S) ∧¬∃S ∈A,a+k=2* S}.ncard+(((A.image (2 *.))∪A.image (2 *.-k)).ncard)
                                                           · use(Set.ncard_le_ncard (fun R L=>? _) ((hA.add hA).sep _|>.union ((hA.image _).union (hA.image _) ) )).trans ↑(Set.ncard_union_le _ _)
                                                             use or_iff_not_imp_right.2 (and_assoc.1 ⟨ L,. ∘.inl ∘.imp (by bound),by valid ∘Or.inr ∘Exists.imp fun and=>And.imp_right (Nat.sub_eq_of_eq_add ·.symm)⟩)
                                                           · apply add_right_mono ((Set.ncard_union_le _ _).trans (by push_cast [Nat.add_le_add, A.ncard_image_le hA]))

lemma quad_lower (A : Set ℕ) (k : ℕ) (hSidon : IsSidon A) (hA : A.Finite) :
  4 * N_k_N (A + A) k ≤ (quad_k_N A k).ncard + 8 * A.ncard := by
  have h1 := quad_lower_sub A k hA
  have h2 := quad_lower_edges A k hA
  omega

lemma quad_lower_2 (A : Set ℕ) (k : ℕ) (hSidon : IsSidon A) (hA : A.Finite) :
  N_k_Z (D_set A) k ≤ (quad_k_N A k).ncard + 2 * A.ncard := by
  simp_rw [N_k_Z, two_mul,D_set]
  show@@_≤Nat.card {s |_} +_
  by_cases h:{ a ∈A ×ˢA ×ˢA ×ˢA|a.1+a.2.1+k = a.2.2.1+ a.2.snd.snd}.Finite
  · trans .card (h.toFinset.image fun and=> (and.fst -and.snd.2.snd : ℤ))+(A.ncard+ A.ncard)
    · use le_add_right (Nat.card_mono (Finset.finite_toSet _) fun and⟨ ⟨a, C, E, F, G⟩,x,y,A, B, _⟩=>G▸ Finset.mem_image.2 ? _)
      exists(a,y,x,C),h.mem_toFinset.2 ⟨⟨E,B,A,F⟩,by fin_omega⟩
    · exact (Nat.add_le_add_right ((Nat.card_eq_finsetCard _)▸ Finset.card_image_le.trans_eq ((Nat.card_eq_finsetCard _)▸congr_arg _ (by simp_all[and_assoc]))) _)
  · rcases h (.sep ↑(.prod hA (hA.prod (hA.prod hA))) _)

lemma quad_upper_2 (A : Set ℕ) (k : ℕ) (hSidon : IsSidon A) (hA : A.Finite) :
  (quad_k_N A k).ncard ≤ 4 * N_k_N (A + A) k + 2 * A.ncard := by
  show @Nat.card {s |_}≤(4)*.card @_ +_
  lift A to Finset ℕ using hA
  trans{ a ∈A ×ˢA ×ˢA ×ˢA|a.1+a.2.1+k = a.2.2.1+a.2.2.2}.card
  · exact (Nat.card_eq_finsetCard _)▸(((congr_arg _) ↑(by simp_all [ and_assoc]))).ge
  push_cast[Set.setOf_and, A.sum_product, A.mem_coe, two_mul,IsSidon,Set.mem_add,Nat.card_eq_fintype_card,Set.ncard_eq_toFinset_card', Fintype.card_ofFinset, Finset.card_filter]at *
  trans(4)*.card { a ∈(A ×ˢA).image fun and=>and.1+and.2|∃S ∈A,∃T ∈A,S+T = a+k}+(A.card+A.card)
  · use(A.sum_product' _ _).ge.trans (Nat.card_eq_finsetCard _▸.trans (by rw [←funext fun and=> A.sum_product' _ _ ,← Finset.sum_fiberwise_of_maps_to fun and=>(A ×ˢA).mem_image_of_mem fun and=>and.1+and.2]) ? _)
    trans∑ a ∈{ a ∈(A ×ˢA).image fun and=>and.1+and.2|∃S ∈A,∃T ∈A,S+T = a+k},4
    · use(Finset.sum_subset (by bound) ?_).ge.trans ( Finset.sum_le_sum fun and x =>( Finset.sum_le_sum fun and μ=>by rw [← Finset.card_filter]).trans (?_))
      · use fun and a s => Finset.sum_eq_zero fun and β=> Finset.sum_eq_zero fun and α=>if_neg (( Finset.mem_filter.1 β).2▸ (s.comp ( Finset.mem_filter.mpr ⟨a, _,(A.mem_product.mp α).1, _,(A.mem_product.mp α).2, ·.symm⟩)))
      use(Finset.mem_filter.1 x).2.elim fun and ⟨a, C, _⟩=>.trans ( Finset.sum_le_card_nsmul _ _ _ fun R M=>show _≤2 from(?_)) (mul_le_mul_right' (?_:_≤2) _)
      · exact ( Finset.card_mono fun and=>by simp_all[and.ext_iff]).trans (Finset.card_le_two: Finset.card { (and, C),(C, and)}≤2)
      · exact ( Finset.filter _ _).eq_empty_or_nonempty.elim (.▸bot_le) (fun⟨(x, y), _⟩=>.trans ( Finset.card_mono fun and=>by simp_all[and.ext_iff]) ( Finset.card_le_two: Finset.card {(x, y), ⟨y,x⟩}≤2))
    · exact ( Finset.sum_const 4)▸Nat.card_eq_finsetCard _▸Nat.mul_comm _ _▸le_self_add
  · exact (congr_arg₂ ↑( _) ((congr_arg _).comp (congr_arg _) (by·norm_num[Set.inter_def, and_assoc])) (by ·norm_num)).le

lemma N_bound_upper_1 (A : Set ℕ) (hA : A.Finite) (hSidon : IsSidon A) :
  4 * N_k_N (A + A) 1 ≤ N_k_Z (D_set A) 1 + 10 * A.ncard := by
  have h1 := quad_lower A 1 hSidon hA
  have h2 : (quad_k_N A 1).ncard ≤ N_k_Z (D_set A) (1 : ℤ) + 2 * A.ncard := quad_upper A 1 hSidon hA (by omega)
  omega

lemma N_bound_lower_2 (A : Set ℕ) (hA : A.Finite) (hSidon : IsSidon A) :
  N_k_Z (D_set A) 2 ≤ 4 * N_k_N (A + A) 2 + 10 * A.ncard := by
  have h1 := quad_lower_2 A 2 hSidon hA
  have h2 : N_k_Z (D_set A) (2 : ℤ) ≤ (quad_k_N A 2).ncard + 2 * A.ncard := quad_lower_2 A 2 hSidon hA
  have h3 : (quad_k_N A 2).ncard ≤ 4 * N_k_N (A + A) 2 + 2 * A.ncard := quad_upper_2 A 2 hSidon hA
  omega

lemma N_bound_upper_3 (A : Set ℕ) (hA : A.Finite) (hSidon : IsSidon A) :
  4 * N_k_N (A + A) 3 ≤ N_k_Z (D_set A) 3 + 10 * A.ncard := by
  have h1 := quad_lower A 3 hSidon hA
  have h2 : (quad_k_N A 3).ncard ≤ N_k_Z (D_set A) (3 : ℤ) + 2 * A.ncard := quad_upper A 3 hSidon hA (by omega)
  omega

lemma D_set_card (A : Set ℕ) (hA : A.Finite) :
  (D_set A).ncard ≤ A.ncard * A.ncard := by
  simp_rw [D_set, mul_comm (A.ncard)]
  use A.ncard_prod▸.trans (Nat.card_mono ((hA.prod hA).image ((Prod.rec _) ) ) fun and⟨x,y,A, B, e⟩=>by cases e with exists(x, y)) (Nat.card_image_le (hA.prod hA))

lemma S_card (A : Set ℕ) (hA : A.Finite) (hSidon : IsSidon A) :
  2 * (A + A).ncard ≥ A.ncard * A.ncard := by
  lift A to Finset (↑ ℕ) using (hA) with and A
  rw_mod_cast[ge_iff_le, two_mul,IsSidon]at*
  use and.card_product and▸.trans ( Finset.card_eq_sum_card_fiberwise fun and' =>And.elim and.add_mem_add ∘ Finset.mem_product.1).le ?_
  use Nat.mul_two _▸ Finset.sum_le_card_nsmul _ _ _ (and.forall_mem_image₂.2 fun and R L M=>.trans ( Finset.card_mono fun and=> by aesop) ( Finset.card_le_two: Finset.card { (and, L),(L, and)}≤2))

lemma num_isolated_lower_bound (n : ℕ) (hn : n > 0) (A : Set ℕ) (h_card : A.ncard = n) (h_sidon : IsSidon A) :
  16 * num_isolated A + 100 * n + 16 ≥ n * n := by
  have hF : A.Finite := Set.finite_of_ncard_pos (by omega)
  have hSF : (A + A).Finite := Set.Finite.add hF hF
  have hSF_Z : (Z_S (A + A)).Finite := by simp_rw [ ←h_card,Z_S]at *
                                          apply hSF.image
  have hDF : (D_set A).Finite := by simp_all [D_set]
                                    exact ( (hF.prod hF).image (Prod.rec _)).subset fun and⟨x,k,y,A, B⟩=>⟨(x, y), ⟨k,A⟩,B.symm⟩
  have h1 := I_identity_Z (Z_S (A + A)) hSF_Z
  have h2 := universal_parity_3 (D_set A) hDF
  have h3 := local_pattern_bound_Z (Z_S (A + A)) hSF_Z
  have h4 := N_bound_upper_1 A hF h_sidon
  have h5 := N_bound_lower_2 A hF h_sidon
  have h6 := N_bound_upper_3 A hF h_sidon
  have h7 := D_set_card A hF
  have h8 := S_card A hF h_sidon
  have hI1 := num_isolated_Z_rel A
  have hN1 : N_k_Z (Z_S (A + A)) (1 : ℤ) = N_k_N (A + A) 1 := N_k_Z_rel_1 A
  have hN2 : N_k_Z (Z_S (A + A)) (2 : ℤ) = N_k_N (A + A) 2 := N_k_Z_rel_2 A
  have hN3 : N_k_Z (Z_S (A + A)) (3 : ℤ) = N_k_N (A + A) 3 := N_k_Z_rel_3 A
  have hC := Z_S_card A
  have hn_sq : A.ncard * A.ncard = n * n := by subst h_card; rfl
  omega

lemma exists_sidon_set_n (n : ℕ) : ∃ A : Set ℕ, A.ncard = n ∧ IsSidon A := by
  delta IsSidon
  use .image (2 ^ ·) ( Finset.range n),mod_cast by simp_all [ Finset.card_image_of_injective, (@2).pow_right_injective],Set.forall_mem_image.2 fun and x =>Set.forall_mem_image.2 ?_
  use fun a s y⟨A, B, _⟩z⟨D,E, _⟩h=> if I:and<a then if I: A<D then(? _)else(? _)else if I: A<D then(? _)else(? _)
  · use absurd ((2).pow_lt_pow_right · I) (absurd ((2).pow_lt_pow_right · ↑‹and<a›) ∘by (fin_omega))
  · rcases lt_trichotomy A a with S |rfl | S
    · exact absurd D.two_pow_pos fun and' => absurd ((2).pow_le_pow_right · S) ( (by fin_omega ∘(2).pow_le_pow_right (by decide)) (‹and<a›) )
    · fin_omega
    · match(2).pow_le_pow_right (by decide) S,(2).pow_le_pow_right (by decide) ( (not_lt.1 I).lt_of_ne fun and=> by aesop), and.two_pow_pos with|_, _A, B=>fin_omega
  · rcases lt_trichotomy and D with a|rfl|c
    · refine absurd (h.symm▸Nat.lt_add_of_pos_left (by positivity)) fun and=> absurd ((2).pow_le_pow_right · I) ( (by fin_omega ∘(2).pow_le_pow_right (by decide)) ( a))
    · fin_omega
    · simp_all [le_antisymm (not_lt.1 ↑(mt ((2).pow_le_pow_right ↑ _) fun and=> absurd A.two_pow_pos ((by fin_omega ∘(2).pow_le_pow_right (by decide)) c))) (by valid: a ≤and)]
  · match (by bound:2^D≤2^A∧2^and≥2^a) with| ⟨a, _⟩=>fin_omega

lemma f_lower_bound_div (n : ℕ) : f n ≥ (n * n - 100 * n - 16) / 16 := by
  have hn : n = 0 ∨ n > 0 := Nat.eq_zero_or_pos n
  cases hn with
  | inr h_pos =>
    have ⟨A, hA⟩ := exists_sidon_set_n n
    have h_nonempty : Nonempty {A : Set ℕ | A.ncard = n ∧ IsSidon A} := ⟨⟨A, hA⟩⟩
    unfold f
    apply le_ciInf
    intro A_sub
    have h_b := num_isolated_lower_bound n h_pos A_sub.val A_sub.property.1 A_sub.property.2
    unfold num_isolated at h_b
    apply Nat.div_le_of_le_mul
    omega
  | inl h_zero =>
    subst h_zero
    omega

lemma tendsto_bound : Tendsto (fun n : ℕ => (n * n - 100 * n - 16) / 16) atTop atTop := by
  exact (Filter.tendsto_atTop.2 fun and=>by filter_upwards[Filter.mem_atTop 101,Filter.mem_atTop (and*16+16)] with a _ _ using (by valid ∘Nat.mul_le_mul_right a) (‹101 ≤ a›))

lemma tendsto_f : Tendsto f atTop atTop := by
  have h_le : ∀ᶠ n in atTop, (n * n - 100 * n - 16) / 16 ≤ f n := by
    filter_upwards [eventually_ge_atTop 1000] with n hn
    exact f_lower_bound_div n
  exact tendsto_atTop_mono' atTop h_le tendsto_bound


/-- Must `lim f n = ∞`? -/
@[category research solved, AMS 5]
theorem erdos_152 : answer(True) ↔ Tendsto f atTop atTop := by
  constructor
  · intro _
    exact tendsto_f
  · intro _
    trivial

/-- `f n ≫ n ^ 2`, i.e. $f(n) = \Omega(n^2)$.
This follows from the bound $f(n) \geq (n^2 - 100n - 16)/16$. -/
@[category research solved, AMS 5]
theorem erdos_152.variants.square : answer(True) ↔
    (fun n => f n : ℕ → ℝ) ≫ (fun n => n ^ 2 : ℕ → ℝ) := by
  constructor
  · intro _
    show (fun n : ℕ => (n : ℝ) ^ 2) =O[atTop] (fun n : ℕ => (f n : ℝ))
    rw [Asymptotics.isBigO_iff]
    refine ⟨64, ?_⟩
    filter_upwards [eventually_ge_atTop 200] with n hn
    rw [Real.norm_of_nonneg (sq_nonneg _), sq, Real.norm_of_nonneg (Nat.cast_nonneg _)]
    have h := f_lower_bound_div n
    have h_sq : 200 * n ≤ n * n := Nat.mul_le_mul_right n hn
    have h_dm := Nat.div_add_mod (n * n - 100 * n - 16) 16
    have h_ml := Nat.mod_lt (n * n - 100 * n - 16) (show (0 : ℕ) < 16 by omega)
    have : n * n ≤ 64 * f n := by omega
    exact_mod_cast this
  · intro _; trivial

end Erdos152
