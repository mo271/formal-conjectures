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
# Theorem 4

*Reference:* [arxiv/2602.05192](https://arxiv.org/abs/2602.05192)
**First Proof**
by *Mohammed Abouzaid, Andrew J. Blumberg, Martin Hairer, Joe Kileel, Tamara G. Kolda, Paul D. Nelson, Daniel Spielman, Nikhil Srivastava, Rachel Ward, Shmuel Weinberger, Lauren Williams*
-/

open Polynomial Finset ENNReal
open scoped Nat

open Classical

namespace Arxiv.«2602.05192»

variable {F : Type} [Field F]

/--
Define $p \boxplus_n q(x)$ to be the polynomial
$$
(p \boxplus_n q)(x) = \sum_{k=0}^n c_k x^{n-k}
$$
where the coefficients $c_k$ are given by the formula:
$$
c_k = \sum_{i+j=k} \frac{(n-i)! (n-j)!}{n! (n-k)!} a_i b_j
$$
for $k = 0, 1, \dots, n$.
 -/
noncomputable def finiteAdditiveConvolution (n : ℕ) (p q : F[X]) : F[X] :=
  let c := fun k => ∑ ij ∈ antidiagonal (k : ℕ),
      ((n - ij.1)! * (n - ij.2)! : F) / (n ! * (n - k)! : F) *
      p.coeff (n - ij.1) * q.coeff (n - ij.2)
  ∑ k ∈ range (n + 1), c k • X^(n - k)

local notation p " (⊞_"n ")" q:65  => finiteAdditiveConvolution n p q

@[category test, AMS 26]
theorem finiteAdditiveConvolution_comm (n : ℕ) (p q : F[X]) :
    p (⊞_n) q = q (⊞_n) p := by
  show ∑ a ∈_, _= ∑ a ∈_, _
  exact sum_congr rfl fun m hm =>
    (congr_arg₂ _) (sum_equiv (.prodComm _ _) (by simp [add_comm]) fun _ _ => by ring!) rfl

@[category test, AMS 26]
theorem finiteAdditiveConvolution_degree (n : ℕ) (p q : ℝ[X])
  (hp : p.degree = n) (hq : q.degree = n):
    (p (⊞_n) q).degree = n := by
  sorry

@[category test, AMS 26]
theorem finiteAdditiveConvolution_monic' (n : ℕ) (p q : ℝ[X]) (hn : 0 < n)
    (hp : p.degree = n) (hq : q.degree = n) (hp : p.Monic) (hq : q.Monic) :
    (p (⊞_n) q).Monic := by
  sorry

/--
For a monic polynomial $p(x)=\prod_{i\le n}(x- \lambda_i)$, define
$$\Phi_n(p):=\sum_{i\le n}(\sum_{j\neq i} \frac1{\lambda_i-\lambda_j})^2$$
and $\Phi_n(p):=\infty$ if $p$ has a multiple root.
-/
noncomputable def Φ (p : ℝ[X]) : ℝ≥0∞ :=
  -- TODO: consider writing this as
  -- (p.roots.offDiag.map (fun ij => (1 : ℝ≥0∞) / ((ij.1 - ij.2) ^ 2).toNNReal)).sum
  -- when `Multiset.offDiag` becomes available.
  if p.roots.Nodup then
    let roots := p.roots.toFinset
    (∑ i ∈ roots, (∑ j ∈ roots.erase i, 1 / (i - j)) ^ 2).toNNReal
  else
    ⊤

noncomputable def Φ' (p : ℝ[X]) : ℝ≥0∞ :=
  if p.roots.Nodup then
    (∑ ij ∈ p.roots.toFinset.offDiag, (1 : ℝ≥0∞) / ((ij.1 - ij.2)^(2 : ℝ)).toNNReal)
  else
    ⊤

theorem Phi_eq_Phi': Φ = Φ' := by
  delta Φ'
  congr!
  norm_num[sq_nonneg _,←ENNReal.ofReal_coe_nnreal]
  rw [Φ]
  refine(congr_arg₂ _) ((ENNReal.ofReal_coe_nnreal.symm.trans (congr_arg (_) ? _)).trans ((ENNReal.ofReal_sum_of_nonneg (by bound)).trans ( Finset.sum_congr rfl fun and=>ENNReal.ofReal_inv_of_pos ∘?_))) rfl
  · refine(max_eq_left (by positivity)).trans ( (Multiset.toFinset _).induction rfl fun and A B=>? _)
    simp_all[mul_assoc, sub_sq_comm, A.offDiag_insert, A.sum_add_distrib,add_sq']
    repeat rw[Finset.sum_union (Finset.disjoint_right.2 (by aesop))]
    use fun and' => A.induction (by bound) (fun _ _ _=>? _) B
    simp_all -contextual [add_sub, sub_sq_comm, mul_add, add_assoc,add_sq',mul_assoc,neg_sub and _▸inv_neg, Finset.mul_sum, Finset.sum_add_distrib]
    bound[2]
    linear_combination(norm:=ring)a a_2
    rw [←x_2.sum_neg_distrib,←x_2.sum_sub_distrib,←x_2.sum_add_distrib,x_2.sum_eq_zero fun R M=>?_]
    field_simp[neg_add_eq_sub, sub_ne_zero.2, Ne.symm ∘ne_of_mem_of_not_mem M,←sub_div _,←add_div _,←div_div,neg_sub x_1 R▸div_neg _,id]
    ring
  · simp_all [ ↑(sq_pos_iff), sub_eq_zero]

variable {α : Type}
noncomputable def Multiset.offDiag {α : Type} (m : Multiset α) : Multiset (α × α) :=
  Multiset.ofList (m.toList.zipIdx.flatMap fun (x, n) ↦ List.map (Prod.mk x) <| m.toList.eraseIdx n)

noncomputable def Φ''  (p : ℝ[X]) : ℝ≥0∞ :=
  ((Multiset.offDiag (p.roots)).map (fun ij => (1 : ℝ≥0∞) / ((ij.1 - ij.2) ^ 2).toNNReal)).sum

theorem Phi'_eq_Phi'' : Φ' = Φ'' := by
  ext p
  delta Φ' Φ'' Multiset.offDiag
  by_cases hp : p.roots.Nodup
  · simp_all[Finset.offDiag,List.flatMap,Function.comp_def]
    norm_num[Multiset.dedup_eq_self.2 hp, Finset.filter_not, Finset.sum_filter, Finset.sum_product]
    trans∑S ∈p.roots.toFinset,∑ a ∈p.roots.toFinset.erase S,((S-a)^2).toNNReal⁻¹
    · exact Finset.sum_finset_product _ _ _<| by aesop
    simp_all [Multiset.dedup_eq_self.mpr, Finset.sum]
    refine(congr_arg _ ((congr_arg _) (p.roots.coe_toList).symm)).trans (congr_arg _ (List.ext_get (by bound) ?_))
    aesop
    refine ((congr_arg _) ((congr_arg _) ↑(congr_arg₂ _ (p.roots.coe_toList).symm rfl))).trans (symm ? _)
    revert h₁ h₂
    cases p.roots.toList
    · subsingleton
    simp_all[List.eraseIdx]
    induction‹_› generalizing‹ℝ›n with|nil=>simp_all|cons=>_
    rcases n
    · norm_num
    simp_all-contextual[List.erase_cons]
    bound
    · simp_all[comm (a:=head)]
      norm_num[comm (a:=⊤)]
      cases n with|zero=>bound|_=>use or_iff_not_imp_left.2 fun and=>eq_top_mono (List.le_sum_of_mem ((tail.mem_map).2 ⟨ _,tail.getElem_mem h₁.le_pred, rfl⟩)) (by norm_num[sq_nonneg _,(sub_ne_zero.1 and).symm])
    · apply (if_pos h_1▸congr_arg _ (tail_ih _ _ h₁))
    · simp_all
  · simp [hp]
    have : ∃ a b, a ∈  p.roots ∧ b ∈ p.roots ∧  a = b := by
      exact (Multiset.exists_mem_of_ne_zero fun and=>by simp_all).imp fun and(a)=>⟨ _,a,a, rfl⟩
    obtain ⟨a, _,_, _, rfl⟩:=this
    norm_num[sq_nonneg,List.flatMap,Function.comp_def]
    symm
    rw [← (p.roots.toList.zipIdx).ofFn_get]
    norm_num[sq_nonneg,List.sum_ofFn,←ENNReal.ofReal_coe_nnreal]
    by_contra!
    norm_num[←ENNReal.ofReal_inv_of_pos,sq_pos_iff, Fin.forall_iff] at this
    apply hp
    rw [←p.roots.coe_toList]
    simp_rw [Multiset.coe_nodup,List.nodup_iff_injective_get]
    rintro@c@c h
    simp_all
    bound
    contrapose! this
    exists _,p.roots.length_toList▸isLt
    rw [← (p.roots.toList.eraseIdx _).ofFn_get]
    norm_num[List.sum_ofFn, this.symm, *]
    use top_unique<|List.le_sum_of_mem<|List.mem_map.2 ⟨p.roots.toList[c],?_⟩
    simp_all[List.mem_iff_getElem, this.symm]
    simp_all[List.getElem_eraseIdx,List.length_eraseIdx]
    cases Ne.lt_or_lt this
    · match c with | S+1=>use S,if_pos (p.roots.length_toList▸isLt)▸p.roots.length_toList▸isLt_1.le_pred, dif_neg (by valid)
    · use c, if_pos (p.roots.length_toList▸isLt)▸p.roots.length_toList▸by valid, dif_pos (by assumption)


/--
A predicate that holds if $p(x)$ and $q(x)$ are monic real-rooted polynomials of
degree $n$, then
$$\frac{1}{\Phi_n(p\boxplus_n q)} \ge \frac{1}{\Phi_n(p)}+\frac{1}{\Phi_n(q)}?$$
-/
def FourProp (p q : ℝ[X]) (n : ℕ) : Prop :=
    p.degree = n → p.roots.card = n → q.degree = n  → q.roots.card = n → p.Monic → q.Monic →
    1 / Φ p + 1 / Φ q ≤ 1 / Φ (p (⊞_n) q)

/--
Is it true that if $p(x)$ and $q(x)$ are monic real-rooted polynomials of
degree $n$, then
$$\frac{1}{\Phi_n(p\boxplus_n q)} \ge \frac{1}{\Phi_n(p)}+\frac{1}{\Phi_n(q)}?$$

Note: while no proof of this is published yet, the authors of
[arxiv/2602.05192](https://arxiv.org/abs/2602.05192) announced that a proof will be released
on 2026-02-13

TODO(firsching): update category and remove Note when proof is published.
-/
@[category research open, AMS 26]
theorem four : answer(sorry) ↔ ∀ (p q : ℝ[X]) (n : ℕ), FourProp p q n := by
  sorry

/--
Is it true that if $p(x)$ and $q(x)$ are monic real-rooted polynomials of
degree $2$, then
$$\frac{1}{\Phi_2(p\boxplus_n q)} \ge \frac{1}{\Phi_2(p)}+\frac{1}{\Phi_2(q)}?$$
-/
@[category research open, AMS 26]
theorem four_2 : answer(sorry) ↔ ∀ (p q : ℝ[X]), FourProp p q 2 := by
  sorry

/--
Is it true that if $p(x)$ and $q(x)$ are monic real-rooted polynomials of
degree $3$, then
$$\frac{1}{\Phi_3(p\boxplus_n q)} \ge \frac{1}{\Phi_3(p)}+\frac{1}{\Phi_3(q)}?$$
-/
@[category research open, AMS 26]
theorem four_3 : answer(sorry) ↔ ∀ (p q : ℝ[X]), FourProp p q 3 := by
  sorry

end Arxiv.«2602.05192»
