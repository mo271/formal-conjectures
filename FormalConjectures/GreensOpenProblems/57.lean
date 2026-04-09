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
# Ben Green's Open Problem 57

*Reference:* [Ben Green's Open Problem 57](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.8 Problem 57)
-/

namespace Green57

open scoped Pointwise

noncomputable section

variable (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Uniform average over pairs `(x₁, x₂)` in `G × G`, with the third variable determined by
the relation `x₁ + x₂ + x₃ = g`. -/
def tripleKernel (f₁ f₂ f₃ : G × G → ℝ) : G → ℝ := fun g =>
  let cardG : ℝ := Fintype.card G
  (cardG ^ 2)⁻¹ *
      ∑ x₁ : G, ∑ x₂ : G,
        f₁ (x₂, g - x₁ - x₂) * f₂ (x₁, g - x₁ - x₂) * f₃ (x₁, x₂)

/-- The generating family of functions for `Φ(G)`. -/
def baseΦ : Set (G → ℝ) :=
  {φ | ∃ f₁ f₂ f₃ : G × G → ℝ,
    (∀ p, |f₁ p| ≤ 1) ∧ (∀ p, |f₂ p| ≤ 1) ∧ (∀ p, |f₃ p| ≤ 1) ∧
    φ = tripleKernel G f₁ f₂ f₃}

/-- The generating family of functions for `Φ′(G)`, where the third kernel depends only on
`x₁ + x₂`. -/
def baseΦ' : Set (G → ℝ) :=
  {φ | ∃ f₁ f₂ : G × G → ℝ, ∃ h : G → ℝ,
    (∀ p, |f₁ p| ≤ 1) ∧ (∀ p, |f₂ p| ≤ 1) ∧ (∀ x, |h x| ≤ 1) ∧
    φ = tripleKernel G f₁ f₂ (fun p => h (p.1 + p.2))}

/-- The space `Φ(G)` of convex combinations of kernels from `baseΦ`. -/
def Φ : Set (G → ℝ) :=
  convexHull ℝ (baseΦ G)

/-- The restricted space `Φ′(G)` of convex combinations of kernels from `baseΦ'`. -/
def Φ' : Set (G → ℝ) :=
  convexHull ℝ (baseΦ' G)


def c_int (g : ZMod 3) : ℤ :=
  if g = 0 then 1 else if g = 1 then 1 else -1

def f1_int (p : ZMod 3 × ZMod 3) : ℤ :=
  let x := p.1.val; let y := p.2.val
  let l : List ℤ := [1, 1, 1, 1, 1, -1, 1, -1, 1]
  l.getD (x * 3 + y) 0

def f2_int (p : ZMod 3 × ZMod 3) : ℤ :=
  let x := p.1.val; let y := p.2.val
  let l : List ℤ := [-1, -1, 1, -1, 1, -1, 1, 1, 1]
  l.getD (x * 3 + y) 0

def f3_int (p : ZMod 3 × ZMod 3) : ℤ :=
  let x1 := p.1.val; let x2 := p.2.val
  let z0 := c_int (x1 + x2 + 0) * f1_int (x2, 0) * f2_int (x1, 0)
  let z1 := c_int (x1 + x2 + 1) * f1_int (x2, 1) * f2_int (x1, 1)
  let z2 := c_int (x1 + x2 + 2) * f1_int (x2, 2) * f2_int (x1, 2)
  if z0 + z1 + z2 ≥ 0 then 1 else -1

def c_fun (g : ZMod 3) : ℝ := c_int g
def f1_val (p : ZMod 3 × ZMod 3) : ℝ := f1_int p
def f2_val (p : ZMod 3 × ZMod 3) : ℝ := f2_int p
def f3_val (p : ZMod 3 × ZMod 3) : ℝ := f3_int p

def eval_functional (phi : ZMod 3 → ℝ) : ℝ := ∑ g : ZMod 3, c_fun g * phi g
def phi_witness : ZMod 3 → ℝ := tripleKernel (ZMod 3) f1_val f2_val f3_val

lemma f1_int_bound (p : ZMod 3 × ZMod 3) : |f1_int p| ≤ 1 := by revert p; decide
lemma f2_int_bound (p : ZMod 3 × ZMod 3) : |f2_int p| ≤ 1 := by revert p; decide
lemma f3_int_bound (p : ZMod 3 × ZMod 3) : |f3_int p| ≤ 1 := by revert p; decide

lemma phi_witness_in_baseΦ : phi_witness ∈ baseΦ (ZMod 3) := by
  dsimp [baseΦ, phi_witness]; use f1_val, f2_val, f3_val; refine ⟨?_, ?_, ?_, rfl⟩
  · intro p; dsimp [f1_val]; exact_mod_cast f1_int_bound p
  · intro p; dsimp [f2_val]; exact_mod_cast f2_int_bound p
  · intro p; dsimp [f3_val]; exact_mod_cast f3_int_bound p

def eval_functional_int (phi : ZMod 3 → ℤ) : ℤ := ∑ g : ZMod 3, c_int g * phi g
def tripleKernel_int (f1 f2 f3 : ZMod 3 × ZMod 3 → ℤ) : ZMod 3 → ℤ := fun g =>
  ∑ x1 : ZMod 3, ∑ x2 : ZMod 3, f1 (x2, g - x1 - x2) * f2 (x1, g - x1 - x2) * f3 (x1, x2)
def phi_witness_int : ZMod 3 → ℤ := tripleKernel_int f1_int f2_int f3_int

lemma phi_witness_int_eval : eval_functional_int phi_witness_int = 21 := rfl

lemma phi_witness_eval : eval_functional phi_witness = 21 / 9 := by show(id _) = _
                                                                    show∑x,(id _)*(id _) = _
                                                                    show∑i,_*(id (id _)) = ( _)
                                                                    norm_num+decide only[Green/em',id, ZMod.card, mul_assoc, mul_left_comm ((_ : ℤ):ℚ), ← Finset.mul_sum, Fin.sum_univ_three, Fin.neg_def]
                                                                    use show∑x,_*(_*∑A,∑B,id _*((id _)*id _)) =7/3 from(Fintype.sum_congr _ _ fun and=>by rw [ Fintype.sum_congr _ _ fun and=> Fintype.sum_congr _ _ fun and=> by aesop]).trans (? _)
                                                                    exact ( Fintype.sum_congr _ _ fun and=>by rw [mul_comm_div, one_mul,mul_div]).trans ( (Finset.sum_div _ _ _).symm.trans ((div_eq_div_iff (by simp_all) three_ne_zero).2 (by norm_cast)))

lemma abs_eq_sign_mul (c : ℝ) : ∃ t : ℝ, (t = 1 ∨ t = -1) ∧ |c| = t * c := by
  rcases le_total 0 c with hc | hc
  · exact ⟨1, Or.inl rfl, by linarith [abs_of_nonneg hc]⟩
  · exact ⟨-1, Or.inr rfl, by linarith [abs_of_nonpos hc]⟩

lemma abs_sum_le_iff (A B C M : ℝ) :
  |A| + |B| + |C| ≤ M ↔ ∀ s0 s1 s2 : ℝ, (s0=1 ∨ s0=-1) → (s1=1 ∨ s1=-1) → (s2=1 ∨ s2=-1) →
  s0*A + s1*B + s2*C ≤ M := by
  constructor
  · intro h s0 s1 s2 hs0 hs1 hs2
    have hA : s0 * A ≤ |A| := by
      rcases hs0 with rfl|rfl
      · linarith [le_abs_self A]
      · linarith [neg_le_abs A]
    have hB : s1 * B ≤ |B| := by
      rcases hs1 with rfl|rfl
      · linarith [le_abs_self B]
      · linarith [neg_le_abs B]
    have hC : s2 * C ≤ |C| := by
      rcases hs2 with rfl|rfl
      · linarith [le_abs_self C]
      · linarith [neg_le_abs C]
    linarith
  · intro h
    rcases abs_eq_sign_mul A with ⟨s0, hs0, eq0⟩
    rcases abs_eq_sign_mul B with ⟨s1, hs1, eq1⟩
    rcases abs_eq_sign_mul C with ⟨s2, hs2, eq2⟩
    rw [eq0, eq1, eq2]
    exact h s0 s1 s2 hs0 hs1 hs2

lemma solve_C_bound (w0 w1 w2 : ℝ) (hw0 : w0=1 ∨ w0=-1) (hw1 : w1=1 ∨ w1=-1) (hw2 : w2=1 ∨ w2=-1)
  (v0 v1 v2 : ℝ) (h0 : |v0|≤1) (h1 : |v1|≤1) (h2 : |v2|≤1) :
  |w0*v0 + w1*v1 + w2*v2| + |w1*v0 + w2*v1 + w0*v2| + |w2*v0 + w0*v1 + w1*v2| ≤
  if w0 = w1 ∧ w1 = w2 then (9:ℝ) else 5 := by
  have hv0_le : v0 ≤ 1 := (abs_le.1 h0).2
  have hv0_ge : -1 ≤ v0 := (abs_le.1 h0).1
  have hv1_le : v1 ≤ 1 := (abs_le.1 h1).2
  have hv1_ge : -1 ≤ v1 := (abs_le.1 h1).1
  have hv2_le : v2 ≤ 1 := (abs_le.1 h2).2
  have hv2_ge : -1 ≤ v2 := (abs_le.1 h2).1
  rcases hw0 with rfl|rfl <;> rcases hw1 with rfl|rfl <;> rcases hw2 with rfl|rfl
  all_goals {
    norm_num
    rw [abs_sum_le_iff]
    intro s0 s1 s2 hs0 hs1 hs2
    rcases hs0 with rfl|rfl <;> rcases hs1 with rfl|rfl <;> rcases hs2 with rfl|rfl <;>
    linarith
  }

lemma bound_all_S (S0 S1 S2 : ℝ) (hS0 : S0=1 ∨ S0=-1) (hS1 : S1=1 ∨ S1=-1) (hS2 : S2=1 ∨ S2=-1)
  (v0_0 v1_0 v2_0 v0_1 v1_1 v2_1 v0_2 v1_2 v2_2 : ℝ)
  (hv00: |v0_0|≤1) (hv10: |v1_0|≤1) (hv20: |v2_0|≤1)
  (hv01: |v0_1|≤1) (hv11: |v1_1|≤1) (hv21: |v2_1|≤1)
  (hv02: |v0_2|≤1) (hv12: |v1_2|≤1) (hv22: |v2_2|≤1) :
  (|S0*v0_0 + S1*v1_0 + (-S2)*v2_0| + |S1*v0_0 + (-S2)*v1_0 + S0*v2_0| + |(-S2)*v0_0 + S0*v1_0 + S1*v2_0|) +
  (|S0*v0_1 + (-S1)*v1_1 + S2*v2_1| + |(-S1)*v0_1 + S2*v1_1 + S0*v2_1| + |S2*v0_1 + S0*v1_1 + (-S1)*v2_1|) +
  (|(-S0)*v0_2 + S1*v1_2 + S2*v2_2| + |S1*v0_2 + S2*v1_2 + (-S0)*v2_2| + |S2*v0_2 + (-S0)*v1_2 + S1*v2_2|) ≤ 19 := by
  have hS2_neg : -S2 = 1 ∨ -S2 = -1 := by rcases hS2 with rfl|rfl <;> norm_num
  have hS1_neg : -S1 = 1 ∨ -S1 = -1 := by rcases hS1 with rfl|rfl <;> norm_num
  have hS0_neg : -S0 = 1 ∨ -S0 = -1 := by rcases hS0 with rfl|rfl <;> norm_num
  have H0 := solve_C_bound S0 S1 (-S2) hS0 hS1 hS2_neg v0_0 v1_0 v2_0 hv00 hv10 hv20
  have H1 := solve_C_bound S0 (-S1) S2 hS0 hS1_neg hS2 v0_1 v1_1 v2_1 hv01 hv11 hv21
  have H2 := solve_C_bound (-S0) S1 S2 hS0_neg hS1 hS2 v0_2 v1_2 v2_2 hv02 hv12 hv22
  rcases hS0 with rfl|rfl <;> rcases hS1 with rfl|rfl <;> rcases hS2 with rfl|rfl
  all_goals {
    conv at H0 => rhs; norm_num
    conv at H1 => rhs; norm_num
    conv at H2 => rhs; norm_num
    linarith
  }

lemma bil_le_abs (u c : ℝ) (hu : |u| ≤ 1) : u * c ≤ |c| := by
  have h1 : u ≤ 1 := (abs_le.1 hu).2
  have h2 : -1 ≤ u := (abs_le.1 hu).1
  rcases le_total 0 c with hc | hc
  · have : u * c ≤ 1 * c := mul_le_mul_of_nonneg_right h1 hc
    linarith [le_abs_self c]
  · have : u * c ≤ (-1) * c := mul_le_mul_of_nonpos_right h2 hc
    linarith [neg_le_abs c]

lemma sum_bilinear_le_C (w0 w1 w2 : ℝ) (u0 u1 u2 v0 v1 v2 : ℝ) (hu0 : |u0| ≤ 1) (hu1 : |u1| ≤ 1) (hu2 : |u2| ≤ 1) :
  u0 * (w0*v0 + w1*v1 + w2*v2) + u1 * (w1*v0 + w2*v1 + w0*v2) + u2 * (w2*v0 + w0*v1 + w1*v2) ≤
  |w0*v0 + w1*v1 + w2*v2| + |w1*v0 + w2*v1 + w0*v2| + |w2*v0 + w0*v1 + w1*v2| := by
  have h0 := bil_le_abs u0 (w0*v0 + w1*v1 + w2*v2) hu0
  have h1 := bil_le_abs u1 (w1*v0 + w2*v1 + w0*v2) hu1
  have h2 := bil_le_abs u2 (w2*v0 + w0*v1 + w1*v2) hu2
  linarith

lemma sum_zmod3 (f : ZMod 3 → ℝ) : ∑ x : ZMod 3, f x = f 0 + f 1 + f 2 := by apply Fin.sum_univ_three

def W_z (f1 f2 : ZMod 3 × ZMod 3 → ℝ) (z s : ZMod 3) : ℝ :=
  ∑ x : ZMod 3, f1 (s - x, z) * f2 (x, z)

def A_val (f1 f2 : ZMod 3 × ZMod 3 → ℝ) (s : ZMod 3) : ℝ :=
  ∑ z : ZMod 3, c_fun (s + z) * W_z f1 f2 z s

lemma Z3_calc1 : (0 - 1 : ZMod 3) = 2 := by decide
lemma Z3_calc2 : (0 - 2 : ZMod 3) = 1 := by decide
lemma Z3_calc3 : (1 - 0 : ZMod 3) = 1 := by decide
lemma Z3_calc4 : (1 - 2 : ZMod 3) = 2 := by decide
lemma Z3_calc5 : (2 - 0 : ZMod 3) = 2 := by decide
lemma Z3_calc6 : (2 - 1 : ZMod 3) = 1 := by decide
lemma Z3_calc7 : (0 - 0 : ZMod 3) = 0 := by decide
lemma Z3_calc8 : (1 - 1 : ZMod 3) = 0 := by decide
lemma Z3_calc9 : (2 - 2 : ZMod 3) = 0 := by decide

lemma Z3_add00 : (0 + 0 : ZMod 3) = 0 := by decide
lemma Z3_add01 : (0 + 1 : ZMod 3) = 1 := by decide
lemma Z3_add02 : (0 + 2 : ZMod 3) = 2 := by decide
lemma Z3_add10 : (1 + 0 : ZMod 3) = 1 := by decide
lemma Z3_add11 : (1 + 1 : ZMod 3) = 2 := by decide
lemma Z3_add12 : (1 + 2 : ZMod 3) = 0 := by decide
lemma Z3_add20 : (2 + 0 : ZMod 3) = 2 := by decide
lemma Z3_add21 : (2 + 1 : ZMod 3) = 0 := by decide
lemma Z3_add22 : (2 + 2 : ZMod 3) = 1 := by decide

lemma c_fun_00 : c_fun (0 + 0) = 1 := by dsimp [c_fun]; exact_mod_cast (rfl : c_int (0 + 0) = 1)
lemma c_fun_01 : c_fun (0 + 1) = 1 := by dsimp [c_fun]; exact_mod_cast (rfl : c_int (0 + 1) = 1)
lemma c_fun_02 : c_fun (0 + 2) = -1 := by dsimp [c_fun]; exact_mod_cast (rfl : c_int (0 + 2) = -1)
lemma c_fun_10 : c_fun (1 + 0) = 1 := by dsimp [c_fun]; exact_mod_cast (rfl : c_int (1 + 0) = 1)
lemma c_fun_11 : c_fun (1 + 1) = -1 := by dsimp [c_fun]; exact_mod_cast (rfl : c_int (1 + 1) = -1)
lemma c_fun_12 : c_fun (1 + 2) = 1 := by dsimp [c_fun]; exact_mod_cast (rfl : c_int (1 + 2) = 1)
lemma c_fun_20 : c_fun (2 + 0) = -1 := by dsimp [c_fun]; exact_mod_cast (rfl : c_int (2 + 0) = -1)
lemma c_fun_21 : c_fun (2 + 1) = 1 := by dsimp [c_fun]; exact_mod_cast (rfl : c_int (2 + 1) = 1)
lemma c_fun_22 : c_fun (2 + 2) = 1 := by dsimp [c_fun]; exact_mod_cast (rfl : c_int (2 + 2) = 1)

lemma S_A_bound (f1 f2 : ZMod 3 × ZMod 3 → ℝ) (h1 : ∀ p, |f1 p| ≤ 1) (h2 : ∀ p, |f2 p| ≤ 1)
  (S0 S1 S2 : ℝ) (hS0 : S0=1 ∨ S0=-1) (hS1 : S1=1 ∨ S1=-1) (hS2 : S2=1 ∨ S2=-1) :
  S0 * A_val f1 f2 0 + S1 * A_val f1 f2 1 + S2 * A_val f1 f2 2 ≤ 19 := by
  have H0 := sum_bilinear_le_C S0 S1 (-S2) (f2 (0,0)) (f2 (1,0)) (f2 (2,0)) (f1 (0,0)) (f1 (1,0)) (f1 (2,0)) (h2 _) (h2 _) (h2 _)
  have H1 := sum_bilinear_le_C S0 (-S1) S2 (f2 (0,1)) (f2 (1,1)) (f2 (2,1)) (f1 (0,1)) (f1 (1,1)) (f1 (2,1)) (h2 _) (h2 _) (h2 _)
  have H2 := sum_bilinear_le_C (-S0) S1 S2 (f2 (0,2)) (f2 (1,2)) (f2 (2,2)) (f1 (0,2)) (f1 (1,2)) (f1 (2,2)) (h2 _) (h2 _) (h2 _)
  have H_all := bound_all_S S0 S1 S2 hS0 hS1 hS2 (f1 (0,0)) (f1 (1,0)) (f1 (2,0)) (f1 (0,1)) (f1 (1,1)) (f1 (2,1)) (f1 (0,2)) (f1 (1,2)) (f1 (2,2)) (h1 _) (h1 _) (h1 _) (h1 _) (h1 _) (h1 _) (h1 _) (h1 _) (h1 _)
  have h_eq : S0 * A_val f1 f2 0 + S1 * A_val f1 f2 1 + S2 * A_val f1 f2 2 =
    (f2 (0,0) * (S0 * f1 (0,0) + S1 * f1 (1,0) + -S2 * f1 (2,0)) +
     f2 (1,0) * (S1 * f1 (0,0) + -S2 * f1 (1,0) + S0 * f1 (2,0)) +
     f2 (2,0) * (-S2 * f1 (0,0) + S0 * f1 (1,0) + S1 * f1 (2,0))) +
    (f2 (0,1) * (S0 * f1 (0,1) + -S1 * f1 (1,1) + S2 * f1 (2,1)) +
     f2 (1,1) * (-S1 * f1 (0,1) + S2 * f1 (1,1) + S0 * f1 (2,1)) +
     f2 (2,1) * (S2 * f1 (0,1) + S0 * f1 (1,1) + -S1 * f1 (2,1))) +
    (f2 (0,2) * (-S0 * f1 (0,2) + S1 * f1 (1,2) + S2 * f1 (2,2)) +
     f2 (1,2) * (S1 * f1 (0,2) + S2 * f1 (1,2) + -S0 * f1 (2,2)) +
     f2 (2,2) * (S2 * f1 (0,2) + -S0 * f1 (1,2) + S1 * f1 (2,2))) := by
    dsimp [A_val, W_z]
    repeat rw [sum_zmod3]
    rw [c_fun_00, c_fun_01, c_fun_02, c_fun_10, c_fun_11, c_fun_12, c_fun_20, c_fun_21, c_fun_22]
    rw [Z3_calc1, Z3_calc2, Z3_calc3, Z3_calc4, Z3_calc5, Z3_calc6, Z3_calc7, Z3_calc8, Z3_calc9]
    ring
  rw [h_eq]
  exact le_trans (add_le_add (add_le_add H0 H1) H2) H_all

lemma base_phi_prime_le_19_9 (phi : ZMod 3 → ℝ) (hphi : phi ∈ baseΦ' (ZMod 3)) :
  eval_functional phi ≤ 19 / 9 := by
  rcases hphi with ⟨f1, f2, h, h1, h2, hh, rfl⟩
  have h_eq : eval_functional (tripleKernel (ZMod 3) f1 f2 fun p ↦ h (p.1 + p.2)) =
    (1/9 : ℝ) * (h 0 * A_val f1 f2 0 + h 1 * A_val f1 f2 1 + h 2 * A_val f1 f2 2) := by show∑_, _ = _ * (_*(∑_, _)+_*(∑_, _)+ h (2) *∑_, _)
                                                                                        show∑_, _*id _ = _*(_*∑_, _*(id _) +_*∑_, _*(id _) +_*∑_, _*id _)
                                                                                        push_cast[id,ZMod, sub_sub, zero_add, one_div, Fin.sum_univ_three, Fintype.card_fin, Finset.mul_sum]
                                                                                        ring
  rw [h_eq]
  rcases abs_eq_sign_mul (A_val f1 f2 0) with ⟨S0, hS0, eq0⟩
  rcases abs_eq_sign_mul (A_val f1 f2 1) with ⟨S1, hS1, eq1⟩
  rcases abs_eq_sign_mul (A_val f1 f2 2) with ⟨S2, hS2, eq2⟩
  have H_bound := S_A_bound f1 f2 h1 h2 S0 S1 S2 hS0 hS1 hS2
  have h_h0 := bil_le_abs (h 0) (A_val f1 f2 0) (hh 0)
  have h_h1 := bil_le_abs (h 1) (A_val f1 f2 1) (hh 1)
  have h_h2 := bil_le_abs (h 2) (A_val f1 f2 2) (hh 2)
  rw [eq0] at h_h0
  rw [eq1] at h_h1
  rw [eq2] at h_h2
  linarith

lemma eval_functional_convexHull (S : Set (ZMod 3 → ℝ)) (B : ℝ)
  (hS : ∀ p ∈ S, eval_functional p ≤ B) (p : ZMod 3 → ℝ) (hp : p ∈ convexHull ℝ S) :
  eval_functional p ≤ B := by rewrite[@mem_convexHull_iff]at hp
                              use hp {x|∑i,_* x i≤B} (hS) fun and R L M a s K V C=>Set.mem_setOf.2 ?_
                              exact (dotProduct_add _ _ _).trans_le.comp (add_le_add ↑(dotProduct_smul _ _ _).le ↑(dotProduct_smul _ _ _).le).trans ↑(isPreconnected_Iic.convex R M K V @C)

lemma all_phi_prime_le_19_9 : ∀ phi ∈ Φ' (ZMod 3), eval_functional phi ≤ 19 / 9 := by
  intro phi hphi
  exact eval_functional_convexHull (baseΦ' (ZMod 3)) (19 / 9) base_phi_prime_le_19_9 phi hphi

lemma green57_false : ¬ ∀ (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G], Φ G = Φ' G := by
  intro h
  have h3 := h (ZMod 3)
  have hphi_in : phi_witness ∈ Φ (ZMod 3) := subset_convexHull _ _ phi_witness_in_baseΦ
  rw [h3] at hphi_in
  have hval := all_phi_prime_le_19_9 phi_witness hphi_in
  have hval2 := phi_witness_eval
  linarith


/--
Is it true that for every finite abelian group $G$ the convex hulls $\Phi(G)$ and $\Phi'(G)$,
obtained from kernels $\phi(g) = \mathbb{E}_{x_1 + x_2 + x_3 = g} f_1(x_2, x_3)
      f_2(x_1, x_3) f_3(x_1, x_2)$ with $\lVert f_i \rVert_\infty \le 1$, still coincide when the
third kernel is required to depend only on $x_1 + x_2$?

A DeepMind prover agent showed that this is false for $G = \mathbb{Z}/3/mathbb{Z}$.
-/
@[category research solved, AMS 5 11]
theorem green_57 :
  answer(False) ↔
    ∀ (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G],
      Φ G = Φ' G := by
  constructor
  · intro h
    exfalso
    exact h
  · intro h
    have hF := green57_false h
    exact hF

end

end Green57
