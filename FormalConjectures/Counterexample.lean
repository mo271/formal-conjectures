import FormalConjectures.Util.ProblemImports
import Mathlib

namespace Erdos1097

/-- The set of functions from `Fin M` to `{0, 2}`. -/
def X_funs (M : ℕ) : Finset (Fin M → ℤ) :=
  Fintype.piFinset (fun _ => ({0, 2} : Finset ℤ))

/-- The set of functions from `Fin M` to `{1, 2}`. -/
def Y_funs (M : ℕ) : Finset (Fin M → ℤ) :=
  Fintype.piFinset (fun _ => ({1, 2} : Finset ℤ))

/-- The set of functions from `Fin M` to `{-1, 0, 1}`. -/
def D_funs (M : ℕ) : Finset (Fin M → ℤ) :=
  Fintype.piFinset (fun _ => ({-1, 0, 1} : Finset ℤ))

/-- Evaluates a function in base 3. -/
def eval_fun (M : ℕ) (f : Fin M → ℤ) : ℤ :=
  ∑ i : Fin M, f i * (3 : ℤ) ^ (i : ℕ)

/-- The image of `X_funs` under `eval_fun`. -/
def X_M (M : ℕ) : Finset ℤ := (X_funs M).image (eval_fun M)

/-- The image of `Y_funs` under `eval_fun`. -/
def Y_M (M : ℕ) : Finset ℤ := (Y_funs M).image (eval_fun M)

/-- The union of `X_M` and `Y_M`. -/
def A_M (M : ℕ) : Finset ℤ := X_M M ∪ Y_M M

end Erdos1097

/-- The size of `A_M` is at most `2^(M+1)`. -/
lemma card_A_M (M : ℕ) : (Erdos1097.A_M M).card ≤ 2^(M+1) := by
  /-
  Proof outline:
  The set $A_M$ is the union of $X_M$ and $Y_M$.
  The size of $X_M$ is at most the number of functions in $X\_funs$, which is $2^M$.
  The size of $Y_M$ is at most the number of functions in $Y\_funs$, which is $2^M$.
  Therefore, the size of $A_M$ is at most $2^M + 2^M = 2^{M+1}$.
  -/
  unfold Erdos1097.A_M
  apply le_trans (Finset.card_union_le _ _)
  have hX : (Erdos1097.X_M M).card ≤ 2^M := by
    unfold Erdos1097.X_M
    apply le_trans Finset.card_image_le
    unfold Erdos1097.X_funs
    rw [Fintype.card_piFinset]
    have : ∏ i : Fin M, ({0, 2} : Finset ℤ).card = 2^M := by
      have : ({0, 2} : Finset ℤ).card = 2 := rfl
      simp [this]
    exact le_of_eq this
  have hY : (Erdos1097.Y_M M).card ≤ 2^M := by
    unfold Erdos1097.Y_M
    apply le_trans Finset.card_image_le
    unfold Erdos1097.Y_funs
    rw [Fintype.card_piFinset]
    have : ∏ i : Fin M, ({1, 2} : Finset ℤ).card = 2^M := by
      have : ({1, 2} : Finset ℤ).card = 2 := rfl
      simp [this]
    exact le_of_eq this
  have h2 : 2 ^ (M + 1) = 2 ^ M + 2 ^ M := by ring
  linarith



namespace Erdos1097

/-- Evaluates a function in base 3 for M+1, splitting off the last term. -/
lemma eval_fun_succ (M : ℕ) (f : Fin (M + 1) → ℤ) :
  eval_fun (M + 1) f = f ⟨M, Nat.lt_succ_self M⟩ * 3^M + eval_fun M (fun i => f ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self M)⟩) := by
  /-
  Proof outline:
  We expand the sum defining `eval_fun` for $M+1$ terms.
  We split the sum into the last term (index $M$) and the sum of the first $M$ terms.
  The last term is $f(M) \cdot 3^M$, and the remaining sum is exactly `eval_fun M` applied to the restriction of $f$.
  -/
  unfold eval_fun
  rw [Fin.sum_univ_castSucc]
  have h1 : f (Fin.last M) * 3 ^ (Fin.last M : ℕ) = f ⟨M, Nat.lt_succ_self M⟩ * 3 ^ M := rfl
  rw [h1, add_comm]
  rfl

/-- Evaluates a function in base 3 for M+1, splitting off the first term. -/
lemma eval_fun_succ_left (M : ℕ) (f : Fin (M + 1) → ℤ) :
  eval_fun (M + 1) f = f 0 + 3 * eval_fun M (fun i => f i.succ) := by
  /-
  Proof outline:
  We expand the sum defining `eval_fun` for $M+1$ terms.
  We split the sum into the first term (index $0$) and the sum of the remaining $M$ terms.
  The first term is $f(0) \cdot 3^0 = f(0)$.
  For the remaining terms, we factor out a 3 from $3^{i+1} = 3 \cdot 3^i$, giving $3$ times `eval_fun M` applied to the shifted function.
  -/
  unfold eval_fun
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have : (3 : ℤ) ^ (i.succ : ℕ) = 3 * 3 ^ (i : ℕ) := by
    have h_succ : (i.succ : ℕ) = (i : ℕ) + 1 := rfl
    rw [h_succ, pow_add, pow_one, mul_comm]
  rw [this]
  ring

/-- Injectivity of eval_fun when coefficients are in {0, 1, 2}. -/
lemma eval_fun_inj {M : ℕ} (f g : Fin M → ℤ) (hf : ∀ i, f i ∈ ({0, 1, 2} : Set ℤ)) (hg : ∀ i, g i ∈ ({0, 1, 2} : Set ℤ)) (h : eval_fun M f = eval_fun M g) : f = g := by
  /-
  Proof outline:
  We proceed by induction on $M$. The base case $M=0$ is trivial.
  For the inductive step, we use `eval_fun_succ_left` to split off the first term of both $f$ and $g$.
  Taking both sides modulo 3, we see that $f(0) \equiv g(0) \pmod 3$.
  Since $f(0), g(0) \in \{0, 1, 2\}$, this implies $f(0) = g(0)$.
  Subtracting this from both sides and dividing by 3, we get that `eval_fun M` of the shifted functions are equal.
  By the inductive hypothesis, the shifted functions are equal, so $f = g$.
  -/
  induction M with
  | zero =>
    ext i
    exact Fin.elim0 i
  | succ M ih =>
    have h1 := eval_fun_succ_left M f
    have h2 := eval_fun_succ_left M g
    rw [h1, h2] at h
    have h_mod : (f 0 + 3 * eval_fun M (fun i => f i.succ)) % 3 = (g 0 + 3 * eval_fun M (fun i => g i.succ)) % 3 := by rw [h]
    have h_mod_f : (f 0 + 3 * eval_fun M (fun i => f i.succ)) % 3 = f 0 % 3 := by omega
    have h_mod_g : (g 0 + 3 * eval_fun M (fun i => g i.succ)) % 3 = g 0 % 3 := by omega
    rw [h_mod_f, h_mod_g] at h_mod
    have hf0 := hf 0
    have hg0 := hg 0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf0 hg0
    have h0 : f 0 = g 0 := by
      rcases hf0 with hf0 | hf0 | hf0 <;> rcases hg0 with hg0 | hg0 | hg0 <;> (rw [hf0, hg0] at h_mod ⊢; try rfl) <;> revert h_mod <;> decide
    have h_rest : 3 * eval_fun M (fun i => f i.succ) = 3 * eval_fun M (fun i => g i.succ) := by
      linarith
    have h_rest2 : eval_fun M (fun i => f i.succ) = eval_fun M (fun i => g i.succ) := by
      linarith
    have h_ih := ih (fun i => f i.succ) (fun i => g i.succ) (fun i => hf i.succ) (fun i => hg i.succ) h_rest2
    ext i
    cases i using Fin.cases with
    | zero => exact h0
    | succ i =>
      have h_ih_i := congr_fun h_ih i
      exact h_ih_i

/-- Injectivity of eval_fun when coefficients are in {-1, 0, 1}. -/
lemma eval_fun_inj_D {M : ℕ} (f g : Fin M → ℤ) (hf : ∀ i, f i ∈ ({-1, 0, 1} : Set ℤ)) (hg : ∀ i, g i ∈ ({-1, 0, 1} : Set ℤ)) (h : eval_fun M f = eval_fun M g) : f = g := by
  /-
  Proof outline:
  We proceed by induction on $M$. The base case $M=0$ is trivial.
  For the inductive step, we use `eval_fun_succ_left` to split off the first term of both $f$ and $g$.
  Taking both sides modulo 3, we see that $f(0) \equiv g(0) \pmod 3$.
  Since $f(0), g(0) \in \{-1, 0, 1\}$, this implies $f(0) = g(0)$.
  Subtracting this from both sides and dividing by 3, we get that `eval_fun M` of the shifted functions are equal.
  By the inductive hypothesis, the shifted functions are equal, so $f = g$.
  -/
  induction M with
  | zero =>
    ext i
    exact Fin.elim0 i
  | succ M ih =>
    have h1 := eval_fun_succ_left M f
    have h2 := eval_fun_succ_left M g
    rw [h1, h2] at h
    have h_mod : (f 0 + 3 * eval_fun M (fun i => f i.succ)) % 3 = (g 0 + 3 * eval_fun M (fun i => g i.succ)) % 3 := by rw [h]
    have h_mod_f : (f 0 + 3 * eval_fun M (fun i => f i.succ)) % 3 = f 0 % 3 := by omega
    have h_mod_g : (g 0 + 3 * eval_fun M (fun i => g i.succ)) % 3 = g 0 % 3 := by omega
    rw [h_mod_f, h_mod_g] at h_mod
    have hf0 := hf 0
    have hg0 := hg 0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf0 hg0
    have h0 : f 0 = g 0 := by
      rcases hf0 with hf0 | hf0 | hf0 <;> rcases hg0 with hg0 | hg0 | hg0 <;> (rw [hf0, hg0] at h_mod ⊢; try rfl) <;> revert h_mod <;> decide
    have h_rest : 3 * eval_fun M (fun i => f i.succ) = 3 * eval_fun M (fun i => g i.succ) := by
      linarith
    have h_rest2 : eval_fun M (fun i => f i.succ) = eval_fun M (fun i => g i.succ) := by
      linarith
    have h_ih := ih (fun i => f i.succ) (fun i => g i.succ) (fun i => hf i.succ) (fun i => hg i.succ) h_rest2
    ext i
    cases i using Fin.cases with
    | zero => exact h0
    | succ i =>
      have h_ih_i := congr_fun h_ih i
      exact h_ih_i

end Erdos1097



