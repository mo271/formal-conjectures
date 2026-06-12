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
# OEIS A177043: Central MacMahon numbers

The central MacMahon numbers are defined as $a(n) = T(2n+1, n+1)$ where $T(n,k)$ is the triangle
of type B Eulerian numbers (OEIS A060187).

The type B Eulerian numbers satisfy the recurrence
$T(n, 1) = T(n, n) = 1$ and $T(n, k) = (2n - 2k + 1) T(n-1, k-1) + (2k - 1) T(n-1, k)$,
and have the closed form
$T(n, k) = \sum_{i=1}^{k} (-1)^{k-i} \binom{n}{k-i} (2i-1)^{n-1}$.

An equivalent explicit formula for the central MacMahon numbers is:
$$a(n) = \sum_{i=0}^{n} (-1)^{n-i} \binom{2n+1}{n-i} (2i+1)^{2n}.$$

A third formula, using Stirling numbers of the second kind, arises from the inclusion-exclusion
principle. Let
$$E(j_r, j_s, 2n) = \sum_{r=0}^{2n} (-1)^{2n-r} \binom{2n}{r}
  \left\{r \atop j_r\right\} j_r! \left\{2n-r \atop j_s\right\} j_s!$$
Then:
$$a(n) = \sum_{j_r=0}^{n} \sum_{j_s=0}^{n} \binom{2n+1}{j_r}
  \binom{2n+1-j_r}{j_s} \binom{2n-j_r-j_s}{n-j_r} \cdot E(j_r, j_s, 2n).$$

*Reference:* [A177043](https://oeis.org/A177043)
-/

namespace OeisA177043

open Finset Nat

/-- The Eulerian numbers of type B (A060187), given by
$T(n, k) = \sum_{i=1}^{k} (-1)^{k-i} \binom{n}{k-i} (2i-1)^{n-1}$.
Here we use 1-based indexing for $k$. -/
def eulerianB (n k : ℕ) : ℤ :=
  ∑ i ∈ range k,
    (-1) ^ (k - 1 - i) * (n.choose (k - 1 - i) : ℤ) * ((2 * (i : ℤ) + 1) ^ (n - 1))

/-- The central MacMahon numbers via the type B Eulerian triangle:
$a'(n) = T(2n+1, n+1)$. -/
def a' (n : ℕ) : ℤ := eulerianB (2 * n + 1) (n + 1)

/-- The central MacMahon numbers: $a(n) = \sum_{i=0}^{n} (-1)^{n-i} \binom{2n+1}{n-i}
(2i+1)^{2n}$. These are the central column of the type B Eulerian number triangle
(A060187). -/
def a (n : ℕ) : ℤ :=
  ∑ i ∈ range (n + 1),
    (-1) ^ (n - i) * (Nat.choose (2 * n + 1) (n - i) : ℤ) * ((2 * (i : ℤ) + 1) ^ (2 * n))

/-- The two definitions of the central MacMahon numbers agree. -/
@[category API, AMS 5]
theorem a_eq_a' (n : ℕ) : a n = a' n := by
  simp only [a, a', eulerianB]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  have h1 : n + 1 - 1 - i = n - i := by omega
  have h2 : 2 * n + 1 - 1 = 2 * n := by omega
  rw [h1, h2]

/-- The auxiliary function $E(j_r, j_s, m) =
$\sum_{r=0}^{m} (-1)^{m-r} \binom{m}{r} \{r \choose j_r\} j_r! \{m-r \choose j_s\} j_s!$. -/
def E (jr js m : ℕ) : ℤ :=
  ∑ r ∈ range (m + 1),
    (-1) ^ (m - r) * (m.choose r : ℤ) *
      (Nat.stirlingSecond r jr * jr.factorial : ℤ) *
      (Nat.stirlingSecond (m - r) js * js.factorial : ℤ)

/-- The degree formula $D(q, 1)$ from Zhang.
It sums over $0 \le j_r, j_s \le (q-1)/2$.
We use `n = (q - 1) / 2` for the upper bounds of the sums.
The multinomial coefficient $\binom{q}{j_r, j_s, q-j_r-j_s}$ is expressed as the product
of binomial coefficients $\binom{q}{j_r} \binom{q-j_r}{j_s}$. -/
def D (q : ℕ) : ℤ :=
  let n := (q - 1) / 2
  ∑ jr ∈ range (n + 1), ∑ js ∈ range (n + 1),
    (q.choose jr : ℤ) *
    ((q - jr).choose js : ℤ) *
    ((q - 1 - jr - js).choose (n - jr) : ℤ) *
    E jr js (q - 1)

/-- The Zhang formula for the central MacMahon numbers, using Stirling numbers of the
second kind. The sequence is obtained by multiplying the degree by $(-1)^n$. -/
def zhang (n : ℕ) : ℤ := (-1) ^ n * D (2 * n + 1)

/- ## Proof of `zhang_eq_a`

The proof proceeds through a chain of identities:

1. **Stirling inclusion-exclusion**: `k! · S(m,k) = ∑_{j=0}^{k} (-1)^{k-j} C(k,j) j^m`
2. **E closed form**: Substitute (1) into `E` and apply the binomial theorem
3. **Sum collapse**: Apply Vandermonde-type identities to collapse the 4-fold sum in `D`
   to the 1-fold sum in `a(n)`
-/

section Proof

-- Auxiliary definitions for the proof
private def f (m k : ℕ) : ℤ :=
  ∑ j ∈ range (k + 1), (-1 : ℤ) ^ (k - j) * (k.choose j : ℤ) * (j : ℤ) ^ m

private def g (m k : ℕ) : ℤ :=
  ∑ j ∈ range (k + 1), (-1 : ℤ) ^ (k - j) * (k.choose j : ℤ) * ((j : ℤ) + 1) ^ m

-- Step 0: Sign manipulation
@[category API, AMS 5]
private lemma neg_one_pow_sub (a b : ℕ) (h : b ≤ a) :
    (-1 : ℤ) ^ (a - b) = (-1) ^ a * (-1) ^ b := by
  have key : (-1 : ℤ) ^ (a - b) * (-1) ^ b = (-1) ^ a := by
    rw [← pow_add, Nat.sub_add_cancel h]
  have inv : ((-1 : ℤ) ^ b) * ((-1 : ℤ) ^ b) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  calc (-1 : ℤ) ^ (a - b)
      = (-1) ^ (a - b) * 1 := by ring
    _ = (-1) ^ (a - b) * ((-1) ^ b * (-1) ^ b) := by rw [inv]
    _ = ((-1) ^ (a - b) * (-1) ^ b) * (-1) ^ b := by ring
    _ = (-1) ^ a * (-1) ^ b := by rw [key]

-- Step 1a: Alternating sum of binomials is zero
@[category API, AMS 5]
private lemma alternating_binom_zero (k : ℕ) :
    ∑ j ∈ range (k + 2), (-1 : ℤ) ^ (k + 1 - j) * ((k + 1).choose j : ℤ) = 0 := by
  have step : ∀ j ∈ range (k + 2),
      (-1 : ℤ) ^ (k + 1 - j) * ((k + 1).choose j : ℤ) =
        (-1) ^ (k + 1) * ((-1) ^ j * ((k + 1).choose j : ℤ)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [neg_one_pow_sub (k + 1) j (by omega)]
    ring
  rw [Finset.sum_congr rfl step, ← Finset.mul_sum]
  suffices h : ∑ i ∈ range (k + 2), (-1 : ℤ) ^ i * ((k + 1).choose i : ℤ) = 0 by
    rw [h]; ring
  convert Int.alternating_sum_range_choose_of_ne (n := k + 1) (by omega) using 1

-- Step 1b: Base cases for f
@[category API, AMS 5]
private lemma f_zero_succ (k : ℕ) : f 0 (k + 1) = 0 := by
  simp [f]; exact alternating_binom_zero k

@[category API, AMS 5]
private lemma f_zero_zero : f 0 0 = 1 := by simp [f]

@[category API, AMS 5]
private lemma f_succ_zero (m : ℕ) : f (m + 1) 0 = 0 := by simp [f]

-- Step 1c: Absorption identity
@[category API, AMS 5]
private lemma absorption (k j : ℕ) (hj : 0 < j) :
    (j : ℤ) * ((k + 1).choose j : ℤ) = ((k + 1 : ℕ) : ℤ) * (k.choose (j - 1) : ℤ) := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  have := Nat.add_one_mul_choose_eq k j'
  exact_mod_cast (show (j' + 1) * (k + 1).choose (j' + 1) = (k + 1) * k.choose j' by
    rw [mul_comm]; exact this.symm)

-- Step 1d: Recurrence lemmas for f
@[category API, AMS 5]
private lemma f_succ_range (m k : ℕ) :
    f m (k + 1) = (-1 : ℤ) ^ (k + 1) * (0 : ℤ) ^ m +
      ∑ j ∈ range (k + 1), (-1 : ℤ) ^ (k - j) *
        ((k + 1).choose (j + 1) : ℤ) * ((j + 1 : ℕ) : ℤ) ^ m := by
  rw [f, sum_range_succ']
  have h_zero : (-1 : ℤ) ^ (k + 1 - 0) * ↑((k + 1).choose 0) * ↑(0 : ℕ) ^ m =
      (-1 : ℤ) ^ (k + 1) * (0 : ℤ) ^ m := by simp
  rw [h_zero, add_comm]
  congr 1
  apply sum_congr rfl
  intro j hj; rw [mem_range] at hj
  have : k + 1 - (j + 1) = k - j := by omega
  rw [this]

@[category API, AMS 5]
private lemma choose_succ_succ_split (k j : ℕ) :
    ((k + 1).choose (j + 1) : ℤ) = (k.choose (j + 1) : ℤ) + (k.choose j : ℤ) := by
  rw [Nat.choose_succ_succ]; push_cast; ring

@[category API, AMS 5]
private lemma g_eq_f_add (m k : ℕ) : g m k = f m (k + 1) + f m k := by
  rw [f_succ_range]
  have h_split : ∑ j ∈ range (k + 1),
      (-1 : ℤ) ^ (k - j) * ((k + 1).choose (j + 1) : ℤ) * ((j + 1 : ℕ) : ℤ) ^ m =
      ∑ j ∈ range (k + 1),
        (-1 : ℤ) ^ (k - j) * (k.choose (j + 1) : ℤ) * ((j + 1 : ℕ) : ℤ) ^ m +
      ∑ j ∈ range (k + 1),
        (-1 : ℤ) ^ (k - j) * (k.choose j : ℤ) * ((j + 1 : ℕ) : ℤ) ^ m := by
    simp_rw [choose_succ_succ_split]
    have : ∀ j ∈ range (k + 1),
        (-1 : ℤ) ^ (k - j) * ((k.choose (j + 1) : ℤ) + (k.choose j : ℤ)) *
          ((j + 1 : ℕ) : ℤ) ^ m =
        (-1 : ℤ) ^ (k - j) * (k.choose (j + 1) : ℤ) * ((j + 1 : ℕ) : ℤ) ^ m +
        (-1 : ℤ) ^ (k - j) * (k.choose j : ℤ) * ((j + 1 : ℕ) : ℤ) ^ m := by
      intro j _; ring
    rw [sum_congr rfl this, sum_add_distrib]
  rw [h_split]
  have h_g : ∑ j ∈ range (k + 1),
      (-1 : ℤ) ^ (k - j) * (k.choose j : ℤ) * ((j + 1 : ℕ) : ℤ) ^ m = g m k := rfl
  rw [h_g]
  have h_sum : ∑ j ∈ range (k + 1),
      (-1 : ℤ) ^ (k - j) * (k.choose (j + 1) : ℤ) * ((j + 1 : ℕ) : ℤ) ^ m =
      ∑ j ∈ range k,
      (-1 : ℤ) ^ (k - j) * (k.choose (j + 1) : ℤ) * ((j + 1 : ℕ) : ℤ) ^ m := by
    rw [sum_range_succ]
    simp
  rw [h_sum]
  have h_f : f m k = (-1 : ℤ) ^ k * 0 ^ m +
      ∑ j ∈ range k,
        (-1 : ℤ) ^ (k - (j + 1)) * (k.choose (j + 1) : ℤ) * ((j + 1 : ℕ) : ℤ) ^ m := by
    rw [f, sum_range_succ']
    have : k - 0 = k := by omega
    have h0 : (-1 : ℤ) ^ (k - 0) * ↑(k.choose 0) * ↑(0 : ℕ) ^ m =
        (-1 : ℤ) ^ k * 0 ^ m := by rw [this]; simp
    rw [h0, add_comm]
  have h_neg : ∑ j ∈ range k,
      (-1 : ℤ) ^ (k - j) * (k.choose (j + 1) : ℤ) * ((j + 1 : ℕ) : ℤ) ^ m =
      - ∑ j ∈ range k,
      (-1 : ℤ) ^ (k - (j + 1)) * (k.choose (j + 1) : ℤ) * ((j + 1 : ℕ) : ℤ) ^ m := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro j hj; rw [mem_range] at hj
    have : (-1 : ℤ) ^ (k - j) = - (-1 : ℤ) ^ (k - (j + 1)) := by
      have : k - j = k - (j + 1) + 1 := by omega
      rw [this, pow_add, pow_one]; ring
    rw [this]; ring
  rw [h_neg]
  have h_pow : (-1 : ℤ) ^ (k + 1) * 0 ^ m = - ((-1 : ℤ) ^ k * 0 ^ m) := by
    rw [pow_succ]; ring
  rw [h_pow, h_f]; ring

@[category API, AMS 5]
private lemma f_succ_succ_eq (m k : ℕ) :
    f (m + 1) (k + 1) = ((k : ℤ) + 1) * g m k := by
  rw [f, g]
  have h_sum : ∑ j ∈ range (k + 1 + 1),
      (-1 : ℤ) ^ (k + 1 - j) * ↑((k + 1).choose j) * ↑j ^ (m + 1) =
      ∑ j ∈ range (k + 1),
      (-1 : ℤ) ^ (k + 1 - (j + 1)) * ↑((k + 1).choose (j + 1)) * ↑(j + 1) ^ (m + 1) := by
    rw [sum_range_succ']
    have h0 : (-1 : ℤ) ^ (k + 1 - 0) * ↑((k + 1).choose 0) * ↑(0 : ℕ) ^ (m + 1) = 0 := by
      have : ↑(0 : ℕ) ^ (m + 1) = (0 : ℤ) := by push_cast; exact zero_pow (by omega)
      rw [this]; ring
    rw [h0, add_zero]
  rw [h_sum, mul_sum]
  apply sum_congr rfl
  intro j hj; rw [mem_range] at hj
  have h_pow : ((j + 1 : ℕ) : ℤ) ^ (m + 1) = ((j + 1 : ℕ) : ℤ) * ((j + 1 : ℕ) : ℤ) ^ m := by
    rw [pow_succ]; ring
  have h_sub : k + 1 - (j + 1) = k - j := by omega
  rw [h_sub, h_pow]
  have h_abs : ((j + 1 : ℕ) : ℤ) * ((k + 1).choose (j + 1) : ℤ) =
      ((k + 1 : ℕ) : ℤ) * (k.choose j : ℤ) := by
    have := absorption k (j + 1) (by omega)
    have hj1 : j + 1 - 1 = j := by omega
    rw [hj1] at this; exact this
  calc (-1 : ℤ) ^ (k - j) * ↑((k + 1).choose (j + 1)) * (↑(j + 1) * ↑(j + 1) ^ m)
      = (-1 : ℤ) ^ (k - j) * (↑(j + 1) * ↑((k + 1).choose (j + 1))) * ↑(j + 1) ^ m := by ring
    _ = (-1 : ℤ) ^ (k - j) * ((↑k + 1) * ↑(k.choose j)) * ↑(j + 1) ^ m := by
        rw [h_abs]; push_cast; rfl
    _ = (↑k + 1) * ((-1 : ℤ) ^ (k - j) * ↑(k.choose j) * ↑(j + 1) ^ m) := by ring

@[category API, AMS 5]
private lemma f_recurrence (m k : ℕ) :
    f (m + 1) (k + 1) = ((k : ℤ) + 1) * (f m (k + 1) + f m k) := by
  rw [f_succ_succ_eq, g_eq_f_add]

-- Step 2: Stirling numbers inclusion-exclusion
/-- The inclusion-exclusion identity for Stirling numbers:
$k! \cdot S(m,k) = \sum_{j=0}^{k} (-1)^{k-j} \binom{k}{j} j^m$. -/
@[category API, AMS 5]
private theorem stirling_IE (m k : ℕ) :
    (k.factorial : ℤ) * (Nat.stirlingSecond m k : ℤ) = f m k := by
  induction m, k using Nat.stirlingSecond.induct with
  | case1 => simp [f_zero_zero, Nat.stirlingSecond]
  | case2 k => simp [f_zero_succ, Nat.stirlingSecond]
  | case3 n => simp [f_succ_zero, Nat.stirlingSecond]
  | case4 n k ih1 ih2 =>
    rw [Nat.stirlingSecond_succ_succ]; push_cast
    rw [f_recurrence, ← ih1, ← ih2, Nat.factorial_succ]; push_cast; ring

-- Step 3: E closed form
/-- The closed form for $E$ after applying the Stirling inclusion-exclusion identity:
$E(j_r, j_s, m) = \sum_{a=0}^{j_r} \sum_{b=0}^{j_s}
  (-1)^{j_r-a+j_s-b} \binom{j_r}{a} \binom{j_s}{b} (a-b)^m$. -/
@[category API, AMS 5]
private theorem E_eq_E_closed (jr js m : ℕ) :
    E jr js m =
    ∑ a ∈ range (jr + 1), ∑ b ∈ range (js + 1),
      (-1 : ℤ) ^ (jr - a + (js - b)) * (jr.choose a : ℤ) * (js.choose b : ℤ) *
      ((a : ℤ) - b) ^ m := by
  have h_stirling : ∀ r k, (Nat.stirlingSecond r k * k.factorial : ℤ) =
      ∑ j ∈ range (k + 1), (-1 : ℤ) ^ (k - j) * (k.choose j : ℤ) * (j : ℤ) ^ r := by
    intro r k; rw [mul_comm]; exact stirling_IE r k
  rw [E]
  simp_rw [h_stirling]
  -- Distribute the outer product into inner sums
  have h_expand : ∀ r ∈ range (m + 1),
      (-1 : ℤ) ^ (m - r) * ↑(m.choose r) *
      (∑ j ∈ range (jr + 1), (-1 : ℤ) ^ (jr - j) * ↑(jr.choose j) * ↑j ^ r) *
      (∑ j ∈ range (js + 1), (-1 : ℤ) ^ (js - j) * ↑(js.choose j) * ↑j ^ (m - r)) =
      ∑ a ∈ range (jr + 1), ∑ b ∈ range (js + 1),
        ((-1 : ℤ) ^ (m - r) * ↑(m.choose r) *
        ((-1 : ℤ) ^ (jr - a) * ↑(jr.choose a) * ↑a ^ r) *
        ((-1 : ℤ) ^ (js - b) * ↑(js.choose b) * ↑b ^ (m - r))) := by
    intro r _
    rw [mul_assoc]
    rw [show (∑ j ∈ range (jr + 1), (-1 : ℤ) ^ (jr - j) * ↑(jr.choose j) * ↑j ^ r) *
        (∑ j ∈ range (js + 1), (-1 : ℤ) ^ (js - j) * ↑(js.choose j) * ↑j ^ (m - r)) =
        ∑ a ∈ range (jr + 1), ∑ b ∈ range (js + 1),
        ((-1 : ℤ) ^ (jr - a) * ↑(jr.choose a) * ↑a ^ r) *
        ((-1 : ℤ) ^ (js - b) * ↑(js.choose b) * ↑b ^ (m - r)) from by
      rw [sum_mul]; apply sum_congr rfl; intro a _; rw [mul_sum]]
    rw [mul_sum]; apply sum_congr rfl; intro a _
    rw [mul_sum]; apply sum_congr rfl; intro b _; ring
  rw [sum_congr rfl h_expand]
  -- Swap sums: r ↔ a, then r ↔ b
  rw [sum_comm]
  apply sum_congr rfl; intro a _
  rw [sum_comm]
  apply sum_congr rfl; intro b _
  -- Factor out constants and apply binomial theorem
  rw [show ∑ r ∈ range (m + 1),
      (-1 : ℤ) ^ (m - r) * ↑(m.choose r) *
      ((-1 : ℤ) ^ (jr - a) * ↑(jr.choose a) * ↑a ^ r) *
      ((-1 : ℤ) ^ (js - b) * ↑(js.choose b) * ↑b ^ (m - r)) =
      (-1 : ℤ) ^ (jr - a + (js - b)) * ↑(jr.choose a) * ↑(js.choose b) *
      ∑ r ∈ range (m + 1), (-1 : ℤ) ^ (m - r) * ↑(m.choose r) * ↑a ^ r * ↑b ^ (m - r) from by
    rw [mul_sum]; apply sum_congr rfl; intro r _
    rw [show (-1 : ℤ) ^ (jr - a + (js - b)) = (-1 : ℤ) ^ (jr - a) * (-1 : ℤ) ^ (js - b) from
        pow_add (-1) _ _]
    ring]
  congr 1
  -- Apply binomial theorem: sum = (a - b)^m
  have : ((a : ℤ) - b) ^ m = ((a : ℤ) + - (b : ℤ)) ^ m := by ring
  rw [this, add_pow]
  apply sum_congr rfl
  intro r hr; rw [mem_range] at hr
  rw [show (- (b : ℤ)) ^ (m - r) = (-1 : ℤ) ^ (m - r) * (b : ℤ) ^ (m - r) from by
    rw [show - (b : ℤ) = (-1 : ℤ) * (b : ℤ) from by ring, mul_pow]]
  ring

-- Step 4a: Binomial sum identity and helpers
-- Prove: n.choose k * (n-k).choose k1 = n.choose k1 * (n-k1).choose k
@[category API, AMS 5]
lemma choose_mul_choose_comm (n k k1 : ℕ) :
    n.choose k * (n - k).choose k1 = n.choose k1 * (n - k1).choose k := by
  have h_kk1 : k ≤ k + k1 := Nat.le_add_right k k1
  have step1 : n.choose (k + k1) * (k + k1).choose k = n.choose k * (n - k).choose k1 := by
    have := @Nat.choose_mul n (k + k1) k h_kk1
    rwa [show k + k1 - k = k1 from by omega] at this
  have h_k1k : k1 ≤ k + k1 := Nat.le_add_left k1 k
  have step2 : n.choose (k + k1) * (k + k1).choose k1 = n.choose k1 * (n - k1).choose k := by
    have := @Nat.choose_mul n (k + k1) k1 h_k1k
    rwa [show k + k1 - k1 = k from by omega] at this
  have h_sym : (k + k1).choose k = (k + k1).choose k1 := by
    have h := Nat.choose_symm h_kk1
    rw [show k + k1 - k = k1 from by omega] at h
    exact h.symm
  calc n.choose k * (n - k).choose k1
      = n.choose (k + k1) * (k + k1).choose k := step1.symm
    _ = n.choose (k + k1) * (k + k1).choose k1 := by rw [h_sym]
    _ = n.choose k1 * (n - k1).choose k := step2

@[category API, AMS 5]
lemma choose_mul_choose_mul_choose (q j jr js : ℕ) (hjs : js ≤ j) (hj : j ≤ q) :
    q.choose j * (q - j).choose jr * j.choose js =
    q.choose js * (q - js).choose jr * (q - js - jr).choose (j - js) := by
  by_cases hjr : jr ≤ q - j
  · calc q.choose j * (q - j).choose jr * j.choose js
        = q.choose j * j.choose js * (q - j).choose jr := by ring
      _ = q.choose js * (q - js).choose (j - js) * (q - j).choose jr := by
        rw [Nat.choose_mul hjs]
      _ = q.choose js * ((q - js).choose (j - js) * (q - j).choose jr) := by ring
      _ = q.choose js * ((q - js).choose (j - js) * ((q - js) - (j - js)).choose jr) := by
        congr 2; congr 1; omega
      _ = q.choose js * ((q - js).choose jr * (q - js - jr).choose (j - js)) := by
        rw [choose_mul_choose_comm (q - js) (j - js) jr]
      _ = q.choose js * (q - js).choose jr * (q - js - jr).choose (j - js) := by ring
  · have h1 : (q - j).choose jr = 0 := Nat.choose_eq_zero_of_lt (not_le.mp hjr)
    by_cases hjs_r : jr ≤ q - js
    · have h2 : q - js - jr < j - js := by omega
      have h3 : (q - js - jr).choose (j - js) = 0 := Nat.choose_eq_zero_of_lt h2
      simp [h1, h3]
    · have h2 : (q - js).choose jr = 0 := Nat.choose_eq_zero_of_lt (not_le.mp hjs_r)
      simp [h1, h2]

@[category API, AMS 5]
lemma sum_range_add_split (n js : ℕ) (h : js ≤ n + 1) (g : ℕ → ℤ) :
    ∑ j ∈ range (n + 1), g j = (∑ j ∈ range js, g j) + ∑ j ∈ range (n + 1 - js), g (js + j) := by
  have : n + 1 = js + (n + 1 - js) := by omega
  nth_rw 1 [this]
  exact sum_range_add g js (n + 1 - js)

@[category API, AMS 5]
lemma partial_alternating_binom_sum (k m : ℕ) (hm : 1 ≤ m) :
    ∑ j ∈ range (k + 1), (-1 : ℤ) ^ j * (m.choose j : ℤ) =
    (-1 : ℤ) ^ k * ((m - 1).choose k : ℤ) := by
  induction' k with k ih
  · simp
  · rw [sum_range_succ, ih]
    have h_pascal : (m - 1).choose (k + 1) + (m - 1).choose k = m.choose (k + 1) := by
      have : m - 1 + 1 = m := by omega
      rw [← this, add_comm]
      exact (Nat.choose_succ_succ (m - 1) k).symm
    calc (-1 : ℤ) ^ k * ((m - 1).choose k : ℤ) + (-1 : ℤ) ^ (k + 1) * (m.choose (k + 1) : ℤ)
      _ = (-1 : ℤ) ^ k * ((m - 1).choose k : ℤ) - (-1 : ℤ) ^ k * (m.choose (k + 1) : ℤ) := by
        rw [pow_succ]; ring
      _ = (-1 : ℤ) ^ k * (((m - 1).choose k : ℤ) - (m.choose (k + 1) : ℤ)) := by ring
      _ = (-1 : ℤ) ^ k * -((m - 1).choose (k + 1) : ℤ) := by
        congr 1
        
        linarith
      _ = (-1 : ℤ) ^ (k + 1) * ((m - 1).choose (k + 1) : ℤ) := by
        rw [pow_succ]; ring


@[category API, AMS 5]
lemma binom_sum_identity (n jr js : ℕ) (h_sum_le : jr + js ≤ 2 * n) :
    ∑ j ∈ range (n + 1), (-1 : ℤ) ^ j * ((2 * n + 1).choose j : ℤ) * ((2 * n + 1 - j).choose jr : ℤ) * (j.choose js : ℤ) =
    if js ≤ n then (-1 : ℤ) ^ n * ((2 * n + 1).choose js : ℤ) * ((2 * n + 1 - js).choose jr : ℤ) * ((2 * n - jr - js).choose (n - js) : ℤ) else 0 := by
  by_cases hjs_n : js ≤ n
  · rw [if_pos hjs_n]
    calc ∑ j ∈ range (n + 1), (-1 : ℤ) ^ j * ((2 * n + 1).choose j : ℤ) * ((2 * n + 1 - j).choose jr : ℤ) * (j.choose js : ℤ)
      _ = ∑ j ∈ range (n + 1), if js ≤ j then (-1 : ℤ) ^ j * (((2 * n + 1).choose js : ℤ) * ((2 * n + 1 - js).choose jr : ℤ) * ((2 * n + 1 - js - jr).choose (j - js) : ℤ)) else 0 := by
        apply sum_congr rfl
        intro j hj
        split_ifs with hjs
        · have hj_q : j ≤ 2 * n + 1 := by
            have : j < n + 1 := mem_range.mp hj
            omega
          have h_id := choose_mul_choose_mul_choose (2 * n + 1) j jr js hjs hj_q
          have h_id_z : ((2 * n + 1).choose j : ℤ) * ((2 * n + 1 - j).choose jr : ℤ) * (j.choose js : ℤ) =
              ((2 * n + 1).choose js : ℤ) * ((2 * n + 1 - js).choose jr : ℤ) * ((2 * n + 1 - js - jr).choose (j - js) : ℤ) := by
            exact_mod_cast h_id
          calc (-1 : ℤ) ^ j * ((2 * n + 1).choose j : ℤ) * ((2 * n + 1 - j).choose jr : ℤ) * (j.choose js : ℤ)
            _ = (-1 : ℤ) ^ j * (((2 * n + 1).choose j : ℤ) * ((2 * n + 1 - j).choose jr : ℤ) * (j.choose js : ℤ)) := by ring
            _ = (-1 : ℤ) ^ j * (((2 * n + 1).choose js : ℤ) * ((2 * n + 1 - js).choose jr : ℤ) * ((2 * n + 1 - js - jr).choose (j - js) : ℤ)) := by rw [h_id_z]
        · have : j.choose js = 0 := Nat.choose_eq_zero_of_lt (not_le.mp hjs)
          push_cast at this ⊢
          rw [this]; ring
      _ = ∑ j ∈ range (n + 1), if js ≤ j then (-1 : ℤ) ^ j * ((2 * n + 1).choose js : ℤ) * ((2 * n + 1 - js).choose jr : ℤ) * ((2 * n + 1 - js - jr).choose (j - js) : ℤ) else 0 := by
        apply sum_congr rfl; intro j hj; split_ifs; ring; rfl
      _ = (-1 : ℤ) ^ n * ((2 * n + 1).choose js : ℤ) * ((2 * n + 1 - js).choose jr : ℤ) * ((2 * n - jr - js).choose (n - js) : ℤ) := by
        have hjs_le : js ≤ n + 1 := by omega
        rw [sum_range_add_split n js hjs_le]
        have h_zero : (∑ j ∈ range js, if js ≤ j then (-1 : ℤ) ^ j * ((2 * n + 1).choose js : ℤ) * ((2 * n + 1 - js).choose jr : ℤ) * ((2 * n + 1 - js - jr).choose (j - js) : ℤ) else 0) = 0 := by
          apply sum_eq_zero
          intro j hj
          have : ¬(js ≤ j) := by
            have : j < js := mem_range.mp hj
            omega
          rw [if_neg this]
        rw [h_zero, zero_add]
        have h_shift : (∑ j ∈ range (n + 1 - js), if js ≤ js + j then (-1 : ℤ) ^ (js + j) * ((2 * n + 1).choose js : ℤ) * ((2 * n + 1 - js).choose jr : ℤ) * ((2 * n + 1 - js - jr).choose (js + j - js) : ℤ) else 0) =
            ∑ j ∈ range (n + 1 - js), (-1 : ℤ) ^ (js + j) * ((2 * n + 1).choose js : ℤ) * ((2 * n + 1 - js).choose jr : ℤ) * ((2 * n + 1 - js - jr).choose j : ℤ) := by
          apply sum_congr rfl
          intro j _
          have : js ≤ js + j := Nat.le_add_right _ _
          rw [if_pos this]
          congr 3
          omega
        rw [h_shift]
        have h_const : ∑ j ∈ range (n + 1 - js), (-1 : ℤ) ^ (js + j) * ((2 * n + 1).choose js : ℤ) * ((2 * n + 1 - js).choose jr : ℤ) * ((2 * n + 1 - js - jr).choose j : ℤ) =
            (-1 : ℤ) ^ js * ((2 * n + 1).choose js : ℤ) * ((2 * n + 1 - js).choose jr : ℤ) * ∑ j ∈ range (n + 1 - js), (-1 : ℤ) ^ j * ((2 * n + 1 - js - jr).choose j : ℤ) := by
          calc ∑ j ∈ range (n + 1 - js), (-1 : ℤ) ^ (js + j) * ((2 * n + 1).choose js : ℤ) * ((2 * n + 1 - js).choose jr : ℤ) * ((2 * n + 1 - js - jr).choose j : ℤ)
            _ = ∑ j ∈ range (n + 1 - js), (-1 : ℤ) ^ js * ((2 * n + 1).choose js : ℤ) * ((2 * n + 1 - js).choose jr : ℤ) * ((-1 : ℤ) ^ j * ((2 * n + 1 - js - jr).choose j : ℤ)) := by
              apply sum_congr rfl
              intro j _
              rw [pow_add]
              ring
            _ = (-1 : ℤ) ^ js * ((2 * n + 1).choose js : ℤ) * ((2 * n + 1 - js).choose jr : ℤ) * ∑ j ∈ range (n + 1 - js), (-1 : ℤ) ^ j * ((2 * n + 1 - js - jr).choose j : ℤ) := by
              rw [← mul_sum]
        rw [h_const]
        have h_pas := partial_alternating_binom_sum (n - js) (2 * n + 1 - js - jr) (by omega)
        have h_range : n + 1 - js = n - js + 1 := by omega
        rw [h_range]
        rw [h_pas]
        have h_pow : (-1 : ℤ) ^ js * (-1 : ℤ) ^ (n - js) = (-1 : ℤ) ^ n := by
          rw [← pow_add]
          congr 1
          omega
        have h_bin : 2 * n + 1 - js - jr - 1 = 2 * n - jr - js := by omega
        rw [h_bin]
        calc (-1 : ℤ) ^ js * ((2 * n + 1).choose js : ℤ) * ((2 * n + 1 - js).choose jr : ℤ) * ((-1 : ℤ) ^ (n - js) * ((2 * n - jr - js).choose (n - js) : ℤ))
          _ = ((-1 : ℤ) ^ js * (-1 : ℤ) ^ (n - js)) * ((2 * n + 1).choose js : ℤ) * ((2 * n + 1 - js).choose jr : ℤ) * ((2 * n - jr - js).choose (n - js) : ℤ) := by ring
          _ = (-1 : ℤ) ^ n * ((2 * n + 1).choose js : ℤ) * ((2 * n + 1 - js).choose jr : ℤ) * ((2 * n - jr - js).choose (n - js) : ℤ) := by rw [h_pow]
  · rw [if_neg hjs_n]
    apply sum_eq_zero
    intro j hj
    have h1 : j < n + 1 := mem_range.mp hj
    have h2 : j < js := by omega
    have h3 : j.choose js = 0 := Nat.choose_eq_zero_of_lt h2
    push_cast at h3 ⊢
    rw [h3]; ring


-- Step 4b: E is symmetric under swapping its first two arguments up to a sign.
-- Proved by reindexing r → m-r and noting that the sign factor changes.
@[category API, AMS 5]
private lemma E_swap (jr js m : ℕ) : E jr js m = (-1 : ℤ) ^ m * E js jr m := by
  simp only [E, mul_sum]
  rw [show ∑ r ∈ range (m + 1),
      (-1 : ℤ) ^ (m - r) * ↑(m.choose r) *
        (↑(Nat.stirlingSecond r jr) * ↑jr !) *
        (↑(Nat.stirlingSecond (m - r) js) * ↑js !) =
      ∑ r ∈ range (m + 1),
      (-1 : ℤ) ^ r * ↑(m.choose r) *
        (↑(Nat.stirlingSecond (m - r) jr) * ↑jr !) *
        (↑(Nat.stirlingSecond r js) * ↑js !) from by
    rw [← Finset.sum_range_reflect]
    apply sum_congr rfl
    intro r hr
    rw [Finset.mem_range] at hr
    have h1 : m + 1 - 1 - r = m - r := by omega
    have h2 : m - (m - r) = r := by omega
    rw [h1, h2]
    have h3 : m.choose (m - r) = m.choose r := Nat.choose_symm (by omega)
    rw [h3]]
  apply sum_congr rfl
  intro r hr
  rw [Finset.mem_range] at hr
  have h_sign : (-1 : ℤ) ^ m * (-1 : ℤ) ^ (m - r) = (-1 : ℤ) ^ r := by
    have h1 : (-1 : ℤ) ^ (m - r) * (-1 : ℤ) ^ r = (-1 : ℤ) ^ m := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    have neg_one_pow_cases : ∀ k, (-1 : ℤ) ^ k = 1 ∨ (-1 : ℤ) ^ k = -1 := by
      intro k
      rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
      · left; rw [hj]; ring_nf; rw [mul_comm, pow_mul]; simp
      · right; rw [hj, pow_succ]; ring_nf; rw [mul_comm, pow_mul]; simp
    rcases neg_one_pow_cases (m - r) with hmr | hmr <;>
      rcases neg_one_pow_cases m with hm | hm <;>
        rcases neg_one_pow_cases r with hrr | hrr <;>
          simp_all
  calc (-1 : ℤ) ^ r * ↑(m.choose r) *
        (↑(Nat.stirlingSecond (m - r) jr) * ↑jr !) *
        (↑(Nat.stirlingSecond r js) * ↑js !)
      = ((-1 : ℤ) ^ m * (-1 : ℤ) ^ (m - r)) * ↑(m.choose r) *
        (↑(Nat.stirlingSecond (m - r) jr) * ↑jr !) *
        (↑(Nat.stirlingSecond r js) * ↑js !) := by rw [h_sign]
    _ = (-1 : ℤ) ^ m *
        ((-1 : ℤ) ^ (m - r) * ↑(m.choose r) *
        (↑(Nat.stirlingSecond r js) * ↑js !) *
        (↑(Nat.stirlingSecond (m - r) jr) * ↑jr !)) := by ring

-- Step 4c: For even exponent, E is fully symmetric.
@[category API, AMS 5]
private lemma E_symm_even (jr js n : ℕ) : E jr js (2 * n) = E js jr (2 * n) := by
  rw [E_swap]; simp [pow_mul]

@[category API, AMS 5]
private lemma sum_alternating_binom (M : ℕ) :
    ∑ v ∈ range (M + 1), (-1 : ℤ) ^ v * (M.choose v : ℤ) = if M = 0 then 1 else 0 := by
  cases M
  · simp
  · rename_i M'
    have hm : 1 ≤ M' + 1 := by omega
    rw [if_neg (by omega)]
    have h_pas := partial_alternating_binom_sum (M' + 1) (M' + 1) hm
    rw [h_pas]
    have h_sub : M' + 1 - 1 = M' := by omega
    rw [h_sub]
    have h_zero : M'.choose (M' + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h_zero]
    ring

@[category API, AMS 5]
private lemma collapse_inner (N a : ℕ) :
    ∑ u ∈ range (N + 1), (-1 : ℤ) ^ (u - a) * (N.choose u : ℤ) * (u.choose a : ℤ) =
    if a = N then 1 else 0 := by
  by_cases ha : a ≤ N
  · calc ∑ u ∈ range (N + 1), (-1 : ℤ) ^ (u - a) * (N.choose u : ℤ) * (u.choose a : ℤ)
      _ = ∑ u ∈ range (N + 1), if a ≤ u then (-1 : ℤ) ^ (u - a) * ((N.choose a : ℤ) * ((N - a).choose (u - a) : ℤ)) else 0 := by
        apply sum_congr rfl
        intro u hu
        split_ifs with hau
        · have h_sub : u - a ≤ N - a := by
            have : u < N + 1 := mem_range.mp hu
            omega
          have h_id : N.choose u * u.choose a = N.choose a * (N - a).choose (u - a) := @Nat.choose_mul N u a hau
          have h_id_z : (N.choose u : ℤ) * (u.choose a : ℤ) = (N.choose a : ℤ) * ((N - a).choose (u - a) : ℤ) := by exact_mod_cast h_id
          calc (-1 : ℤ) ^ (u - a) * (N.choose u : ℤ) * (u.choose a : ℤ)
            _ = (-1 : ℤ) ^ (u - a) * ((N.choose u : ℤ) * (u.choose a : ℤ)) := by ring
            _ = (-1 : ℤ) ^ (u - a) * ((N.choose a : ℤ) * ((N - a).choose (u - a) : ℤ)) := by rw [h_id_z]
        · have : u.choose a = 0 := Nat.choose_eq_zero_of_lt (not_le.mp hau)
          push_cast at this ⊢
          rw [this]
          ring
      _ = ∑ u ∈ range (N + 1), if a ≤ u then (N.choose a : ℤ) * ((-1 : ℤ) ^ (u - a) * ((N - a).choose (u - a) : ℤ)) else 0 := by
        apply sum_congr rfl; intro u hu; split_ifs; ring; rfl
      _ = (N.choose a : ℤ) * ∑ v ∈ range (N + 1 - a), (-1 : ℤ) ^ v * ((N - a).choose v : ℤ) := by
        have h_sum : (∑ u ∈ range (N + 1), if a ≤ u then (N.choose a : ℤ) * ((-1 : ℤ) ^ (u - a) * ((N - a).choose (u - a) : ℤ)) else 0) =
            (∑ u ∈ range a, if a ≤ u then (N.choose a : ℤ) * ((-1 : ℤ) ^ (u - a) * ((N - a).choose (u - a) : ℤ)) else 0) +
            ∑ u ∈ range (N + 1 - a), if a ≤ a + u then (N.choose a : ℤ) * ((-1 : ℤ) ^ (a + u - a) * ((N - a).choose (a + u - a) : ℤ)) else 0 := by
          have : N + 1 = a + (N + 1 - a) := by omega
          nth_rw 1 [this]
          exact sum_range_add _ a (N + 1 - a)
        rw [h_sum]
        have h_zero : (∑ u ∈ range a, if a ≤ u then (N.choose a : ℤ) * ((-1 : ℤ) ^ (u - a) * ((N - a).choose (u - a) : ℤ)) else 0) = 0 := by
          apply sum_eq_zero
          intro u hu
          have : ¬(a ≤ u) := by
            have : u < a := mem_range.mp hu
            omega
          rw [if_neg this]
        rw [h_zero, zero_add]
        have h_shift : (∑ u ∈ range (N + 1 - a), if a ≤ a + u then (N.choose a : ℤ) * ((-1 : ℤ) ^ (a + u - a) * ((N - a).choose (a + u - a) : ℤ)) else 0) =
            ∑ u ∈ range (N + 1 - a), (N.choose a : ℤ) * ((-1 : ℤ) ^ u * ((N - a).choose u : ℤ)) := by
          apply sum_congr rfl
          intro j _
          have : a ≤ a + j := by omega
          rw [if_pos this]
          have h_aj : a + j - a = j := by omega
          rw [h_aj]
        rw [h_shift, ← mul_sum]
      _ = (N.choose a : ℤ) * (if N - a = 0 then 1 else 0) := by
        have h_bound : N + 1 - a = N - a + 1 := by omega
        rw [h_bound, sum_alternating_binom]
      _ = if a = N then 1 else 0 := by
        split_ifs with h1 h2 h3
        · have : N = a := by omega
          subst this
          simp
        · omega
        · omega
        · have : N - a ≠ 0 := by omega
          have : a ≠ N := by omega
          ring
  · rw [if_neg (by omega)]
    apply sum_eq_zero
    intro u hu
    have : u.choose a = 0 := by
      apply Nat.choose_eq_zero_of_lt
      have : u < N + 1 := mem_range.mp hu
      omega
    push_cast at this ⊢
    rw [this]
    ring

-- Step 4d: The key derivation showing a(n) = (-1)^n * D(2n+1).
-- This is proved by:
--   (i) expanding (q-2j)^{2n} = ((q-j)-j)^{2n} via binomial theorem,
--   (ii) applying the Stirling IE to convert each power to falling factorials,
--   (iii) evaluating the inner j-sum using two applications of Vandermonde
--         (Nat.choose_mul) and the partial_alternating_binom_sum,
--   (iv) recognizing the resulting triple sum as E(k1,k2,2n), and
--   (v) renaming summation variables to match D.

@[category API, AMS 5]
private lemma E_eq_zero_of_gt (jr js m : ℕ) (h : m < jr + js) : E jr js m = 0 := by
  unfold E
  apply Finset.sum_eq_zero
  intro r hr
  rw [Finset.mem_range] at hr
  by_cases h1 : r < jr
  · have : Nat.stirlingSecond r jr = 0 := Nat.stirlingSecond_eq_zero_of_lt h1
    rw [this]
    push_cast
    ring
  · have h2 : m - r < js := by omega
    have : Nat.stirlingSecond (m - r) js = 0 := Nat.stirlingSecond_eq_zero_of_lt h2
    rw [this]
    push_cast
    ring


@[category API, AMS 5]
private lemma swap_four_sums
    (A B : ℕ)
    (f : ℕ → ℕ → ℤ)
    (g : ℕ → ℕ → ℤ)
    (h : ℕ → ℕ → ℤ) :
    (∑ jr ∈ range A, ∑ js ∈ range B, ∑ a ∈ range A, ∑ b ∈ range B,
      f jr a * g js b * h a b) =
    ∑ a ∈ range A, ∑ b ∈ range B,
      (∑ jr ∈ range A, f jr a) * (∑ js ∈ range B, g js b) * h a b := by
  have h1 : (∑ jr ∈ range A, ∑ js ∈ range B, ∑ a ∈ range A, ∑ b ∈ range B, f jr a * g js b * h a b) =
      ∑ jr ∈ range A, ∑ a ∈ range A, ∑ js ∈ range B, ∑ b ∈ range B, f jr a * g js b * h a b := by
    apply sum_congr rfl; intro jr _
    rw [sum_comm]
  rw [h1]
  have h2 : (∑ jr ∈ range A, ∑ a ∈ range A, ∑ js ∈ range B, ∑ b ∈ range B, f jr a * g js b * h a b) =
      ∑ a ∈ range A, ∑ jr ∈ range A, ∑ js ∈ range B, ∑ b ∈ range B, f jr a * g js b * h a b := by
    rw [sum_comm]
  rw [h2]
  have h3 : (∑ a ∈ range A, ∑ jr ∈ range A, ∑ js ∈ range B, ∑ b ∈ range B, f jr a * g js b * h a b) =
      ∑ a ∈ range A, ∑ jr ∈ range A, ∑ b ∈ range B, ∑ js ∈ range B, f jr a * g js b * h a b := by
    apply sum_congr rfl; intro a _
    apply sum_congr rfl; intro jr _
    rw [sum_comm]
  rw [h3]
  have h4 : (∑ a ∈ range A, ∑ jr ∈ range A, ∑ b ∈ range B, ∑ js ∈ range B, f jr a * g js b * h a b) =
      ∑ a ∈ range A, ∑ b ∈ range B, ∑ jr ∈ range A, ∑ js ∈ range B, f jr a * g js b * h a b := by
    apply sum_congr rfl; intro a _
    rw [sum_comm]
  rw [h4]
  apply sum_congr rfl; intro a _
  apply sum_congr rfl; intro b _
  have h5 : (∑ jr ∈ range A, ∑ js ∈ range B, f jr a * g js b * h a b) =
      ∑ jr ∈ range A, ∑ js ∈ range B, f jr a * (g js b * h a b) := by
    apply sum_congr rfl; intro jr _
    apply sum_congr rfl; intro js _
    ring
  rw [h5]
  have h6 : (∑ jr ∈ range A, ∑ js ∈ range B, f jr a * (g js b * h a b)) =
      ∑ jr ∈ range A, f jr a * (∑ js ∈ range B, g js b * h a b) := by
    apply sum_congr rfl; intro jr _
    rw [mul_sum]
  rw [h6]
  have h7 : (∑ jr ∈ range A, f jr a * (∑ js ∈ range B, g js b * h a b)) =
      (∑ jr ∈ range A, f jr a) * (∑ js ∈ range B, g js b * h a b) := by
    rw [sum_mul]
  rw [h7]
  have h8 : (∑ js ∈ range B, g js b) * h a b = ∑ js ∈ range B, g js b * h a b := by
    rw [sum_mul]
  rw [← h8]
  ring


@[category API, AMS 5]
private lemma pow_eq_sum_E_closed (n j : ℕ) (hj : j ≤ 2 * n + 1) :
    ((2 * n + 1 - 2 * j : ℤ) ^ (2 * n)) =
    ∑ jr ∈ Finset.range (2 * n + 1 - j + 1), ∑ js ∈ Finset.range (j + 1),
      ((2 * n + 1 - j).choose jr : ℤ) * (j.choose js : ℤ) * (∑ a ∈ Finset.range (jr + 1), ∑ b ∈ Finset.range (js + 1), (-1 : ℤ) ^ (jr - a + (js - b)) * (jr.choose a : ℤ) * (js.choose b : ℤ) * ((a : ℤ) - b) ^ (2 * n)) := by
  have hE : ∀ jr ∈ Finset.range (2 * n + 1 - j + 1), ∀ js ∈ Finset.range (j + 1), (∑ a ∈ Finset.range (jr + 1), ∑ b ∈ Finset.range (js + 1), (-1 : ℤ) ^ (jr - a + (js - b)) * (jr.choose a : ℤ) * (js.choose b : ℤ) * ((a : ℤ) - b) ^ (2 * n)) =
      ∑ a ∈ Finset.range (2 * n + 1 - j + 1), ∑ b ∈ Finset.range (j + 1),
        if a ≤ jr ∧ b ≤ js then
          (-1 : ℤ) ^ (jr - a + (js - b)) * (jr.choose a : ℤ) * (js.choose b : ℤ) * ((a : ℤ) - b) ^ (2 * n)
        else (0 : ℤ) := by
    intro jr hjr js hjs
    rw [mem_range] at hjr hjs
     
    have h_a : ∑ a ∈ Finset.range (jr + 1), ∑ b ∈ Finset.range (js + 1), (-1 : ℤ) ^ (jr - a + (js - b)) * (jr.choose a : ℤ) * (js.choose b : ℤ) * ((a : ℤ) - (b : ℤ)) ^ (2 * n) =
        ∑ a ∈ Finset.range (2 * n + 1 - j + 1), if a ≤ jr then (∑ b ∈ Finset.range (js + 1), (-1 : ℤ) ^ (jr - a + (js - b)) * (jr.choose a : ℤ) * (js.choose b : ℤ) * ((a : ℤ) - (b : ℤ)) ^ (2 * n)) else (0 : ℤ) := by
      have h_split : Finset.range (2 * n + 1 - j + 1) = Finset.range (jr + 1) ∪ Ico (jr + 1) (2 * n + 1 - j + 1) := by
        ext x; rw [mem_union, mem_range, mem_range, mem_Ico]; omega
      rw [h_split, sum_union (by rw [disjoint_iff_ne]; intro x hx y hy; rw [mem_range] at hx; rw [mem_Ico] at hy; omega)]
      have h1 : (∑ a ∈ Finset.range (jr + 1), if a ≤ jr then (∑ b ∈ Finset.range (js + 1), (-1 : ℤ) ^ (jr - a + (js - b)) * (jr.choose a : ℤ) * (js.choose b : ℤ) * ((a : ℤ) - (b : ℤ)) ^ (2 * n)) else (0 : ℤ)) =
          ∑ a ∈ Finset.range (jr + 1), ∑ b ∈ Finset.range (js + 1), (-1 : ℤ) ^ (jr - a + (js - b)) * (jr.choose a : ℤ) * (js.choose b : ℤ) * ((a : ℤ) - (b : ℤ)) ^ (2 * n) := by
        apply sum_congr rfl
        intro x hx; rw [mem_range] at hx; rw [if_pos (by omega)]
      rw [h1]
      have h2 : (∑ x ∈ Ico (jr + 1) (2 * n + 1 - j + 1), if x ≤ jr then (∑ b ∈ Finset.range (js + 1), (-1 : ℤ) ^ (jr - x + (js - b)) * (jr.choose x : ℤ) * (js.choose b : ℤ) * ((x : ℤ) - (b : ℤ)) ^ (2 * n)) else (0 : ℤ)) = 0 := by
        apply sum_eq_zero
        intro x hx; rw [mem_Ico] at hx; rw [if_neg (by omega)]
      rw [h2, add_zero]
    rw [h_a]
    apply sum_congr rfl
    intro a _
    split_ifs with ha
    · have h_split : Finset.range (j + 1) = Finset.range (js + 1) ∪ Ico (js + 1) (j + 1) := by
        ext x; rw [mem_union, mem_range, mem_range, mem_Ico]; omega
      rw [h_split, sum_union (by rw [disjoint_iff_ne]; intro x hx y hy; rw [mem_range] at hx; rw [mem_Ico] at hy; omega)]
      have h1 : (∑ b ∈ Finset.range (js + 1), if a ≤ jr ∧ b ≤ js then ((-1 : ℤ) ^ (jr - a + (js - b)) * (jr.choose a : ℤ) * (js.choose b : ℤ) * ((a : ℤ) - (b : ℤ)) ^ (2 * n)) else (0 : ℤ)) =
          ∑ b ∈ Finset.range (js + 1), (-1 : ℤ) ^ (jr - a + (js - b)) * (jr.choose a : ℤ) * (js.choose b : ℤ) * ((a : ℤ) - (b : ℤ)) ^ (2 * n) := by
        apply sum_congr rfl
        intro x hx; rw [mem_range] at hx; rw [if_pos (by omega)]
      have h2 : (∑ x ∈ Ico (js + 1) (j + 1), if a ≤ jr ∧ x ≤ js then ((-1 : ℤ) ^ (jr - a + (js - x)) * (jr.choose a : ℤ) * (js.choose x : ℤ) * ((a : ℤ) - (x : ℤ)) ^ (2 * n)) else (0 : ℤ)) = 0 := by
        apply sum_eq_zero
        intro x hx; rw [mem_Ico] at hx; rw [if_neg (by omega)]
      rw [h1, h2, add_zero]
    · symm
      apply sum_eq_zero
      intro x _
      rw [if_neg (by omega)]

  -- Apply hE
  have hE2 : ∑ jr ∈ Finset.range (2 * n + 1 - j + 1), ∑ js ∈ Finset.range (j + 1),
      ((2 * n + 1 - j).choose jr : ℤ) * (j.choose js : ℤ) * (∑ a ∈ Finset.range (jr + 1), ∑ b ∈ Finset.range (js + 1), (-1 : ℤ) ^ (jr - a + (js - b)) * (jr.choose a : ℤ) * (js.choose b : ℤ) * ((a : ℤ) - b) ^ (2 * n)) =
      ∑ jr ∈ Finset.range (2 * n + 1 - j + 1), ∑ js ∈ Finset.range (j + 1),
        ((2 * n + 1 - j).choose jr : ℤ) * (j.choose js : ℤ) *
        ∑ a ∈ Finset.range (2 * n + 1 - j + 1), ∑ b ∈ Finset.range (j + 1),
          if a ≤ jr ∧ b ≤ js then
            (-1 : ℤ) ^ (jr - a + (js - b)) * (jr.choose a : ℤ) * (js.choose b : ℤ) * ((a : ℤ) - b) ^ (2 * n)
          else (0 : ℤ) := by
    apply sum_congr rfl
    intro jr hjr
    apply sum_congr rfl
    intro js hjs
    rw [hE jr hjr js hjs]

  rw [hE2]
  have hE3 : (∑ jr ∈ Finset.range (2 * n + 1 - j + 1), ∑ js ∈ Finset.range (j + 1),
        ((2 * n + 1 - j).choose jr : ℤ) * (j.choose js : ℤ) *
        ∑ a ∈ Finset.range (2 * n + 1 - j + 1), ∑ b ∈ Finset.range (j + 1),
          if a ≤ jr ∧ b ≤ js then
            (-1 : ℤ) ^ (jr - a + (js - b)) * (jr.choose a : ℤ) * (js.choose b : ℤ) * ((a : ℤ) - b) ^ (2 * n)
          else (0 : ℤ)) =
      ∑ jr ∈ Finset.range (2 * n + 1 - j + 1), ∑ js ∈ Finset.range (j + 1),
        ∑ a ∈ Finset.range (2 * n + 1 - j + 1), ∑ b ∈ Finset.range (j + 1),
          ((-1 : ℤ) ^ (jr - a) * ((2 * n + 1 - j).choose jr : ℤ) * (jr.choose a : ℤ)) *
          ((-1 : ℤ) ^ (js - b) * (j.choose js : ℤ) * (js.choose b : ℤ)) * ((a : ℤ) - b) ^ (2 * n) := by
    apply sum_congr rfl
    intro jr hjr
    apply sum_congr rfl
    intro js hjs
    rw [mul_sum]
    apply sum_congr rfl
    intro a ha
    rw [mul_sum]
    apply sum_congr rfl
    intro b hb
    split_ifs with hab
    · rcases hab with ⟨har, hbs⟩
      have h_pow : (-1 : ℤ) ^ (jr - a + (js - b)) = (-1 : ℤ) ^ (jr - a) * (-1 : ℤ) ^ (js - b) := by
        rw [pow_add]
      rw [h_pow]
      ring
    · have h_zero : (jr.choose a : ℤ) = 0 ∨ (js.choose b : ℤ) = 0 := by
        rw [not_and_or, not_le, not_le] at hab
        rcases hab with ha | hb
        · left; rw [Nat.choose_eq_zero_of_lt ha]; simp
        · right; rw [Nat.choose_eq_zero_of_lt hb]; simp
      rcases h_zero with h | h
      · rw [h]; ring
      · rw [h]; ring

  rw [hE3]
  have h_swap : (∑ jr ∈ Finset.range (2 * n + 1 - j + 1), ∑ js ∈ Finset.range (j + 1),
        ∑ a ∈ Finset.range (2 * n + 1 - j + 1), ∑ b ∈ Finset.range (j + 1),
          ((-1 : ℤ) ^ (jr - a) * ((2 * n + 1 - j).choose jr : ℤ) * (jr.choose a : ℤ)) *
          ((-1 : ℤ) ^ (js - b) * (j.choose js : ℤ) * (js.choose b : ℤ)) * ((a : ℤ) - b) ^ (2 * n)) =
      ∑ a ∈ Finset.range (2 * n + 1 - j + 1), ∑ b ∈ Finset.range (j + 1),
        (∑ jr ∈ Finset.range (2 * n + 1 - j + 1), (-1 : ℤ) ^ (jr - a) * ((2 * n + 1 - j).choose jr : ℤ) * (jr.choose a : ℤ)) *
        (∑ js ∈ Finset.range (j + 1), (-1 : ℤ) ^ (js - b) * (j.choose js : ℤ) * (js.choose b : ℤ)) * ((a : ℤ) - b) ^ (2 * n) := by
    apply swap_four_sums
      (2 * n + 1 - j + 1)
      (j + 1)
      (fun jr a => (-1 : ℤ) ^ (jr - a) * ((2 * n + 1 - j).choose jr : ℤ) * (jr.choose a : ℤ))
      (fun js b => (-1 : ℤ) ^ (js - b) * (j.choose js : ℤ) * (js.choose b : ℤ))
      (fun a b => ((a : ℤ) - b) ^ (2 * n))

  rw [h_swap]
  have h_collapse_a : ∀ a ∈ Finset.range (2 * n + 1 - j + 1),
      (∑ jr ∈ Finset.range (2 * n + 1 - j + 1), (-1 : ℤ) ^ (jr - a) * ((2 * n + 1 - j).choose jr : ℤ) * (jr.choose a : ℤ)) =
      if a = 2 * n + 1 - j then 1 else 0 := by
    intro a _
    apply collapse_inner
  have h_collapse_b : ∀ b ∈ Finset.range (j + 1),
      (∑ js ∈ Finset.range (j + 1), (-1 : ℤ) ^ (js - b) * (j.choose js : ℤ) * (js.choose b : ℤ)) =
      if b = j then 1 else 0 := by
    intro b _
    apply collapse_inner
  
  have h_final : (∑ a ∈ Finset.range (2 * n + 1 - j + 1), ∑ b ∈ Finset.range (j + 1),
        (∑ jr ∈ Finset.range (2 * n + 1 - j + 1), (-1 : ℤ) ^ (jr - a) * ((2 * n + 1 - j).choose jr : ℤ) * (jr.choose a : ℤ)) *
        (∑ js ∈ Finset.range (j + 1), (-1 : ℤ) ^ (js - b) * (j.choose js : ℤ) * (js.choose b : ℤ)) * ((a : ℤ) - b) ^ (2 * n)) = 
      (2 * n + 1 - 2 * j : ℤ) ^ (2 * n) := by
    -- We can simplify this sum to the single term where a = 2*n+1-j and b = j
    -- by using the fact that all other terms are 0.
    have h_a_sum : (∑ a ∈ Finset.range (2 * n + 1 - j + 1), ∑ b ∈ Finset.range (j + 1),
          (∑ jr ∈ Finset.range (2 * n + 1 - j + 1), (-1 : ℤ) ^ (jr - a) * ((2 * n + 1 - j).choose jr : ℤ) * (jr.choose a : ℤ)) *
          (∑ js ∈ Finset.range (j + 1), (-1 : ℤ) ^ (js - b) * (j.choose js : ℤ) * (js.choose b : ℤ)) * ((a : ℤ) - b) ^ (2 * n)) =
        ∑ a ∈ Finset.range (2 * n + 1 - j + 1), ∑ b ∈ Finset.range (j + 1),
          (if a = 2 * n + 1 - j then (1 : ℤ) else 0) *
          (if b = j then (1 : ℤ) else 0) * ((a : ℤ) - b) ^ (2 * n) := by
      apply sum_congr rfl; intro a ha
      apply sum_congr rfl; intro b hb
      rw [h_collapse_a a ha, h_collapse_b b hb]
    rw [h_a_sum]
    have h_a_sum2 : (∑ a ∈ Finset.range (2 * n + 1 - j + 1), ∑ b ∈ Finset.range (j + 1),
          (if a = 2 * n + 1 - j then (1 : ℤ) else 0) *
          (if b = j then (1 : ℤ) else 0) * ((a : ℤ) - b) ^ (2 * n)) =
        ∑ a ∈ Finset.range (2 * n + 1 - j + 1), if a = 2 * n + 1 - j then 
          (∑ b ∈ Finset.range (j + 1), (if b = j then (1 : ℤ) else 0) * ((a : ℤ) - b) ^ (2 * n)) else 0 := by
      apply sum_congr rfl; intro a _
      split_ifs with ha
      · rw [ha]
        apply sum_congr rfl; intro b _
        ring
      · apply sum_eq_zero; intro b _
        ring
    rw [h_a_sum2]
    have h_a_sum3 : (∑ a ∈ Finset.range (2 * n + 1 - j + 1), if a = 2 * n + 1 - j then 
          (∑ b ∈ Finset.range (j + 1), (if b = j then (1 : ℤ) else 0) * ((a : ℤ) - b) ^ (2 * n)) else 0) =
        ∑ b ∈ Finset.range (j + 1), (if b = j then (1 : ℤ) else 0) * ((2 * n + 1 - j : ℤ) - b) ^ (2 * n) := by
      have h_in : 2 * n + 1 - j ∈ Finset.range (2 * n + 1 - j + 1) := by rw [mem_range]; omega
      rw [sum_eq_single (2 * n + 1 - j)]
      · rw [if_pos rfl]
        apply sum_congr rfl
        intro b hb
        congr 2
        omega
      · intro x hx hnx
        rw [if_neg hnx]
      · intro h_nin
        exfalso
        exact h_nin h_in
    rw [h_a_sum3]
    have h_b_sum : (∑ b ∈ Finset.range (j + 1), (if b = j then (1 : ℤ) else 0) * ((2 * n + 1 - j : ℤ) - b) ^ (2 * n)) =
        ((2 * n + 1 - j : ℤ) - j) ^ (2 * n) := by
      have h_in : j ∈ Finset.range (j + 1) := by rw [mem_range]; omega
      rw [sum_eq_single j]
      · rw [if_pos rfl]
        ring
      · intro x hx hnx
        rw [if_neg hnx]
        ring
      · intro h_nin
        exfalso
        exact h_nin h_in
    rw [h_b_sum]
    congr 1
    omega
  rw [← h_final]



@[category API, AMS 5]
private lemma sum_triple_swap (n : ℕ) (F : ℕ → ℕ → ℕ → ℤ) :
    (∑ j ∈ Finset.range (n + 1), ∑ jr ∈ Finset.range (2 * n + 1 - j + 1), ∑ js ∈ Finset.range (j + 1),
      ((2 * n + 1 - j).choose jr : ℤ) * (j.choose js : ℤ) * F j jr js) =
    ∑ jr ∈ Finset.range (2 * n + 2), ∑ js ∈ Finset.range (2 * n + 2), ∑ j ∈ Finset.range (n + 1),
      ((2 * n + 1 - j).choose jr : ℤ) * (j.choose js : ℤ) * F j jr js := by
  have h1 : ∀ j ∈ Finset.range (n + 1),
      (∑ jr ∈ Finset.range (2 * n + 1 - j + 1), ∑ js ∈ Finset.range (j + 1),
        ((2 * n + 1 - j).choose jr : ℤ) * (j.choose js : ℤ) * F j jr js) =
      ∑ jr ∈ Finset.range (2 * n + 2), ∑ js ∈ Finset.range (2 * n + 2),
        ((2 * n + 1 - j).choose jr : ℤ) * (j.choose js : ℤ) * F j jr js := by
    intro j hj
    have hj_lt : j < n + 1 := mem_range.mp hj
    have h_jr_extend : ∑ jr ∈ Finset.range (2 * n + 1 - j + 1), ∑ js ∈ Finset.range (j + 1), ((2 * n + 1 - j).choose jr : ℤ) * (j.choose js : ℤ) * F j jr js =
        ∑ jr ∈ Finset.range (2 * n + 2), ∑ js ∈ Finset.range (j + 1), ((2 * n + 1 - j).choose jr : ℤ) * (j.choose js : ℤ) * F j jr js := by
      have h_bound : 2 * n + 1 - j + 1 ≤ 2 * n + 2 := by omega
      rw [← sum_range_add_sum_Ico _ h_bound]
      have h_zero : ∑ jr ∈ Ico (2 * n + 1 - j + 1) (2 * n + 2), ∑ js ∈ Finset.range (j + 1), ↑((2 * n + 1 - j).choose jr) * ↑(j.choose js) * F j jr js = 0 := by
        apply sum_eq_zero; intro jr hjr; rw [mem_Ico] at hjr
        have : (2 * n + 1 - j).choose jr = 0 := choose_eq_zero_of_lt (by omega)
        rw [this]; push_cast; simp
      rw [h_zero, add_zero]
    rw [h_jr_extend]
    apply sum_congr rfl
    intro jr _
    have h_js_extend : ∑ js ∈ Finset.range (j + 1), ((2 * n + 1 - j).choose jr : ℤ) * (j.choose js : ℤ) * F j jr js =
        ∑ js ∈ Finset.range (2 * n + 2), ((2 * n + 1 - j).choose jr : ℤ) * (j.choose js : ℤ) * F j jr js := by
      have h_bound : j + 1 ≤ 2 * n + 2 := by omega
      rw [← sum_range_add_sum_Ico _ h_bound]
      have h_zero : ∑ js ∈ Ico (j + 1) (2 * n + 2), ↑((2 * n + 1 - j).choose jr) * ↑(j.choose js) * F j jr js = 0 := by
        apply sum_eq_zero; intro js hjs; rw [mem_Ico] at hjs
        have : j.choose js = 0 := choose_eq_zero_of_lt (by omega)
        rw [this]; push_cast; simp
      rw [h_zero, add_zero]
    rw [h_js_extend]
  rw [sum_congr rfl h1]
  rw [sum_comm]
  apply sum_congr rfl
  intro jr _
  rw [sum_comm]



@[category API, AMS 5]
private lemma a_eq_a_alt (n : ℕ) :
    a n = ∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j * ((2 * n + 1).choose j : ℤ) * ((2 * n + 1 - 2 * j : ℤ) ^ (2 * n)) := by
  unfold a
  have h_rev : ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - i) * ↑((2 * n + 1).choose (n - i)) * (2 * ↑i + 1) ^ (2 * n) =
      ∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j * ↑((2 * n + 1).choose j) * ((2 * ↑n + 1 - 2 * ↑j) ^ (2 * n)) := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro j hj
    have h2 : (n + 1 - 1 - j : ℕ) = n - j := by omega
    have h3 : n - (n - j) = j := by
      have : j < n + 1 := Finset.mem_range.mp hj
      omega
    rw [h2, h3]
    have hj_le : j ≤ n := by
      have : j < n + 1 := Finset.mem_range.mp hj
      omega
    have h4 : (2 * ↑(n - j) + 1 : ℤ) = 2 * ↑n + 1 - 2 * ↑j := by
      zify [hj_le]
      ring
    rw [h4]
  exact h_rev


@[category API, AMS 5]
private lemma a_eq_neg_pow_D (n : ℕ) :
    a n = (-1 : ℤ) ^ n * D (2 * n + 1) := by
  rw [a_eq_a_alt]
  have h_subst : ∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j * ((2 * n + 1).choose j : ℤ) * ((2 * n + 1 - 2 * j : ℤ) ^ (2 * n)) =
      ∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j * ((2 * n + 1).choose j : ℤ) *
        ∑ jr ∈ Finset.range (2 * n + 1 - j + 1), ∑ js ∈ Finset.range (j + 1),
          ((2 * n + 1 - j).choose jr : ℤ) * (j.choose js : ℤ) * 
          (∑ a ∈ Finset.range (jr + 1), ∑ b ∈ Finset.range (js + 1), (-1 : ℤ) ^ (jr - a + (js - b)) * (jr.choose a : ℤ) * (js.choose b : ℤ) * ((a : ℤ) - b) ^ (2 * n)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_bound : j ≤ 2 * n + 1 := by
      have : j < n + 1 := Finset.mem_range.mp hj
      omega
    rw [pow_eq_sum_E_closed n j hj_bound]
  rw [h_subst]
  
  have h_E : ∀ jr js, (∑ a ∈ Finset.range (jr + 1), ∑ b ∈ Finset.range (js + 1), (-1 : ℤ) ^ (jr - a + (js - b)) * (jr.choose a : ℤ) * (js.choose b : ℤ) * ((a : ℤ) - b) ^ (2 * n)) = E jr js (2 * n) := by
    intro jr js
    exact (E_eq_E_closed jr js (2 * n)).symm
  have h_E_subst : (∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j * ((2 * n + 1).choose j : ℤ) *
        ∑ jr ∈ Finset.range (2 * n + 1 - j + 1), ∑ js ∈ Finset.range (j + 1),
          ((2 * n + 1 - j).choose jr : ℤ) * (j.choose js : ℤ) * 
          (∑ a ∈ Finset.range (jr + 1), ∑ b ∈ Finset.range (js + 1), (-1 : ℤ) ^ (jr - a + (js - b)) * (jr.choose a : ℤ) * (js.choose b : ℤ) * ((a : ℤ) - b) ^ (2 * n))) =
      ∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j * ((2 * n + 1).choose j : ℤ) *
        ∑ jr ∈ Finset.range (2 * n + 1 - j + 1), ∑ js ∈ Finset.range (j + 1),
          ((2 * n + 1 - j).choose jr : ℤ) * (j.choose js : ℤ) * E jr js (2 * n) := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply Finset.sum_congr rfl
    intro jr _
    apply Finset.sum_congr rfl
    intro js _
    rw [h_E]
  rw [h_E_subst]
  
  have h_dist : (∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j * ((2 * n + 1).choose j : ℤ) *
        ∑ jr ∈ Finset.range (2 * n + 1 - j + 1), ∑ js ∈ Finset.range (j + 1),
          ((2 * n + 1 - j).choose jr : ℤ) * (j.choose js : ℤ) * E jr js (2 * n)) =
      ∑ j ∈ Finset.range (n + 1), ∑ jr ∈ Finset.range (2 * n + 1 - j + 1), ∑ js ∈ Finset.range (j + 1),
        (-1 : ℤ) ^ j * ((2 * n + 1).choose j : ℤ) * ((2 * n + 1 - j).choose jr : ℤ) * (j.choose js : ℤ) * E jr js (2 * n) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro jr _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro js _
    ring
  rw [h_dist]
  
  have h_swap : (∑ j ∈ Finset.range (n + 1), ∑ jr ∈ Finset.range (2 * n + 1 - j + 1), ∑ js ∈ Finset.range (j + 1),
        (-1 : ℤ) ^ j * ((2 * n + 1).choose j : ℤ) * ((2 * n + 1 - j).choose jr : ℤ) * (j.choose js : ℤ) * E jr js (2 * n)) =
      ∑ jr ∈ Finset.range (2 * n + 2), ∑ js ∈ Finset.range (2 * n + 2), ∑ j ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ j * ((2 * n + 1).choose j : ℤ) * ((2 * n + 1 - j).choose jr : ℤ) * (j.choose js : ℤ) * E jr js (2 * n) := by
    have hF : (∑ j ∈ Finset.range (n + 1), ∑ jr ∈ Finset.range (2 * n + 1 - j + 1), ∑ js ∈ Finset.range (j + 1),
          (-1 : ℤ) ^ j * ↑((2 * n + 1).choose j) * ↑((2 * n + 1 - j).choose jr) * ↑(j.choose js) * E jr js (2 * n)) =
        (∑ j ∈ Finset.range (n + 1), ∑ jr ∈ Finset.range (2 * n + 1 - j + 1), ∑ js ∈ Finset.range (j + 1),
          ↑((2 * n + 1 - j).choose jr) * ↑(j.choose js) * ((-1 : ℤ) ^ j * ↑((2 * n + 1).choose j) * E jr js (2 * n))) := by
      apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro jr _; apply Finset.sum_congr rfl; intro js _; ring
    rw [hF]
    rw [sum_triple_swap n (fun j jr js => (-1 : ℤ) ^ j * ((2 * n + 1).choose j : ℤ) * E jr js (2 * n))]
    apply Finset.sum_congr rfl; intro jr _; apply Finset.sum_congr rfl; intro js _; apply Finset.sum_congr rfl; intro j _; ring
  rw [h_swap]
  
  have h_inner : ∀ jr js, (∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j * ↑((2 * n + 1).choose j) * ↑((2 * n + 1 - j).choose jr) * ↑(j.choose js) * E jr js (2 * n)) =
      (∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j * ↑((2 * n + 1).choose j) * ↑((2 * n + 1 - j).choose jr) * ↑(j.choose js)) * E jr js (2 * n) := by
    intro jr js
    exact (Finset.sum_mul _ _ _).symm
  rw [Finset.sum_congr rfl (fun jr _ => Finset.sum_congr rfl (fun js _ => h_inner jr js))]
  
  have h_eval : (∑ jr ∈ Finset.range (2 * n + 2), ∑ js ∈ Finset.range (2 * n + 2),
      (∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j * ↑((2 * n + 1).choose j) * ↑((2 * n + 1 - j).choose jr) * ↑(j.choose js)) * E jr js (2 * n)) =
      ∑ jr ∈ Finset.range (n + 1), ∑ js ∈ Finset.range (n + 1),
        ((-1 : ℤ) ^ n * ↑((2 * n + 1).choose js) * ↑((2 * n + 1 - js).choose jr) * ↑((2 * n - jr - js).choose (n - js))) * E jr js (2 * n) := by
    have h_subst2 : (∑ jr ∈ Finset.range (2 * n + 2), ∑ js ∈ Finset.range (2 * n + 2),
        (∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j * ↑((2 * n + 1).choose j) * ↑((2 * n + 1 - j).choose jr) * ↑(j.choose js)) * E jr js (2 * n)) =
        ∑ jr ∈ Finset.range (2 * n + 2), ∑ js ∈ Finset.range (2 * n + 2),
        (if js ≤ n then (-1 : ℤ) ^ n * ↑((2 * n + 1).choose js) * ↑((2 * n + 1 - js).choose jr) * ↑((2 * n - jr - js).choose (n - js)) else 0) * E jr js (2 * n) := by
      apply Finset.sum_congr rfl
      intro jr _
      apply Finset.sum_congr rfl
      intro js _
      by_cases h_sum : jr + js ≤ 2 * n
      · rw [binom_sum_identity n jr js h_sum]
      · have h_E0 : E jr js (2 * n) = 0 := E_eq_zero_of_gt jr js (2 * n) (by omega)
        rw [h_E0, mul_zero, mul_zero]
    rw [h_subst2]
    have h_split_jr : ∑ jr ∈ Finset.range (2 * n + 2), ∑ js ∈ Finset.range (2 * n + 2),
        (if js ≤ n then (-1 : ℤ) ^ n * ↑((2 * n + 1).choose js) * ↑((2 * n + 1 - js).choose jr) * ↑((2 * n - jr - js).choose (n - js)) else 0) * E jr js (2 * n) =
        ∑ jr ∈ Finset.range (n + 1), ∑ js ∈ Finset.range (2 * n + 2),
        (if js ≤ n then (-1 : ℤ) ^ n * ↑((2 * n + 1).choose js) * ↑((2 * n + 1 - js).choose jr) * ↑((2 * n - jr - js).choose (n - js)) else 0) * E jr js (2 * n) := by
      have h_sub : Finset.range (n + 1) ⊆ Finset.range (2 * n + 2) := by
        intro x hx
        rw [Finset.mem_range] at hx ⊢
        omega
      exact (Finset.sum_subset h_sub (fun jr _ h_not => by
        apply Finset.sum_eq_zero
        intro js _
        have hjr_gt : ¬ (jr ≤ n) := by
          intro h
          apply h_not
          rw [Finset.mem_range]
          omega
        by_cases hjs : js ≤ n
        · by_cases h_sum : jr + js ≤ 2 * n
          · rw [if_pos hjs]
            have : (2 * n - jr - js).choose (n - js) = 0 := by
              apply choose_eq_zero_of_lt
              omega
            rw [this]; push_cast; ring
          · have h_E0 : E jr js (2 * n) = 0 := E_eq_zero_of_gt jr js (2 * n) (by omega)
            rw [h_E0, mul_zero]
        · rw [if_neg hjs, zero_mul]
      )).symm
    rw [h_split_jr]
    apply Finset.sum_congr rfl
    intro jr hjr
    have h_split_js : ∑ js ∈ Finset.range (2 * n + 2),
        (if js ≤ n then (-1 : ℤ) ^ n * ↑((2 * n + 1).choose js) * ↑((2 * n + 1 - js).choose jr) * ↑((2 * n - jr - js).choose (n - js)) else 0) * E jr js (2 * n) =
        ∑ js ∈ Finset.range (n + 1),
        (if js ≤ n then (-1 : ℤ) ^ n * ↑((2 * n + 1).choose js) * ↑((2 * n + 1 - js).choose jr) * ↑((2 * n - jr - js).choose (n - js)) else 0) * E jr js (2 * n) := by
      have h_sub : Finset.range (n + 1) ⊆ Finset.range (2 * n + 2) := by
        intro x hx
        rw [Finset.mem_range] at hx ⊢
        omega
      exact (Finset.sum_subset h_sub (fun js _ h_not => by
        have hjs_gt : ¬ (js ≤ n) := by
          intro h
          apply h_not
          rw [Finset.mem_range]
          omega
        rw [if_neg hjs_gt, zero_mul]
      )).symm
    rw [h_split_js]
    apply Finset.sum_congr rfl
    intro js hjs
    have hjs_le : js ≤ n := by
      rw [Finset.mem_range] at hjs
      omega
    rw [if_pos hjs_le]
  
  rw [h_eval]
  have h_D : (-1 : ℤ) ^ n * D (2 * n + 1) = ∑ jr ∈ Finset.range (n + 1), ∑ js ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ n * ((2 * n + 1).choose jr : ℤ) * ((2 * n + 1 - jr).choose js : ℤ) * ((2 * n - jr - js).choose (n - jr) : ℤ) * E jr js (2 * n) := by
    unfold D
    have : (2 * n + 1 - 1) / 2 = n := by omega
    rw [this]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro jr _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro js _
    have h_sub1 : 2 * n + 1 - jr = 2 * n + 1 - jr := rfl
    have h_sub2 : 2 * n + 1 - 1 - jr - js = 2 * n - jr - js := by omega
    have h_sub3 : 2 * n + 1 - 1 = 2 * n := by omega
    rw [h_sub1, h_sub2, h_sub3]
    ring
  rw [h_D]
  have h_symm : (∑ jr ∈ Finset.range (n + 1), ∑ js ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ n * ↑((2 * n + 1).choose js) * ↑((2 * n + 1 - js).choose jr) * ↑((2 * n - jr - js).choose (n - js)) * E jr js (2 * n)) =
      ∑ jr ∈ Finset.range (n + 1), ∑ js ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ n * ↑((2 * n + 1).choose jr) * ↑((2 * n + 1 - jr).choose js) * ↑((2 * n - js - jr).choose (n - jr)) * E js jr (2 * n) := by
    exact Finset.sum_comm
  rw [h_symm]
  apply Finset.sum_congr rfl
  intro jr _
  apply Finset.sum_congr rfl
  intro js _
  have h_sub4 : 2 * n - js - jr = 2 * n - jr - js := by omega
  rw [h_sub4, E_symm_even js jr n]

/-- The Zhang formula agrees with the direct formula. -/
@[category API, AMS 5]
theorem zhang_eq_a (n : ℕ) : zhang n = a n := by
  rw [a_eq_neg_pow_D, zhang]

end Proof


@[category test, AMS 5]
theorem a_0 : a 0 = 1 := by decide

@[category test, AMS 5]
theorem a_1 : a 1 = 6 := by decide

@[category test, AMS 5]
theorem a_2 : a 2 = 230 := by decide

@[category test, AMS 5]
theorem a_3 : a 3 = 23548 := by decide +native

@[category test, AMS 5]
theorem a_4 : a 4 = 4675014 := by decide +native


@[category test, AMS 5]
theorem zhang_0 : zhang 0 = 1 := by decide

@[category test, AMS 5]
theorem zhang_1 : zhang 1 = 6 := by decide

@[category test, AMS 5]
theorem zhang_2 : zhang 2 = 230 := by decide

@[category test, AMS 5]
theorem zhang_3 : zhang 3 = 23548 := by decide +native

@[category test, AMS 5]
theorem zhang_4 : zhang 4 = 4675014 := by decide +native

end OeisA177043
