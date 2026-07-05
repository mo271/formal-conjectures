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


@[category API, AMS 5]
lemma sum_alternating_choose_partial (M k : ℕ) (hM : M > 0) :
    ∑ m ∈ range (k + 1), (-1) ^ m * (M.choose m : ℤ) = (-1) ^ k * ((M - 1).choose k : ℤ) := by
  induction' k with k ih
  · simp
  · rw [sum_range_succ]
    rw [ih]
    have h1 : (-1 : ℤ) ^ (k + 1) = (-1) ^ k * (-1 : ℤ) := by ring
    rw [h1]
    have h2 : (M.choose (k + 1) : ℤ) = ((M - 1).choose (k + 1) : ℤ) + ((M - 1).choose k : ℤ) := by
      have h3 : M = M - 1 + 1 := by omega
      nth_rw 1 [h3]
      rw [Nat.choose_succ_succ]
      push_cast
      ring
    rw [h2]
    ring

@[category API, AMS 5]
lemma sum_alternating_choose (M k : ℕ) (hM : M > 0) (hk0 : k > 0) (hk : k ≤ M) :
    ∑ m ∈ Ico k (M + 1), (-1) ^ m * (M.choose m : ℤ) = (-1) ^ k * ((M - 1).choose (k - 1) : ℤ) := by
  have h1 : ∑ m ∈ range (M + 1), (-1) ^ m * (M.choose m : ℤ) = 0 := by
    have h2 : ∑ m ∈ range (M + 1), (-1) ^ m * (M.choose m : ℤ) = (-1) ^ M * ((M - 1).choose M : ℤ) := sum_alternating_choose_partial M M hM
    rw [h2]
    have h3 : (M - 1).choose M = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h3]
    simp
  have h2 : ∑ m ∈ range k, (-1) ^ m * (M.choose m : ℤ) + ∑ m ∈ Ico k (M + 1), (-1) ^ m * (M.choose m : ℤ) = ∑ m ∈ range (M + 1), (-1) ^ m * (M.choose m : ℤ) := by
    apply sum_range_add_sum_Ico
    omega
  rw [h1] at h2
  have h3 : ∑ m ∈ Ico k (M + 1), (-1) ^ m * (M.choose m : ℤ) = - ∑ m ∈ range k, (-1) ^ m * (M.choose m : ℤ) := by omega
  rw [h3]
  cases k with
  | zero =>
    omega
  | succ k' =>
    have h4 : ∑ m ∈ range (k' + 1), (-1) ^ m * (M.choose m : ℤ) = (-1) ^ k' * ((M - 1).choose k' : ℤ) := sum_alternating_choose_partial M k' hM
    rw [h4]
    have h5 : (-1 : ℤ) ^ (k' + 1) = - (-1 : ℤ) ^ k' := by ring
    rw [h5]
    have h6 : k' + 1 - 1 = k' := by omega
    rw [h6]
    ring

@[category API, AMS 5]
lemma sum_stirling_choose (n x : ℕ) :
    ∑ j ∈ range (n + 1), (Nat.stirlingSecond n j : ℤ) * j.factorial * (x.choose j : ℤ) = (x : ℤ) ^ n := by
  induction' n with n ih
  · simp
  · cases n with
      | zero =>
        rw [sum_range_succ, sum_range_succ, sum_range_zero]
        simp
        change (1 : ℤ) * x = x
        ring
      | succ n' =>
      have hn : n' + 1 > 0 := by omega
      let n := n' + 1
      change ∑ j ∈ range (n + 1 + 1), (Nat.stirlingSecond (n + 1) j : ℤ) * ↑j.factorial * ↑(x.choose j) = ↑x ^ (n + 1)
      have ih : ∑ j ∈ range (n + 1), (Nat.stirlingSecond n j : ℤ) * ↑j.factorial * ↑(x.choose j) = ↑x ^ n := ih
      rw [pow_succ, ← ih, sum_mul]
      have h1 : ∀ j, ((Nat.stirlingSecond n j : ℤ) * j.factorial * (x.choose j : ℤ)) * (x : ℤ) =
          (Nat.stirlingSecond n j : ℤ) * j.factorial * (j : ℤ) * (x.choose j : ℤ) +
          (Nat.stirlingSecond n j : ℤ) * (j + 1).factorial * (x.choose (j + 1) : ℤ) := by
        intro j
        have h2 : (x.choose j : ℤ) * (x : ℤ) = (j : ℤ) * (x.choose j : ℤ) + (j + 1 : ℤ) * (x.choose (j + 1) : ℤ) := by
          have hj_or : j ≤ x ∨ x < j := by omega
          cases hj_or with
          | inl hj =>
            have h3 : x.choose (j + 1) * (j + 1) = x.choose j * (x - j) := Nat.choose_succ_right_eq x j
            have h4 : (x.choose (j + 1) : ℤ) * (j + 1 : ℤ) = (x.choose j : ℤ) * (x - j : ℤ) := by exact_mod_cast h3
            push_cast [hj] at h4
            linarith
          | inr hj =>
            have h3 : x.choose j = 0 := Nat.choose_eq_zero_of_lt hj
            have h4 : x.choose (j + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
            rw [h3, h4]
            simp
        have h6 : (j + 1).factorial = (j + 1) * j.factorial := rfl
        have h7 : ((j + 1).factorial : ℤ) = (j + 1 : ℤ) * (j.factorial : ℤ) := by exact_mod_cast h6
        calc ((Nat.stirlingSecond n j : ℤ) * ↑j.factorial * ↑(x.choose j)) * (x : ℤ)
          _ = (Nat.stirlingSecond n j : ℤ) * ↑j.factorial * (↑(x.choose j) * (x : ℤ)) := by ring
          _ = (Nat.stirlingSecond n j : ℤ) * ↑j.factorial * ((j : ℤ) * ↑(x.choose j) + (j + 1 : ℤ) * ↑(x.choose (j + 1))) := by rw [h2]
          _ = (Nat.stirlingSecond n j : ℤ) * ↑j.factorial * (j : ℤ) * ↑(x.choose j) + (Nat.stirlingSecond n j : ℤ) * ((j + 1 : ℤ) * ↑j.factorial) * ↑(x.choose (j + 1)) := by ring
          _ = (Nat.stirlingSecond n j : ℤ) * ↑j.factorial * (j : ℤ) * ↑(x.choose j) + (Nat.stirlingSecond n j : ℤ) * ↑(j + 1).factorial * ↑(x.choose (j + 1)) := by rw [h7]
      have h8 : ∑ j ∈ range (n + 1), ((Nat.stirlingSecond n j : ℤ) * ↑j.factorial * ↑(x.choose j)) * (x : ℤ) =
          ∑ j ∈ range (n + 2), (Nat.stirlingSecond n j : ℤ) * ↑j.factorial * (j : ℤ) * ↑(x.choose j) +
          ∑ j ∈ range (n + 2), (Nat.stirlingSecond n (j - 1) : ℤ) * ↑j.factorial * ↑(x.choose j) := by
        have h9 : ∑ j ∈ range (n + 1), ((Nat.stirlingSecond n j : ℤ) * ↑j.factorial * ↑(x.choose j)) * (x : ℤ) =
            ∑ j ∈ range (n + 1), (Nat.stirlingSecond n j : ℤ) * ↑j.factorial * (j : ℤ) * ↑(x.choose j) +
            ∑ j ∈ range (n + 1), (Nat.stirlingSecond n j : ℤ) * ↑(j + 1).factorial * ↑(x.choose (j + 1)) := by
          simp_rw [h1, sum_add_distrib]
        rw [h9]
        have h10 : ∑ j ∈ range (n + 1), (Nat.stirlingSecond n j : ℤ) * ↑j.factorial * (j : ℤ) * ↑(x.choose j) =
            ∑ j ∈ range (n + 2), (Nat.stirlingSecond n j : ℤ) * ↑j.factorial * (j : ℤ) * ↑(x.choose j) := by
          conv_rhs => rw [sum_range_succ]
          have h11 : (Nat.stirlingSecond n (n + 1) : ℤ) = 0 := by
            have h12 : Nat.stirlingSecond n (n + 1) = 0 := Nat.stirlingSecond_eq_zero_of_lt (by omega)
            rw [h12]
            simp
          rw [h11]
          simp
        rw [h10]
        have h11 : ∑ j ∈ range (n + 1), (Nat.stirlingSecond n j : ℤ) * ↑(j + 1).factorial * ↑(x.choose (j + 1)) =
            ∑ j ∈ range (n + 2), (Nat.stirlingSecond n (j - 1) : ℤ) * ↑j.factorial * ↑(x.choose j) := by
          have h12 : ∑ j ∈ range (n + 2), (Nat.stirlingSecond n (j - 1) : ℤ) * ↑j.factorial * ↑(x.choose j) =
              ∑ j ∈ range 1, (Nat.stirlingSecond n (j - 1) : ℤ) * ↑j.factorial * ↑(x.choose j) +
              ∑ j ∈ Ico 1 (n + 2), (Nat.stirlingSecond n (j - 1) : ℤ) * ↑j.factorial * ↑(x.choose j) := by
            symm
            apply sum_range_add_sum_Ico
            omega
          rw [h12]
          have h13 : ∑ j ∈ range 1, (Nat.stirlingSecond n (j - 1) : ℤ) * ↑j.factorial * ↑(x.choose j) = 0 := by
            simp
          rw [h13, zero_add]
          apply sum_bij (fun a _ => a + 1)
          · intro a ha
            rw [mem_Ico]
            rw [mem_range] at ha
            omega
          · intro a1 a2 ha1 ha2 h
            omega
          · intro b hb
            rw [mem_Ico] at hb
            use b - 1
            have h_mem : b - 1 ∈ range (n + 1) := by
              rw [mem_range]
              omega
            exact ⟨h_mem, by omega⟩
          · intro a ha
            have h14 : a + 1 - 1 = a := by omega
            rw [h14]
        rw [h11]
      rw [h8, ← sum_add_distrib]
      apply sum_congr rfl
      intro j hj
      cases j with
      | zero =>
        simp
      | succ j' =>
        have h12 : Nat.stirlingSecond (n + 1) (j' + 1) = (j' + 1) * Nat.stirlingSecond n (j' + 1) + Nat.stirlingSecond n j' := Nat.stirlingSecond_succ_right (n + 1) j' (by omega)
        have h13 : ((Nat.stirlingSecond (n + 1) (j' + 1)) : ℤ) = ((j' + 1) * Nat.stirlingSecond n (j' + 1) + Nat.stirlingSecond n j' : ℤ) := by exact_mod_cast h12
        rw [h13]
        have h14 : j' + 1 - 1 = j' := by omega
        rw [h14]
        push_cast
        ring

@[category API, AMS 5]
lemma sum_E_choose (n x y : ℕ) :
  ∑ jr ∈ range (2 * n + 1), ∑ js ∈ range (2 * n + 1),
    E jr js (2 * n) * (x.choose jr : ℤ) * (y.choose js : ℤ) =
    ∑ r ∈ range (2 * n + 1), (-1) ^ (2 * n - r) * (Nat.choose (2 * n) r : ℤ) * (x : ℤ) ^ r * (y : ℤ) ^ (2 * n - r) := by
  simp only [E]
  have h_mul : ∀ jr js, (∑ r ∈ range (2 * n + 1), (-1) ^ (2 * n - r) * (Nat.choose (2 * n) r : ℤ) * (Nat.stirlingSecond r jr * jr.factorial : ℤ) * (Nat.stirlingSecond (2 * n - r) js * js.factorial : ℤ)) * (x.choose jr : ℤ) * (y.choose js : ℤ) =
    ∑ r ∈ range (2 * n + 1), (-1) ^ (2 * n - r) * (Nat.choose (2 * n) r : ℤ) * (Nat.stirlingSecond r jr * jr.factorial : ℤ) * (Nat.stirlingSecond (2 * n - r) js * js.factorial : ℤ) * (x.choose jr : ℤ) * (y.choose js : ℤ) := by
    intro jr js
    rw [sum_mul, sum_mul]
  simp only [h_mul]
  have h1 : ∑ jr ∈ range (2 * n + 1), ∑ js ∈ range (2 * n + 1), ∑ r ∈ range (2 * n + 1),
      (-1) ^ (2 * n - r) * (Nat.choose (2 * n) r : ℤ) * (Nat.stirlingSecond r jr * jr.factorial : ℤ) * (Nat.stirlingSecond (2 * n - r) js * js.factorial : ℤ) * (x.choose jr : ℤ) * (y.choose js : ℤ) =
    ∑ r ∈ range (2 * n + 1), ∑ jr ∈ range (2 * n + 1), ∑ js ∈ range (2 * n + 1),
      (-1) ^ (2 * n - r) * (Nat.choose (2 * n) r : ℤ) * (Nat.stirlingSecond r jr * jr.factorial : ℤ) * (Nat.stirlingSecond (2 * n - r) js * js.factorial : ℤ) * (x.choose jr : ℤ) * (y.choose js : ℤ) := by
    calc
      ∑ jr ∈ range (2 * n + 1), ∑ js ∈ range (2 * n + 1), ∑ r ∈ range (2 * n + 1),
          (-1) ^ (2 * n - r) * (Nat.choose (2 * n) r : ℤ) * (Nat.stirlingSecond r jr * jr.factorial : ℤ) * (Nat.stirlingSecond (2 * n - r) js * js.factorial : ℤ) * (x.choose jr : ℤ) * (y.choose js : ℤ)
      _ = ∑ jr ∈ range (2 * n + 1), ∑ r ∈ range (2 * n + 1), ∑ js ∈ range (2 * n + 1),
          (-1) ^ (2 * n - r) * (Nat.choose (2 * n) r : ℤ) * (Nat.stirlingSecond r jr * jr.factorial : ℤ) * (Nat.stirlingSecond (2 * n - r) js * js.factorial : ℤ) * (x.choose jr : ℤ) * (y.choose js : ℤ) := by
        apply sum_congr rfl
        intro jr _
        rw [sum_comm]
      _ = ∑ r ∈ range (2 * n + 1), ∑ jr ∈ range (2 * n + 1), ∑ js ∈ range (2 * n + 1),
          (-1) ^ (2 * n - r) * (Nat.choose (2 * n) r : ℤ) * (Nat.stirlingSecond r jr * jr.factorial : ℤ) * (Nat.stirlingSecond (2 * n - r) js * js.factorial : ℤ) * (x.choose jr : ℤ) * (y.choose js : ℤ) := by
        rw [sum_comm]
  rw [h1]
  apply sum_congr rfl
  intro r hr
  simp only [mem_range] at hr
  have h2 : ∑ jr ∈ range (2 * n + 1), ∑ js ∈ range (2 * n + 1),
      (-1) ^ (2 * n - r) * (Nat.choose (2 * n) r : ℤ) * (Nat.stirlingSecond r jr * jr.factorial : ℤ) * (Nat.stirlingSecond (2 * n - r) js * js.factorial : ℤ) * (x.choose jr : ℤ) * (y.choose js : ℤ) =
    (-1) ^ (2 * n - r) * (Nat.choose (2 * n) r : ℤ) *
      (∑ jr ∈ range (2 * n + 1), (Nat.stirlingSecond r jr * jr.factorial : ℤ) * (x.choose jr : ℤ)) *
      (∑ js ∈ range (2 * n + 1), (Nat.stirlingSecond (2 * n - r) js * js.factorial : ℤ) * (y.choose js : ℤ)) := by
    have h3 : ∀ jr js, (-1) ^ (2 * n - r) * (Nat.choose (2 * n) r : ℤ) * (Nat.stirlingSecond r jr * jr.factorial : ℤ) * (Nat.stirlingSecond (2 * n - r) js * js.factorial : ℤ) * (x.choose jr : ℤ) * (y.choose js : ℤ) =
      (-1) ^ (2 * n - r) * (Nat.choose (2 * n) r : ℤ) * ((Nat.stirlingSecond r jr * jr.factorial : ℤ) * (x.choose jr : ℤ)) * ((Nat.stirlingSecond (2 * n - r) js * js.factorial : ℤ) * (y.choose js : ℤ)) := by
      intro jr js
      ring
    simp only [h3]
    have h4 : ∀ jr, ∑ js ∈ range (2 * n + 1), (-1) ^ (2 * n - r) * (Nat.choose (2 * n) r : ℤ) * ((Nat.stirlingSecond r jr * jr.factorial : ℤ) * (x.choose jr : ℤ)) * ((Nat.stirlingSecond (2 * n - r) js * js.factorial : ℤ) * (y.choose js : ℤ)) =
      (-1) ^ (2 * n - r) * (Nat.choose (2 * n) r : ℤ) * ((Nat.stirlingSecond r jr * jr.factorial : ℤ) * (x.choose jr : ℤ)) * ∑ js ∈ range (2 * n + 1), ((Nat.stirlingSecond (2 * n - r) js * js.factorial : ℤ) * (y.choose js : ℤ)) := by
      intro jr
      rw [← mul_sum]
    simp only [h4]
    rw [← sum_mul]
    have h5 : (∑ i ∈ range (2 * n + 1), (-1) ^ (2 * n - r) * (Nat.choose (2 * n) r : ℤ) * ((Nat.stirlingSecond r i * i.factorial : ℤ) * (x.choose i : ℤ))) =
      (-1) ^ (2 * n - r) * (Nat.choose (2 * n) r : ℤ) * ∑ i ∈ range (2 * n + 1), ((Nat.stirlingSecond r i * i.factorial : ℤ) * (x.choose i : ℤ)) := by
      rw [← mul_sum]
    rw [h5]
  rw [h2]
  have h_jr : ∑ jr ∈ range (2 * n + 1), (Nat.stirlingSecond r jr * jr.factorial : ℤ) * (x.choose jr : ℤ) = (x : ℤ) ^ r := by
    have h_split : ∑ jr ∈ range (2 * n + 1), (Nat.stirlingSecond r jr * jr.factorial : ℤ) * (x.choose jr : ℤ) =
        ∑ jr ∈ range (r + 1), (Nat.stirlingSecond r jr * jr.factorial : ℤ) * (x.choose jr : ℤ) +
        ∑ jr ∈ Ico (r + 1) (2 * n + 1), (Nat.stirlingSecond r jr * jr.factorial : ℤ) * (x.choose jr : ℤ) := by
      symm
      apply sum_range_add_sum_Ico
      omega
    rw [h_split]
    have h_zero : ∑ jr ∈ Ico (r + 1) (2 * n + 1), (Nat.stirlingSecond r jr * jr.factorial : ℤ) * (x.choose jr : ℤ) = 0 := by
      apply sum_eq_zero
      intro jr hjr
      simp only [mem_Ico] at hjr
      have h_stirling : Nat.stirlingSecond r jr = 0 := Nat.stirlingSecond_eq_zero_of_lt hjr.1
      rw [h_stirling]
      simp
    rw [h_zero, add_zero]
    have h_stirling_choose := sum_stirling_choose r x
    have h_rearrange : ∑ jr ∈ range (r + 1), (Nat.stirlingSecond r jr * jr.factorial : ℤ) * (x.choose jr : ℤ) =
        ∑ jr ∈ range (r + 1), (Nat.stirlingSecond r jr : ℤ) * ↑jr.factorial * ↑(x.choose jr) := by
      apply sum_congr rfl
      intro jr _
      ring
    rw [h_rearrange, h_stirling_choose]
  have h_js : ∑ js ∈ range (2 * n + 1), (Nat.stirlingSecond (2 * n - r) js * js.factorial : ℤ) * (y.choose js : ℤ) = (y : ℤ) ^ (2 * n - r) := by
    have h_split : ∑ js ∈ range (2 * n + 1), (Nat.stirlingSecond (2 * n - r) js * js.factorial : ℤ) * (y.choose js : ℤ) =
        ∑ js ∈ range (2 * n - r + 1), (Nat.stirlingSecond (2 * n - r) js * js.factorial : ℤ) * (y.choose js : ℤ) +
        ∑ js ∈ Ico (2 * n - r + 1) (2 * n + 1), (Nat.stirlingSecond (2 * n - r) js * js.factorial : ℤ) * (y.choose js : ℤ) := by
      symm
      apply sum_range_add_sum_Ico
      omega
    rw [h_split]
    have h_zero : ∑ js ∈ Ico (2 * n - r + 1) (2 * n + 1), (Nat.stirlingSecond (2 * n - r) js * js.factorial : ℤ) * (y.choose js : ℤ) = 0 := by
      apply sum_eq_zero
      intro js hjs
      simp only [mem_Ico] at hjs
      have h_stirling : Nat.stirlingSecond (2 * n - r) js = 0 := Nat.stirlingSecond_eq_zero_of_lt hjs.1
      rw [h_stirling]
      simp
    rw [h_zero, add_zero]
    have h_stirling_choose := sum_stirling_choose (2 * n - r) y
    have h_rearrange : ∑ js ∈ range (2 * n - r + 1), (Nat.stirlingSecond (2 * n - r) js * js.factorial : ℤ) * (y.choose js : ℤ) =
        ∑ js ∈ range (2 * n - r + 1), (Nat.stirlingSecond (2 * n - r) js : ℤ) * ↑js.factorial * ↑(y.choose js) := by
      apply sum_congr rfl
      intro js _
      ring
    rw [h_rearrange, h_stirling_choose]
  rw [h_jr, h_js]

@[category API, AMS 5]
lemma choose_mul_choose_eq (N l jr : ℕ) (hl : l ≤ N) (hjr : jr ≤ N - l) :
  N.choose l * (N - l).choose jr = N.choose jr * (N - jr).choose l := by
  have h1 : N.choose l * (N - l).choose jr * l.factorial * jr.factorial * (N - l - jr).factorial = N.factorial := by
    calc
      N.choose l * (N - l).choose jr * l.factorial * jr.factorial * (N - l - jr).factorial
        = N.choose l * l.factorial * ((N - l).choose jr * jr.factorial * (N - l - jr).factorial) := by ring
      _ = N.choose l * l.factorial * (N - l).factorial := by
        rw [Nat.choose_mul_factorial_mul_factorial hjr]
      _ = N.factorial := by
        rw [Nat.choose_mul_factorial_mul_factorial hl]
  have h2 : N.choose jr * (N - jr).choose l * jr.factorial * l.factorial * (N - jr - l).factorial = N.factorial := by
    have hjr_le : jr ≤ N := by omega
    have hl_le : l ≤ N - jr := by omega
    calc
      N.choose jr * (N - jr).choose l * jr.factorial * l.factorial * (N - jr - l).factorial
        = N.choose jr * jr.factorial * ((N - jr).choose l * l.factorial * (N - jr - l).factorial) := by ring
      _ = N.choose jr * jr.factorial * (N - jr).factorial := by
        rw [Nat.choose_mul_factorial_mul_factorial hl_le]
      _ = N.factorial := by
        rw [Nat.choose_mul_factorial_mul_factorial hjr_le]
  have h3 : N - l - jr = N - jr - l := by omega
  rw [h3] at h1
  have h4 : N.choose l * (N - l).choose jr * (l.factorial * jr.factorial * (N - jr - l).factorial) =
            N.choose jr * (N - jr).choose l * (l.factorial * jr.factorial * (N - jr - l).factorial) := by
    calc
      N.choose l * (N - l).choose jr * (l.factorial * jr.factorial * (N - jr - l).factorial)
        = N.choose l * (N - l).choose jr * l.factorial * jr.factorial * (N - jr - l).factorial := by ring
      _ = N.factorial := h1
      _ = N.choose jr * (N - jr).choose l * jr.factorial * l.factorial * (N - jr - l).factorial := h2.symm
      _ = N.choose jr * (N - jr).choose l * (l.factorial * jr.factorial * (N - jr - l).factorial) := by ring
  have h5 : l.factorial * jr.factorial * (N - jr - l).factorial > 0 := by positivity
  exact Nat.eq_of_mul_eq_mul_right h5 h4

@[category API, AMS 5]
lemma sum_coef (n jr js : ℕ) (hjr : jr ≤ n) (hjs : js ≤ n) :
  ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * (((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ)) =
  (-1 : ℤ) ^ n * ((2 * n + 1).choose jr : ℤ) * (((2 * n + 1 - jr).choose js : ℤ) * ((2 * n - jr - js).choose (n - jr) : ℤ)) := by
  have h_sum : ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * (((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ)) =
    ∑ l ∈ Ico js (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * (((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ)) := by
    have h_split : ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * (((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ)) =
      ∑ l ∈ range js, (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * (((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ)) +
      ∑ l ∈ Ico js (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * (((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ)) := by
      rw [sum_range_add_sum_Ico _ (by omega)]
    rw [h_split]
    have h_zero : ∑ l ∈ range js, (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * (((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ)) = 0 := by
      apply sum_eq_zero
      intro l hl
      rw [mem_range] at hl
      have : l.choose js = 0 := Nat.choose_eq_zero_of_lt hl
      simp [this]
    rw [h_zero, zero_add]
  rw [h_sum]
  have h_inner : ∀ l ∈ Ico js (n + 1), ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) =
    ((2 * n + 1).choose jr : ℤ) * ((2 * n + 1 - jr).choose js : ℤ) * ((2 * n + 1 - jr - js).choose (l - js) : ℤ) := by
    intro l hl
    rw [mem_Ico] at hl
    have hl_le : l ≤ 2 * n + 1 := by omega
    have hjr_le : jr ≤ 2 * n + 1 - l := by omega
    have h1 := choose_mul_choose_eq (2 * n + 1) l jr hl_le hjr_le
    have h2 := Nat.choose_mul hl.1 (n := 2 * n + 1 - jr)
    have h3 : (2 * n + 1).choose l * (2 * n + 1 - l).choose jr * l.choose js =
      (2 * n + 1).choose jr * (2 * n + 1 - jr).choose js * (2 * n + 1 - jr - js).choose (l - js) := by
      calc
        (2 * n + 1).choose l * (2 * n + 1 - l).choose jr * l.choose js
          = (2 * n + 1).choose jr * (2 * n + 1 - jr).choose l * l.choose js := by rw [h1]
        _ = (2 * n + 1).choose jr * ((2 * n + 1 - jr).choose l * l.choose js) := by ring
        _ = (2 * n + 1).choose jr * ((2 * n + 1 - jr).choose js * (2 * n + 1 - jr - js).choose (l - js)) := by rw [h2]
        _ = (2 * n + 1).choose jr * (2 * n + 1 - jr).choose js * (2 * n + 1 - jr - js).choose (l - js) := by ring
    exact_mod_cast h3
  have h_inner2 : ∀ l ∈ Ico js (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * (((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ)) =
    (-1 : ℤ) ^ l * (((2 * n + 1).choose jr : ℤ) * ((2 * n + 1 - jr).choose js : ℤ) * ((2 * n + 1 - jr - js).choose (l - js) : ℤ)) := by
    intro l hl
    have := h_inner l hl
    calc
      (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * (((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ))
        = (-1 : ℤ) ^ l * (((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ)) := by ring
      _ = (-1 : ℤ) ^ l * (((2 * n + 1).choose jr : ℤ) * ((2 * n + 1 - jr).choose js : ℤ) * ((2 * n + 1 - jr - js).choose (l - js) : ℤ)) := by rw [this]
  rw [sum_congr rfl h_inner2]
  have h_pull : ∑ l ∈ Ico js (n + 1), (-1 : ℤ) ^ l * (((2 * n + 1).choose jr : ℤ) * ((2 * n + 1 - jr).choose js : ℤ) * ((2 * n + 1 - jr - js).choose (l - js) : ℤ)) =
    ((2 * n + 1).choose jr : ℤ) * ((2 * n + 1 - jr).choose js : ℤ) * ∑ l ∈ Ico js (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1 - jr - js).choose (l - js) : ℤ) := by
    calc
      ∑ l ∈ Ico js (n + 1), (-1 : ℤ) ^ l * (((2 * n + 1).choose jr : ℤ) * ((2 * n + 1 - jr).choose js : ℤ) * ((2 * n + 1 - jr - js).choose (l - js) : ℤ))
        = ∑ l ∈ Ico js (n + 1), (((2 * n + 1).choose jr : ℤ) * ((2 * n + 1 - jr).choose js : ℤ)) * ((-1 : ℤ) ^ l * ((2 * n + 1 - jr - js).choose (l - js) : ℤ)) := by
          apply sum_congr rfl
          intro l hl
          ring
      _ = ((2 * n + 1).choose jr : ℤ) * ((2 * n + 1 - jr).choose js : ℤ) * ∑ l ∈ Ico js (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1 - jr - js).choose (l - js) : ℤ) := by rw [mul_sum]
  rw [h_pull]
  have h_sum2 : ∑ l ∈ Ico js (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1 - jr - js).choose (l - js) : ℤ) =
    (-1 : ℤ) ^ js * ∑ k ∈ range (n + 1 - js), (-1 : ℤ) ^ k * ((2 * n + 1 - jr - js).choose k : ℤ) := by
    have h_shift : ∑ l ∈ Ico js (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1 - jr - js).choose (l - js) : ℤ) =
      ∑ k ∈ range (n + 1 - js), (-1 : ℤ) ^ (js + k) * ((2 * n + 1 - jr - js).choose (js + k - js) : ℤ) := by
      exact sum_Ico_eq_sum_range (fun l => (-1 : ℤ) ^ l * ((2 * n + 1 - jr - js).choose (l - js) : ℤ)) js (n + 1)
    rw [h_shift]
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    have : (-1 : ℤ) ^ (js + k) = (-1 : ℤ) ^ js * (-1 : ℤ) ^ k := by
      rw [pow_add]
    rw [this]
    have : js + k - js = k := by omega
    rw [this]
    ring
  rw [h_sum2]
  have h_sum3 : ∑ k ∈ range (n + 1 - js), (-1 : ℤ) ^ k * ((2 * n + 1 - jr - js).choose k : ℤ) =
    (-1 : ℤ) ^ (n - js) * ((2 * n - jr - js).choose (n - js) : ℤ) := by
    have hN : 2 * n + 1 - jr - js > 0 := by omega
    have hM : n + 1 - js = n - js + 1 := by omega
    rw [hM]
    have h_alt := sum_alternating_choose_partial (2 * n + 1 - jr - js) (n - js) hN
    have h_sub : 2 * n + 1 - jr - js - 1 = 2 * n - jr - js := by omega
    rw [h_sub] at h_alt
    exact h_alt
  rw [h_sum3]
  have h_pow : (-1 : ℤ) ^ js * ((-1 : ℤ) ^ (n - js) * ↑((2 * n - jr - js).choose (n - js))) =
    (-1 : ℤ) ^ n * ↑((2 * n - jr - js).choose (n - jr)) := by
    have : (-1 : ℤ) ^ js * (-1 : ℤ) ^ (n - js) = (-1 : ℤ) ^ n := by
      rw [← pow_add]
      have : js + (n - js) = n := by omega
      rw [this]
    rw [← mul_assoc, this]
    have h_symm : (2 * n - jr - js).choose (n - js) = (2 * n - jr - js).choose (n - jr) := by
      have h_le : n - js ≤ 2 * n - jr - js := by omega
      have h_sub : 2 * n - jr - js - (n - js) = n - jr := by omega
      rw [← Nat.choose_symm h_le, h_sub]
    rw [h_symm]
  rw [h_pow]
  ring

@[category API, AMS 5]
lemma choose_mul_choose_eq_all (N l jr : ℕ) (hl : l ≤ N) :
  N.choose l * (N - l).choose jr = N.choose jr * (N - jr).choose l := by
  have h_or : jr ≤ N - l ∨ jr > N - l := by omega
  cases h_or with
  | inl h1 => exact choose_mul_choose_eq N l jr hl h1
  | inr h2 =>
    have h3 : (N - l).choose jr = 0 := Nat.choose_eq_zero_of_lt h2
    rw [h3, mul_zero]
    have h_or2 : jr > N ∨ jr ≤ N := by omega
    cases h_or2 with
    | inl h4 =>
      have h5 : N.choose jr = 0 := Nat.choose_eq_zero_of_lt h4
      rw [h5, zero_mul]
    | inr h4 =>
      have h5 : l > N - jr := by omega
      have h6 : (N - jr).choose l = 0 := Nat.choose_eq_zero_of_lt h5
      rw [h6, mul_zero]

@[category API, AMS 5]
lemma inner_sum_zero (n jr js : ℕ) (hjr : jr > n) (hjs : js ≤ n) (h_sum : jr + js ≤ 2 * n) :
  ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * (((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ)) = 0 := by
  have h_sum_split : ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * (((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ)) =
    ∑ l ∈ Ico js (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * (((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ)) := by
    have h_split : ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * (((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ)) =
      ∑ l ∈ range js, (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * (((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ)) +
      ∑ l ∈ Ico js (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * (((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ)) := by
      rw [sum_range_add_sum_Ico _ (by omega)]
    rw [h_split]
    have h_zero : ∑ l ∈ range js, (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * (((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ)) = 0 := by
      apply sum_eq_zero
      intro l hl
      rw [mem_range] at hl
      have : l.choose js = 0 := Nat.choose_eq_zero_of_lt hl
      simp [this]
    rw [h_zero, zero_add]
  rw [h_sum_split]
  have h_inner : ∀ l ∈ Ico js (n + 1), ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) =
    ((2 * n + 1).choose jr : ℤ) * ((2 * n + 1 - jr).choose js : ℤ) * ((2 * n + 1 - jr - js).choose (l - js) : ℤ) := by
    intro l hl
    rw [mem_Ico] at hl
    have hl_le : l ≤ 2 * n + 1 := by omega
    have h1 := choose_mul_choose_eq_all (2 * n + 1) l jr hl_le
    have h2 := Nat.choose_mul hl.1 (n := 2 * n + 1 - jr)
    have h3 : (2 * n + 1).choose l * (2 * n + 1 - l).choose jr * l.choose js =
      (2 * n + 1).choose jr * (2 * n + 1 - jr).choose js * (2 * n + 1 - jr - js).choose (l - js) := by
      calc
        (2 * n + 1).choose l * (2 * n + 1 - l).choose jr * l.choose js
          = (2 * n + 1).choose jr * (2 * n + 1 - jr).choose l * l.choose js := by rw [h1]
        _ = (2 * n + 1).choose jr * ((2 * n + 1 - jr).choose l * l.choose js) := by ring
        _ = (2 * n + 1).choose jr * ((2 * n + 1 - jr).choose js * (2 * n + 1 - jr - js).choose (l - js)) := by rw [h2]
        _ = (2 * n + 1).choose jr * (2 * n + 1 - jr).choose js * (2 * n + 1 - jr - js).choose (l - js) := by ring
    exact_mod_cast h3
  have h_inner2 : ∀ l ∈ Ico js (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * (((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ)) =
    (-1 : ℤ) ^ l * (((2 * n + 1).choose jr : ℤ) * ((2 * n + 1 - jr).choose js : ℤ) * ((2 * n + 1 - jr - js).choose (l - js) : ℤ)) := by
    intro l hl
    have := h_inner l hl
    calc
      (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * (((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ))
        = (-1 : ℤ) ^ l * (((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ)) := by ring
      _ = (-1 : ℤ) ^ l * (((2 * n + 1).choose jr : ℤ) * ((2 * n + 1 - jr).choose js : ℤ) * ((2 * n + 1 - jr - js).choose (l - js) : ℤ)) := by rw [this]
  rw [sum_congr rfl h_inner2]
  have h_pull : ∑ l ∈ Ico js (n + 1), (-1 : ℤ) ^ l * (((2 * n + 1).choose jr : ℤ) * ((2 * n + 1 - jr).choose js : ℤ) * ((2 * n + 1 - jr - js).choose (l - js) : ℤ)) =
    ((2 * n + 1).choose jr : ℤ) * ((2 * n + 1 - jr).choose js : ℤ) * ∑ l ∈ Ico js (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1 - jr - js).choose (l - js) : ℤ) := by
    calc
      ∑ l ∈ Ico js (n + 1), (-1 : ℤ) ^ l * (((2 * n + 1).choose jr : ℤ) * ((2 * n + 1 - jr).choose js : ℤ) * ((2 * n + 1 - jr - js).choose (l - js) : ℤ))
        = ∑ l ∈ Ico js (n + 1), (((2 * n + 1).choose jr : ℤ) * ((2 * n + 1 - jr).choose js : ℤ)) * ((-1 : ℤ) ^ l * ((2 * n + 1 - jr - js).choose (l - js) : ℤ)) := by
          apply sum_congr rfl
          intro l hl
          ring
      _ = ((2 * n + 1).choose jr : ℤ) * ((2 * n + 1 - jr).choose js : ℤ) * ∑ l ∈ Ico js (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1 - jr - js).choose (l - js) : ℤ) := by rw [mul_sum]
  rw [h_pull]
  have h_sum2 : ∑ l ∈ Ico js (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1 - jr - js).choose (l - js) : ℤ) =
    (-1 : ℤ) ^ js * ∑ k ∈ range (n + 1 - js), (-1 : ℤ) ^ k * ((2 * n + 1 - jr - js).choose k : ℤ) := by
    have h_shift : ∑ l ∈ Ico js (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1 - jr - js).choose (l - js) : ℤ) =
      ∑ k ∈ range (n + 1 - js), (-1 : ℤ) ^ (js + k) * ((2 * n + 1 - jr - js).choose (js + k - js) : ℤ) := by
      exact sum_Ico_eq_sum_range (fun l => (-1 : ℤ) ^ l * ((2 * n + 1 - jr - js).choose (l - js) : ℤ)) js (n + 1)
    rw [h_shift]
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    have : (-1 : ℤ) ^ (js + k) = (-1 : ℤ) ^ js * (-1 : ℤ) ^ k := by
      rw [pow_add]
    rw [this]
    have : js + k - js = k := by omega
    rw [this]
    ring
  rw [h_sum2]
  have h_sum3 : ∑ k ∈ range (n + 1 - js), (-1 : ℤ) ^ k * ((2 * n + 1 - jr - js).choose k : ℤ) = 0 := by
    let N := 2 * n + 1 - jr - js
    have hN_pos : N > 0 := by omega
    have hN_le : N ≤ n - js := by omega
    have h_split : ∑ k ∈ range (n + 1 - js), (-1 : ℤ) ^ k * (N.choose k : ℤ) =
      ∑ k ∈ range (N + 1), (-1 : ℤ) ^ k * (N.choose k : ℤ) +
      ∑ k ∈ Ico (N + 1) (n + 1 - js), (-1 : ℤ) ^ k * (N.choose k : ℤ) := by
      exact (sum_range_add_sum_Ico _ (by omega)).symm
    rw [h_split]
    have h_zero1 : ∑ k ∈ range (N + 1), (-1 : ℤ) ^ k * (N.choose k : ℤ) = 0 := by
      have h_alt := sum_alternating_choose_partial N N hN_pos
      have h_sub : N - 1 = 2 * n - jr - js := by omega
      have h_choose : (N - 1).choose N = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [h_choose] at h_alt
      simp at h_alt
      exact h_alt
    have h_zero2 : ∑ k ∈ Ico (N + 1) (n + 1 - js), (-1 : ℤ) ^ k * (N.choose k : ℤ) = 0 := by
      apply sum_eq_zero
      intro k hk
      rw [mem_Ico] at hk
      have : N.choose k = 0 := Nat.choose_eq_zero_of_lt hk.1
      simp [this]
    rw [h_zero1, h_zero2, add_zero]
  rw [h_sum3]
  ring

@[category API, AMS 5]
lemma E_zero_of_gt (jr js m : ℕ) (h : jr + js > m) : E jr js m = 0 := by
  unfold E
  apply sum_eq_zero
  intro r hr
  rw [mem_range] at hr
  have h_or : r < jr ∨ m - r < js := by omega
  cases h_or with
  | inl h1 =>
    have h2 : Nat.stirlingSecond r jr = 0 := Nat.stirlingSecond_eq_zero_of_lt h1
    simp [h2]
  | inr h2 =>
    have h3 : Nat.stirlingSecond (m - r) js = 0 := Nat.stirlingSecond_eq_zero_of_lt h2
    simp [h3]

@[category API, AMS 5]
lemma sum_E_choose_eq_pow (n x y : ℕ) :
  ∑ jr ∈ range (2 * n + 1), ∑ js ∈ range (2 * n + 1), E jr js (2 * n) * (x.choose jr : ℤ) * (y.choose js : ℤ) =
  ((x : ℤ) - y) ^ (2 * n) := by
  have h1 := sum_E_choose n x y
  have h2 : ∑ r ∈ range (2 * n + 1), (-1 : ℤ) ^ (2 * n - r) * ((2 * n).choose r : ℤ) * (x : ℤ) ^ r * (y : ℤ) ^ (2 * n - r) = ((x : ℤ) - y) ^ (2 * n) := by
    have h_binom : ((x : ℤ) + (- (y : ℤ))) ^ (2 * n) = ∑ r ∈ range (2 * n + 1), (x : ℤ) ^ r * (- (y : ℤ)) ^ (2 * n - r) * ((2 * n).choose r : ℤ) := by
      exact add_pow (x : ℤ) (- (y : ℤ)) (2 * n)
    have h_sum : ∑ r ∈ range (2 * n + 1), (x : ℤ) ^ r * (- (y : ℤ)) ^ (2 * n - r) * ((2 * n).choose r : ℤ) =
      ∑ r ∈ range (2 * n + 1), (-1 : ℤ) ^ (2 * n - r) * ((2 * n).choose r : ℤ) * (x : ℤ) ^ r * (y : ℤ) ^ (2 * n - r) := by
      apply sum_congr rfl
      intro r _
      have h_neg : (- (y : ℤ)) ^ (2 * n - r) = (-1 : ℤ) ^ (2 * n - r) * (y : ℤ) ^ (2 * n - r) := by
        have : - (y : ℤ) = (-1 : ℤ) * (y : ℤ) := by ring
        rw [this, mul_pow]
      rw [h_neg]
      ring
    rw [← h_sum, ← h_binom]
    ring
  rw [h1, h2]

/-- The Zhang formula agrees with the direct formula. -/
@[category API, AMS 5]
theorem zhang_eq_a (n : ℕ) : zhang n = a n := by
  unfold zhang a D
  have h_n : (2 * n + 1 - 1) / 2 = n := by omega
  simp only [h_n]
  have h_pow : (-1 : ℤ) ^ n * ∑ jr ∈ range (n + 1), ∑ js ∈ range (n + 1), ((2 * n + 1).choose jr : ℤ) * ((2 * n + 1 - jr).choose js : ℤ) * ((2 * n + 1 - 1 - jr - js).choose (n - jr) : ℤ) * E jr js (2 * n + 1 - 1) =
    ∑ jr ∈ range (n + 1), ∑ js ∈ range (n + 1), (-1 : ℤ) ^ n * ((2 * n + 1).choose jr : ℤ) * ((2 * n + 1 - jr).choose js : ℤ) * ((2 * n - jr - js).choose (n - jr) : ℤ) * E jr js (2 * n) := by
    have h_sub : 2 * n + 1 - 1 = 2 * n := by omega
    rw [h_sub]
    rw [mul_sum]
    apply sum_congr rfl
    intro jr _
    rw [mul_sum]
    apply sum_congr rfl
    intro js _
    ring
  rw [h_pow]
  have h_a : ∑ i ∈ range (n + 1), (-1 : ℤ) ^ (n - i) * ((2 * n + 1).choose (n - i) : ℤ) * ((2 * (i : ℤ) + 1) ^ (2 * n)) =
    ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - 2 * l : ℤ) ^ (2 * n)) := by
    have h_rev : ∑ i ∈ range (n + 1), (-1 : ℤ) ^ (n - i) * ((2 * n + 1).choose (n - i) : ℤ) * ((2 * (i : ℤ) + 1) ^ (2 * n)) =
      ∑ l ∈ range (n + 1), (-1 : ℤ) ^ (n - (n + 1 - 1 - l)) * ((2 * n + 1).choose (n - (n + 1 - 1 - l)) : ℤ) * ((2 * ((n + 1 - 1 - l : ℕ) : ℤ) + 1) ^ (2 * n)) := by
      symm
      exact sum_range_reflect (fun i => (-1 : ℤ) ^ (n - i) * ((2 * n + 1).choose (n - i) : ℤ) * ((2 * (i : ℤ) + 1) ^ (2 * n))) (n + 1)
    have h_simp : ∑ l ∈ range (n + 1), (-1 : ℤ) ^ (n - (n + 1 - 1 - l)) * ((2 * n + 1).choose (n - (n + 1 - 1 - l)) : ℤ) * ((2 * ((n + 1 - 1 - l : ℕ) : ℤ) + 1) ^ (2 * n)) =
      ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * ((n - l : ℕ) : ℤ) + 1) ^ (2 * n)) := by
      apply sum_congr rfl
      intro l hl
      rw [mem_range] at hl
      have h_sub : n + 1 - 1 - l = n - l := by omega
      rw [h_sub]
      have h_sub2 : n - (n - l) = l := by omega
      rw [h_sub2]
    rw [h_rev, h_simp]
    apply sum_congr rfl
    intro l hl
    rw [mem_range] at hl
    have h_base : 2 * ((n - l : ℕ) : ℤ) + 1 = (2 * n + 1 - 2 * l : ℤ) := by
      omega
    rw [h_base]
  rw [h_a]
  have h_subst : ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - 2 * l : ℤ)) ^ (2 * n) =
    ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ∑ jr ∈ range (2 * n + 1), ∑ js ∈ range (2 * n + 1), E jr js (2 * n) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) := by
    apply sum_congr rfl
    intro l hl
    rw [mem_range] at hl
    have h_pow2 := sum_E_choose_eq_pow n (2 * n + 1 - l) l
    have h_cast2 : ((2 * n + 1 - l : ℕ) : ℤ) - (l : ℤ) = (2 * n + 1 - 2 * l : ℤ) := by
      omega
    rw [← h_cast2]
    rw [h_pow2]
  rw [h_subst]
  have h_expand : ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ∑ jr ∈ range (2 * n + 1), ∑ js ∈ range (2 * n + 1), E jr js (2 * n) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) =
    ∑ jr ∈ range (2 * n + 1), ∑ js ∈ range (2 * n + 1), E jr js (2 * n) * ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) := by
    calc
      ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ∑ jr ∈ range (2 * n + 1), ∑ js ∈ range (2 * n + 1), E jr js (2 * n) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ)
      _ = ∑ l ∈ range (n + 1), ∑ jr ∈ range (2 * n + 1), ∑ js ∈ range (2 * n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * (E jr js (2 * n) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ)) := by
        apply sum_congr rfl
        intro l _
        rw [mul_sum]
        apply sum_congr rfl
        intro jr _
        rw [mul_sum]
      _ = ∑ jr ∈ range (2 * n + 1), ∑ js ∈ range (2 * n + 1), ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * (E jr js (2 * n) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ)) := by
        rw [sum_comm]
        apply sum_congr rfl
        intro jr _
        rw [sum_comm]
      _ = ∑ jr ∈ range (2 * n + 1), ∑ js ∈ range (2 * n + 1), E jr js (2 * n) * ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) := by
        apply sum_congr rfl
        intro jr _
        apply sum_congr rfl
        intro js _
        rw [mul_sum]
        apply sum_congr rfl
        intro l _
        ring
  rw [h_expand]
  have h_split : ∑ jr ∈ range (2 * n + 1), ∑ js ∈ range (2 * n + 1), E jr js (2 * n) * ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) =
    ∑ jr ∈ range (n + 1), ∑ js ∈ range (n + 1), E jr js (2 * n) * ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) := by
    have h_split_jr : ∑ jr ∈ range (2 * n + 1), ∑ js ∈ range (2 * n + 1), E jr js (2 * n) * ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) =
      ∑ jr ∈ range (n + 1), ∑ js ∈ range (2 * n + 1), E jr js (2 * n) * ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) +
      ∑ jr ∈ Ico (n + 1) (2 * n + 1), ∑ js ∈ range (2 * n + 1), E jr js (2 * n) * ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) := by
      symm
      apply sum_range_add_sum_Ico
      omega
    rw [h_split_jr]
    have h_zero_jr : ∑ jr ∈ Ico (n + 1) (2 * n + 1), ∑ js ∈ range (2 * n + 1), E jr js (2 * n) * ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) = 0 := by
      apply sum_eq_zero
      intro jr hjr
      rw [mem_Ico] at hjr
      have h_split_js : ∑ js ∈ range (2 * n + 1), E jr js (2 * n) * ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) =
        ∑ js ∈ range (n + 1), E jr js (2 * n) * ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) +
        ∑ js ∈ Ico (n + 1) (2 * n + 1), E jr js (2 * n) * ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) := by
        symm
        apply sum_range_add_sum_Ico
        omega
      rw [h_split_js]
      have h_zero_js1 : ∑ js ∈ range (n + 1), E jr js (2 * n) * ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) = 0 := by
        apply sum_eq_zero
        intro js hjs
        rw [mem_range] at hjs
        have h_or : jr + js > 2 * n ∨ jr + js ≤ 2 * n := by omega
        cases h_or with
        | inl h1 =>
          have h_E : E jr js (2 * n) = 0 := E_zero_of_gt jr js (2 * n) h1
          rw [h_E, zero_mul]
        | inr h1 =>
          have h_inner : ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) = 0 := by
            have h_inner_zero := inner_sum_zero n jr js hjr.1 (by omega) h1
            have h_rearrange : ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) =
              ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * (((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ)) := by
              apply sum_congr rfl
              intro l _
              ring
            rw [h_rearrange, h_inner_zero]
          rw [h_inner, mul_zero]
      have h_zero_js2 : ∑ js ∈ Ico (n + 1) (2 * n + 1), E jr js (2 * n) * ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) = 0 := by
        apply sum_eq_zero
        intro js hjs
        rw [mem_Ico] at hjs
        have h_inner : ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) = 0 := by
          apply sum_eq_zero
          intro l hl
          rw [mem_range] at hl
          have h_choose : l.choose js = 0 := Nat.choose_eq_zero_of_lt (by omega)
          rw [h_choose]
          ring
        rw [h_inner, mul_zero]
      rw [h_zero_js1, h_zero_js2, add_zero]
    rw [h_zero_jr, add_zero]
    apply sum_congr rfl
    intro jr _
    have h_split_js : ∑ js ∈ range (2 * n + 1), E jr js (2 * n) * ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) =
      ∑ js ∈ range (n + 1), E jr js (2 * n) * ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) +
      ∑ js ∈ Ico (n + 1) (2 * n + 1), E jr js (2 * n) * ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) := by
      symm
      apply sum_range_add_sum_Ico
      omega
    rw [h_split_js]
    have h_zero_js2 : ∑ js ∈ Ico (n + 1) (2 * n + 1), E jr js (2 * n) * ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) = 0 := by
      apply sum_eq_zero
      intro js hjs
      rw [mem_Ico] at hjs
      have h_inner : ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) = 0 := by
        apply sum_eq_zero
        intro l hl
        rw [mem_range] at hl
        have h_choose : l.choose js = 0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [h_choose]
        ring
      rw [h_inner, mul_zero]
    rw [h_zero_js2, add_zero]
  rw [h_split]
  apply sum_congr rfl
  intro jr hjr
  rw [mem_range] at hjr
  apply sum_congr rfl
  intro js hjs
  rw [mem_range] at hjs
  have h_inner : ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) =
    (-1 : ℤ) ^ n * ((2 * n + 1).choose jr : ℤ) * ((2 * n + 1 - jr).choose js : ℤ) * ((2 * n - jr - js).choose (n - jr) : ℤ) := by
    have h_coef := sum_coef n jr js (by omega) (by omega)
    have h_rearrange : ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * ((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ) =
      ∑ l ∈ range (n + 1), (-1 : ℤ) ^ l * ((2 * n + 1).choose l : ℤ) * (((2 * n + 1 - l).choose jr : ℤ) * (l.choose js : ℤ)) := by
      apply sum_congr rfl
      intro l _
      ring
    rw [h_rearrange, h_coef]
    ring
  rw [h_inner]
  ring



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
