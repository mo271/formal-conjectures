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

/-- The Zhang formula agrees with the direct formula. -/
@[category API, AMS 5]
theorem zhang_eq_a (n : ℕ) : zhang n = a n := by
  sorry

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

@[category test, AMS 5]
theorem zhang_6 : zhang 6 = 743288515164 := by decide +native

@[category test, AMS 5]
theorem zhang_8 : zhang 8 = 455522635895576646 := by decide +native

@[category test, AMS 5]
theorem zhang_10 : zhang 10 = 763820398700983273655796 := by decide +native

end OeisA177043
