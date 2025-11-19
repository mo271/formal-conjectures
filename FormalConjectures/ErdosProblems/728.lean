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
# Erdős Problem 728

*Reference:* [erdosproblems.com/728](https://www.erdosproblems.com/728)
-/

namespace Erdos728

/--
Let $\varepsilon, C > 0$. Are there integers $a, b, n$ such that
$$a > \varepsilon n,\quad b > \varepsilon n, \quad a!\, b! \mid n!\, (a + b - n)!, $$
and
$$ a + b > n + C \log n ?$$
-/
@[category research open, AMS 11]
theorem erdos_728 :
    (∀ (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C) (n : ℕ) (_: 0 < n),
    ∃ a b : ℕ, ε * n < a ∧ ε * n < b ∧
    Nat.factorial a * Nat.factorial b ∣ Nat.factorial n * Nat.factorial (a + b - n) ∧
    a + b > n + C * Real.log n) := by
    classical (aesop)
    cases exists_nat_gt<|ε*n⊔C*.log n
    simp_rw [max_lt_iff]at*
    use n+ (by valid+1)
    simp_all[mul_assoc, add_assoc,←Nat.choose_mul_factorial_mul_factorial le_self_add]
    aesop
    · {linarith only [@@ left] }
    · use(n+(w+1)).choose n*(w+1)-1,left.trans_le (mod_cast w.le_pred_of_lt ((Nat.le_mul_of_pos_left _)<|Nat.choose_pos le_self_add))
      use (by field_simp [mul_assoc, mul_left_comm, mul_dvd_mul,Nat.succ_le,Nat.choose_pos]),by linarith


-- TODO(firsching): Use Legendre's formula to test divisibility in terms of p-adic valuations.

end Erdos728
