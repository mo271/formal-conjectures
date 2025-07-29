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

import Mathlib.Data.Nat.PrimeFin

namespace Nat

/--
A natural number `n` is said to be `k`-full if for every prime `p` that divides `n`, `p^k`
also divides `n`.
-/
def Full (k : ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p^k ∣ n

theorem full_of_succ_full (k : ℕ) (n : ℕ) (h : (k + 1).Full n) : k.Full n := by
  unfold Full at *
  intro hp
  exact fun a ↦ dvd_of_mul_right_dvd (h hp a)
