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
module

public import Mathlib.NumberTheory.ArithmeticFunction.Defs

@[expose] public section

/-!
# Additive arithmetic functions

An arithmetic function `f` is *additive* if `f 1 = 0` and `f (m * n) = f m + f n` whenever `m`
and `n` are coprime, *completely additive* if the latter holds for all nonzero `m` and `n`, and
*strongly additive* if it is additive and `f (p ^ k) = f p` for every prime `p` and every `k ≠ 0`.

These are the additive counterparts of `ArithmeticFunction.IsMultiplicative`, and follow the
same conventions: as there, the value at `1` is part of the definition.
-/

namespace ArithmeticFunction

variable {R : Type*} [AddMonoid R]

/-- Additive functions -/
structure IsAdditive (f : ArithmeticFunction R) : Prop where
  map_one : f 1 = 0
  map_mul_of_coprime : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m + f n

/-- Completely additive functions -/
structure IsCompletelyAdditive (f : ArithmeticFunction R) : Prop where
  map_one : f 1 = 0
  map_mul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → f (m * n) = f m + f n

/-- Strongly additive functions: additive functions with `f (p ^ k) = f p` for every prime `p`
and every `k ≠ 0`. -/
structure IsStronglyAdditive (f : ArithmeticFunction R) : Prop extends f.IsAdditive where
  map_prime_pow : ∀ {p k : ℕ}, p.Prime → k ≠ 0 → f (p ^ k) = f p

attribute [simp] IsAdditive.map_one IsAdditive.map_mul_of_coprime IsCompletelyAdditive.map_one

namespace IsCompletelyAdditive

variable {f : ArithmeticFunction R}

theorem isAdditive (hf : f.IsCompletelyAdditive) : f.IsAdditive := by
  refine ⟨hf.map_one, fun {m n} hmn => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · rw [Nat.coprime_zero_left] at hmn
    simp [hmn, hf.map_one]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.coprime_zero_right] at hmn
    simp [hmn, hf.map_one]
  exact hf.map_mul hm hn

theorem map_pow (hf : f.IsCompletelyAdditive) {m : ℕ} (hm : m ≠ 0) (k : ℕ) :
    f (m ^ k) = k • f m := by
  induction k with
  | zero => simp [hf.map_one]
  | succ k ih => rw [pow_succ, hf.map_mul (pow_ne_zero _ hm) hm, ih, succ_nsmul]

theorem map_prime_pow (hf : f.IsCompletelyAdditive) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    f (p ^ k) = k • f p :=
  hf.map_pow hp.ne_zero k

end IsCompletelyAdditive

end ArithmeticFunction
