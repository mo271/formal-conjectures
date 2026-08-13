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

import FormalConjecturesUtil

/-!
# Decimal expansion of $207/208$

Decimal expansion of the fraction $207/208$.

*References:*
- [A379732](https://oeis.org/A379732)
-/
open Nat

namespace OeisA379732


-- The provided Lean code for the sequence definition is replicated here.
/--
Decimal expansion of $207/208$.
-/
def a (n : ℕ) : ℕ :=
  let p := 207
  let q := 208
  let power_of_10 := 10 ^ (n + 1)
  -- The expression calculates $\lfloor \frac{p \cdot 10^{n+1}}{q} \rfloor \pmod{10}$
  let I := (p * power_of_10) / q
  I % 10

/--
The maximum packing density $\eta_{\max}$ of truncated tetrahedra.
-/
opaque max_packing_density_truncated_tetrahedra : Real

/--
a Conjectured densest packing of truncated tetrahedra.
The maximum packing density $\eta_{\max}$ of congruent truncated tetrahedra in 3D Euclidean space
is conjectured to be $207/208$.
-/
@[category research open, AMS 11]
theorem conjecture : max_packing_density_truncated_tetrahedra = (207 : Real) / 208 :=
by sorry

end OeisA379732
