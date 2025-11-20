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

open Filter Topology
/--
Let $C > 0$. For all sufficiently small $\varepsilon>0$, there are infinitely many $n$,
such that there are $a, b$ such that
$$\varepsilon n < a < n,\quad \varepsilon n < b < n, \quad a!\, b! \mid n!\, (a + b - n)!, $$
and
$$ a + b > n + C \log n ?$$
-/
@[category research solved, AMS 11]
theorem erdos_728 (C : ℝ) (hC : 0 < C) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∃ᶠ n : ℕ in atTop,
      ∃ a < n, ∃ b < n,
        ε * n < a ∧ ε * n < b ∧
        a.factorial * b.factorial ∣ n.factorial * (a + b - n).factorial ∧
        n + C * Real.log n < a + b := by sorry

/--
Let $C > 0$. For all sufficiently small $\varepsilon>0$, there are infinitely many $n$,
such that there are $a, b$ such that
$$\varepsilon n < a < n,\quad \varepsilon n < b < n, \quad a!\, b! \mid n!\, (a + b - n)!, $$
and
$$ a + b > n + C \log n ?$$
-/
@[category research solved, AMS 11]
theorem erdos_728.variant_eventually (C : ℝ) (hC : 0 < C) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᶠ n : ℕ in atTop,
      ∃ a < n, ∃ b < n,
        ε * n < a ∧ ε * n < b ∧
        a.factorial * b.factorial ∣ n.factorial * (a + b - n).factorial ∧
        n + C * Real.log n < a + b := by sorry


end Erdos728
