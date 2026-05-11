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
# Matrix Multiplication Complexity

The *tensor rank* of matrix multiplication is the minimum number of scalar multiplications
needed to multiply two matrices using a bilinear algorithm. Determining this rank, even for
small matrices, is a fundamental open problem in algebraic complexity theory.

For $2 \times 2$ matrices, Strassen showed that $7$ multiplications suffice (instead of the
naive $8$), and Winograd proved this is optimal. For $4 \times 4$ matrices, the best known
algorithm over $\mathbb{Z}$ uses $49$ multiplications (Strassen applied recursively), but
the exact tensor rank remains unknown.

*References:*
- [Strassen69] Strassen, Volker. [Gaussian elimination is not optimal](https://doi.org/10.1007/BF02165411).
  Numerische Mathematik 13.4 (1969): 354-356.
- [Winograd71] Winograd, Shmuel. On multiplication of 2×2 matrices.
  Linear Algebra and its Applications 4.4 (1971): 381-388.
- [Wikipedia](https://en.wikipedia.org/wiki/Computational_complexity_of_matrix_multiplication)
- [AlphaTensor] Fawzi, Alhussein, et al.
  [Discovering faster matrix multiplication algorithms with reinforcement learning](https://doi.org/10.1038/s41586-022-05172-4).
  Nature 610.7930 (2022): 47-53.
-/

namespace MatMulComplexity

open Matrix Finset

/--
A bilinear algorithm for multiplying an $m \times n$ matrix by an $n \times p$ matrix
over a commutative ring $S$ using $R$ scalar multiplications. The algorithm is specified
by coefficient tensors $u$, $v$, $w$ such that for all matrices $A$, $B$:
$$(A \cdot B)_{ij} = \sum_{r=0}^{R-1} \left(\sum_{a,b} u_r(a,b) \cdot A_{ab}\right)
\cdot \left(\sum_{c,d} v_r(c,d) \cdot B_{cd}\right) \cdot w_r(i,j)$$
Each of the $R$ terms involves exactly one *essential* scalar multiplication (of two linear
forms in the entries of $A$ and $B$). All other operations are additions and multiplications
by constants from $S$.

Note: the algorithm must work over a commutative ring, since the bilinear form separates
the entries of $A$ and $B$ into different factors, which requires commutativity with the
algorithm coefficients.
-/
def IsMatMulAlgo (m n p R : ℕ) (S : Type*) [CommRing S]
    (u : Fin R → Fin m → Fin n → S)
    (v : Fin R → Fin n → Fin p → S)
    (w : Fin R → Fin m → Fin p → S) : Prop :=
  ∀ (A : Matrix (Fin m) (Fin n) S) (B : Matrix (Fin n) (Fin p) S)
    (i : Fin m) (j : Fin p),
    (A * B) i j = ∑ r : Fin R,
      (∑ a : Fin m, ∑ b : Fin n, u r a b * A a b) *
      (∑ c : Fin n, ∑ d : Fin p, v r c d * B c d) *
      w r i j

/-- There exists a bilinear algorithm for $n \times n$ matrix multiplication using
$R$ scalar multiplications over $S$. -/
def HasMatMulAlgo (n R : ℕ) (S : Type*) [CommRing S] : Prop :=
  ∃ u v w, IsMatMulAlgo n n n R S u v w

/-- The *tensor rank* of $n \times n$ matrix multiplication over $S$: the minimum
number of scalar multiplications in any bilinear algorithm computing the product
of two $n \times n$ matrices. -/
noncomputable def matMulRank (n : ℕ) (S : Type*) [CommRing S] : ℕ :=
  sInf {R : ℕ | HasMatMulAlgo n R S}

/--
What is the minimum number of scalar multiplications required to multiply two
$4 \times 4$ matrices over the integers?
The best known upper bound is $49$ (Strassen's algorithm applied recursively).

*Reference:*
[Wikipedia](https://en.wikipedia.org/wiki/Computational_complexity_of_matrix_multiplication)
-/
@[category research open, AMS 15 68]
theorem matmul_rank_4x4 : matMulRank 4 ℤ = answer(sorry) := by
  sorry

/--
Strassen's $2 \times 2$ algorithm uses $7$ multiplications. Applied recursively to
$4 \times 4$ matrices (viewed as $2 \times 2$ blocks of $2 \times 2$ blocks),
this yields $7^2 = 49$ multiplications.

*Reference:* [Strassen69]
-/
@[category research solved, AMS 15 68]
theorem matmul_rank_4x4_le : matMulRank 4 ℤ ≤ 49 := by
  sorry

/--
The tensor rank of $2 \times 2$ matrix multiplication is exactly $7$.
The upper bound is due to Strassen (1969) and the lower bound to Winograd (1971).

*References:* [Strassen69], [Winograd71]
-/
@[category research solved, AMS 15 68]
theorem matmul_rank_2x2 : matMulRank 2 ℤ = 7 := by
  sorry

/- ### SAT Connection

The problem of determining `HasMatMulAlgo n R (ZMod p)` can be encoded as a SAT instance:
the entries of the coefficient tensors `u`, `v`, `w` over `ZMod p` are the variables
(each ranging over `p` values), and the algorithm correctness constraint becomes a system
of polynomial equations that can be CNF-encoded.

**Key facts enabling the SAT approach:**

1. **Coefficient characterization**: `IsMatMulAlgo` is equivalent to a finite system of
   equations on the coefficient tensors (the tensor decomposition equations), defined in
   `IsMatMulAlgoCoeff`. This is the form naturally encoded as SAT/CSP.

2. **Transfer theorem**: An algorithm over `ℤ` reduces to an algorithm over `ZMod p` via
   the canonical ring homomorphism. Contrapositively, UNSAT over `ZMod p` implies no
   algorithm exists over `ℤ` either, giving a lower bound on the integer tensor rank.

3. **Certificate verification**: A SAT model (satisfying assignment) provides concrete
   coefficient tensors that can be computationally verified in Lean via `native_decide`.

**Workflow:**
- Encode `HasMatMulAlgo n R (ZMod p)` as a CNF formula externally
- Run a SAT solver on the CNF
- If **SAT**: extract `u`, `v`, `w` from the model, verify in Lean → upper bound
- If **UNSAT**: the LRAT certificate proves `¬ HasMatMulAlgo n R (ZMod p)`,
  and by `matMulRank_zmod_le` this gives `matMulRank n ℤ > R`
-/
section SATConnection

variable {S : Type*} [CommRing S]

/-- An equivalent characterization of `IsMatMulAlgo` in terms of the tensor decomposition
equations. For each sextuple $(a, b, c, d, i, j)$, the sum
$$\sum_r u_r(a,b) \cdot v_r(c,d) \cdot w_r(i,j)$$
must equal the structure constant of matrix multiplication: $1$ if $a = i$, $b = c$,
$d = j$, and $0$ otherwise.

This is the form that naturally encodes as a system of polynomial equations over a finite
field, and hence as a SAT instance. -/
def IsMatMulAlgoCoeff (n R : ℕ) (S : Type*) [CommRing S]
    (u v w : Fin R → Fin n → Fin n → S) : Prop :=
  ∀ (a b c d i j : Fin n),
    ∑ r : Fin R, u r a b * v r c d * w r i j =
      if a = i ∧ b = c ∧ d = j then 1 else 0

/-- The coefficient characterization is equivalent to `IsMatMulAlgo` for square matrices
over any nontrivial commutative ring. The proof uses the fact that the expressions are
multilinear in the matrix entries. -/
@[category API, AMS 15 68]
theorem isMatMulAlgo_iff_coeff {n R : ℕ} [Nontrivial S]
    {u v w : Fin R → Fin n → Fin n → S} :
    IsMatMulAlgo n n n R S u v w ↔ IsMatMulAlgoCoeff n R S u v w := by
  sorry

/-- Algorithms transfer along ring homomorphisms: pushing the coefficient tensors through
$f : S \to T$ preserves the tensor decomposition equations. -/
@[category API, AMS 15 68]
theorem HasMatMulAlgo.of_ringHom {n R : ℕ} {T : Type*} [CommRing T]
    (f : S →+* T) (h : HasMatMulAlgo n R S) : HasMatMulAlgo n R T := by
  sorry

/-- The tensor rank can only decrease when passing to a quotient ring.
This is an immediate consequence of `HasMatMulAlgo.of_ringHom`. -/
@[category API, AMS 15 68]
theorem matMulRank_le_of_ringHom {n : ℕ} {T : Type*} [CommRing T]
    (f : S →+* T) : matMulRank n T ≤ matMulRank n S := by
  sorry

/-- Lower bounds over $\mathbb{Z}/p\mathbb{Z}$ (which can be established via SAT/UNSAT
certificates) transfer to lower bounds over $\mathbb{Z}$.

**SAT workflow:**
- Encode `HasMatMulAlgo n R (ZMod p)` as a CNF formula
- If **UNSAT**: proves `matMulRank n (ZMod p) > R`, hence `matMulRank n ℤ > R`
- If **SAT**: the model gives concrete `u v w` over `ZMod p`, giving
  `matMulRank n (ZMod p) ≤ R` -/
@[category API, AMS 15 68]
theorem matMulRank_zmod_le (n p : ℕ) :
    matMulRank n (ZMod p) ≤ matMulRank n ℤ :=
  matMulRank_le_of_ringHom (Int.castRingHom (ZMod p))

end SATConnection

end MatMulComplexity

