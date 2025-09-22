import FormalConjectures.Util.ProblemImports

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

example : ({1, 2, 3} : Finset ℕ) ≤ {1,3,4} :=  by
  decide

open Set Finset

def IsSubmodular (f : (Finset Ω) → ℕ) : Prop :=
  ∀ (S T : Finset Ω), f (T ∪ S) + f (S ∩ T) ≤ f T + f S

def SubmodularIndecomposable (f : (Finset Ω) → ℕ) : Prop :=
  ∀ (g h :  (Finset Ω) → ℕ),
  IsSubmodular g → IsSubmodular h → f = g + h →
  ∃ c_g : ℕ, g = c_g • f ∧
  ∃ c_h : ℕ, h = c_h • f

def IsMinimal (f : (Finset Ω) → ℕ) : Prop :=
  (univ : Finset (Finset Ω)).gcd f = 1


theorem krasse_vermutung (f : (Finset Ω) → ℕ)
    (h₁ : IsSubmodular f) (h₂ : SubmodularIndecomposable f)
    (h₃ : IsMinimal f) (h₄ : Monotone f):
    let n := Fintype.card Ω
    f ≤ 2 ^ n := by
  sorry


  delta IsMinimal IsSubmodular SubmodularIndecomposable at *
  (first |contrapose! h₂)
  exact ⟨0, f, by aesop⟩
