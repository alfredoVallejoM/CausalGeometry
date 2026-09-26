import CausalGeometry.Calculus.CoordinateTensor
import Mathlib.Tactic

namespace CausalGeometry

universe u v

namespace CoordinateTensor

variable
    {K : Type u}
    {ι : Type v}
    [Field K]
    [Fintype ι]

/-- Symmetry under every transposition of contravariant slots. -/
def ContravariantSymmetric
    {p q : ℕ}
    (T : CoordinateTensor K ι p q) : Prop :=
  ∀ (i j : Fin p),
    i ≠ j →
      permuteContravariant p q
          (Equiv.swap i j) T
        =
      T

/-- Alternation under every transposition of contravariant slots. -/
def ContravariantAlternating
    {p q : ℕ}
    (T : CoordinateTensor K ι p q) : Prop :=
  ∀ (i j : Fin p),
    i ≠ j →
      permuteContravariant p q
          (Equiv.swap i j) T
        =
      - T

/-- Symmetry under every transposition of covariant slots. -/
def CovariantSymmetric
    {p q : ℕ}
    (T : CoordinateTensor K ι p q) : Prop :=
  ∀ (i j : Fin q),
    i ≠ j →
      permuteCovariant p q
          (Equiv.swap i j) T
        =
      T

/-- Alternation under every transposition of covariant slots. -/
def CovariantAlternating
    {p q : ℕ}
    (T : CoordinateTensor K ι p q) : Prop :=
  ∀ (i j : Fin q),
    i ≠ j →
      permuteCovariant p q
          (Equiv.swap i j) T
        =
      - T

/-- Symmetric contravariant coordinate tensors form a linear submodule. -/
def contravariantSymmetricSubmodule
    (p q : ℕ) :
    Submodule K (CoordinateTensor K ι p q) where
  carrier := {T | ContravariantSymmetric T}
  zero_mem' := by
    intro i j hij
    simp [ContravariantSymmetric]
  add_mem' := by
    intro T U hT hU i j hij
    rw [map_add, hT i j hij, hU i j hij]
  smul_mem' := by
    intro a T hT i j hij
    rw [map_smul, hT i j hij]

/-- Alternating contravariant coordinate tensors form a linear submodule. -/
def contravariantAlternatingSubmodule
    (p q : ℕ) :
    Submodule K (CoordinateTensor K ι p q) where
  carrier := {T | ContravariantAlternating T}
  zero_mem' := by
    intro i j hij
    simp [ContravariantAlternating]
  add_mem' := by
    intro T U hT hU i j hij
    rw [map_add, hT i j hij, hU i j hij]
    simp
  smul_mem' := by
    intro a T hT i j hij
    rw [map_smul, hT i j hij]
    simp

/-- Symmetric covariant coordinate tensors form a linear submodule. -/
def covariantSymmetricSubmodule
    (p q : ℕ) :
    Submodule K (CoordinateTensor K ι p q) where
  carrier := {T | CovariantSymmetric T}
  zero_mem' := by
    intro i j hij
    simp [CovariantSymmetric]
  add_mem' := by
    intro T U hT hU i j hij
    rw [map_add, hT i j hij, hU i j hij]
  smul_mem' := by
    intro a T hT i j hij
    rw [map_smul, hT i j hij]

/-- Alternating covariant coordinate tensors form a linear submodule. -/
def covariantAlternatingSubmodule
    (p q : ℕ) :
    Submodule K (CoordinateTensor K ι p q) where
  carrier := {T | CovariantAlternating T}
  zero_mem' := by
    intro i j hij
    simp [CovariantAlternating]
  add_mem' := by
    intro T U hT hU i j hij
    rw [map_add, hT i j hij, hU i j hij]
    simp
  smul_mem' := by
    intro a T hT i j hij
    rw [map_smul, hT i j hij]
    simp

/-- Coordinate symmetric 2-covariant tensors, the natural carrier for a metric
matrix in a finite frame. -/
abbrev SymmetricCovariant2 :=
  covariantSymmetricSubmodule
    (K := K) (ι := ι) 0 2

/-- Coordinate alternating q-forms as the fully covariant alternating sector. -/
abbrev ExteriorCovariant
    (q : ℕ) :=
  covariantAlternatingSubmodule
    (K := K) (ι := ι) 0 q

end CoordinateTensor
end CausalGeometry
