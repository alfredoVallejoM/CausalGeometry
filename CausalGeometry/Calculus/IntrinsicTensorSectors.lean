import CausalGeometry.Calculus.IntrinsicMixedTensor
import Mathlib.Tactic

namespace CausalGeometry

noncomputable section

universe u v

namespace IntrinsicMixedTensor

variable
    {K : Type u}
    {V : Type v}
    [Field K]
    [AddCommGroup V]
    [Module K V]

def ContravariantSymmetric
    {p q : ℕ}
    (T : IntrinsicMixedTensor K V p q) : Prop :=
  ∀ (i j : Fin p),
    i ≠ j →
      permuteContravariant
          (K := K) (V := V)
          p q (Equiv.swap i j) T
        =
      T

def ContravariantAlternating
    {p q : ℕ}
    (T : IntrinsicMixedTensor K V p q) : Prop :=
  ∀ (i j : Fin p),
    i ≠ j →
      permuteContravariant
          (K := K) (V := V)
          p q (Equiv.swap i j) T
        =
      -T

def CovariantSymmetric
    {p q : ℕ}
    (T : IntrinsicMixedTensor K V p q) : Prop :=
  ∀ (i j : Fin q),
    i ≠ j →
      permuteCovariant
          (K := K) (V := V)
          p q (Equiv.swap i j) T
        =
      T

def CovariantAlternating
    {p q : ℕ}
    (T : IntrinsicMixedTensor K V p q) : Prop :=
  ∀ (i j : Fin q),
    i ≠ j →
      permuteCovariant
          (K := K) (V := V)
          p q (Equiv.swap i j) T
        =
      -T

def contravariantSymmetricSubmodule
    (p q : ℕ) :
    Submodule K
      (IntrinsicMixedTensor K V p q) where
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

def contravariantAlternatingSubmodule
    (p q : ℕ) :
    Submodule K
      (IntrinsicMixedTensor K V p q) where
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

def covariantSymmetricSubmodule
    (p q : ℕ) :
    Submodule K
      (IntrinsicMixedTensor K V p q) where
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

def covariantAlternatingSubmodule
    (p q : ℕ) :
    Submodule K
      (IntrinsicMixedTensor K V p q) where
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

/-- Basis-free symmetric covariant rank-two tensors. -/
abbrev SymmetricCovariant2 :=
  covariantSymmetricSubmodule
    (K := K) (V := V) 0 2

/-- Basis-free fully covariant alternating q-tensors. -/
abbrev ExteriorCovariant
    (q : ℕ) :=
  covariantAlternatingSubmodule
    (K := K) (V := V) 0 q

end IntrinsicMixedTensor
end

end CausalGeometry
