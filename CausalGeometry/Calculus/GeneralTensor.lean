import Mathlib.LinearAlgebra.Basic
import Mathlib.Tactic

namespace CausalGeometry

universe u v

/-- Operations of an arbitrary (p,q)-tensor calculus.

The tensor carriers are supplied by a realization.  This interface does not
force a particular concrete tensor-product encoding; it records exactly the
operations that higher causal geometry may consume. -/
structure GeneralCausalTensorCalculus
    (K : Type u)
    (T : ℕ → ℕ → Type v)
    [Field K]
    [∀ p q, AddCommGroup (T p q)]
    [∀ p q, Module K (T p q)] where

  tensor :
    ∀ p q r s,
      T p q →ₗ[K]
        T r s →ₗ[K]
          T (p + r) (q + s)

  contract :
    ∀ p q,
      T (p + 1) (q + 1) →ₗ[K]
        T p q

  permuteContravariant :
    ∀ p q,
      Equiv (Fin p) (Fin p) →
        T p q ≃ₗ[K] T p q

  permuteCovariant :
    ∀ p q,
      Equiv (Fin q) (Fin q) →
        T p q ≃ₗ[K] T p q

namespace GeneralCausalTensorCalculus

variable
    {K : Type u}
    {T : ℕ → ℕ → Type v}
    [Field K]
    [∀ p q, AddCommGroup (T p q)]
    [∀ p q, Module K (T p q)]
    (C : GeneralCausalTensorCalculus K T)

/-- Transport a tensor across proven equalities of its two ranks. -/
def castRanks
    {p p' q q' : ℕ}
    (hp : p = p')
    (hq : q = q')
    (x : T p q) :
    T p' q' := by
  cases hp
  cases hq
  exact x

@[simp] theorem castRanks_rfl
    (p q : ℕ)
    (x : T p q) :
    castRanks (C := C) rfl rfl x = x :=
  rfl

/-- Associativity of tensor product, with the unavoidable rank transport made
explicit instead of relying on definitional equality of natural-number sums. -/
def TensorProductAssociative : Prop :=
  ∀ p q r s a b
    (x : T p q)
    (y : T r s)
    (z : T a b),
      castRanks
          (C := C)
          (Nat.add_assoc p r a)
          (Nat.add_assoc q s b)
          (C.tensor (p + r) (q + s) a b
            (C.tensor p q r s x y) z)
        =
      C.tensor p q (r + a) (s + b)
        x (C.tensor r s a b y z)

def ContravariantPermutationIdentity : Prop :=
  ∀ p q,
    C.permuteContravariant p q (Equiv.refl (Fin p)) =
      LinearEquiv.refl K (T p q)

def CovariantPermutationIdentity : Prop :=
  ∀ p q,
    C.permuteCovariant p q (Equiv.refl (Fin q)) =
      LinearEquiv.refl K (T p q)

/-- Contraction is already K-linear by its type.  Additional compatibility with
chosen slots, permutations and tensor products belongs to a concrete tensor
realization and must be proved there rather than inserted as vacuous data. -/
@[simp] theorem contract_zero
    (p q : ℕ) :
    C.contract p q
        (0 : T (p + 1) (q + 1)) =
      0 := by
  exact map_zero (C.contract p q)

@[simp] theorem tensor_zero_left
    (p q r s : ℕ)
    (y : T r s) :
    C.tensor p q r s
        (0 : T p q) y =
      0 := by
  simp

@[simp] theorem tensor_zero_right
    (p q r s : ℕ)
    (x : T p q) :
    C.tensor p q r s x
        (0 : T r s) =
      0 := by
  simp

end GeneralCausalTensorCalculus

/-- Degreewise tensor transport.  It is separate from the tensor calculus so
that transport may exist without preserving products or contractions. -/
structure GeneralCausalTensorTransport
    {K : Type u}
    {T : ℕ → ℕ → Type v}
    [Field K]
    [∀ p q, AddCommGroup (T p q)]
    [∀ p q, Module K (T p q)]
    (C : GeneralCausalTensorCalculus K T) where

  map : ∀ p q, T p q →ₗ[K] T p q

namespace GeneralCausalTensorTransport

variable
    {K : Type u}
    {T : ℕ → ℕ → Type v}
    [Field K]
    [∀ p q, AddCommGroup (T p q)]
    [∀ p q, Module K (T p q)]
    {C : GeneralCausalTensorCalculus K T}
    (F : GeneralCausalTensorTransport C)

def TensorNatural : Prop :=
  ∀ p q r s
    (x : T p q)
    (y : T r s),
      F.map (p + r) (q + s)
          (C.tensor p q r s x y)
        =
      C.tensor p q r s
        (F.map p q x)
        (F.map r s y)

def ContractionNatural : Prop :=
  ∀ p q
    (x : T (p + 1) (q + 1)),
      F.map p q (C.contract p q x)
        =
      C.contract p q
        (F.map (p + 1) (q + 1) x)

end GeneralCausalTensorTransport
end CausalGeometry
