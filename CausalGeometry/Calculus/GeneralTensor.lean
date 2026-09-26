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

def TensorProductAssociative : Prop :=
  ∀ p q r s a b
    (x : T p q)
    (y : T r s)
    (z : T a b),
      C.tensor (p + r) (q + s) a b
          (C.tensor p q r s x y) z
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

/-- A typed contraction/tensor compatibility obligation.  The exact permutation
needed to bring a chosen vector/covector pair together is deliberately kept
outside this minimal interface and belongs to a concrete tensor realization. -/
def ContractionLinear : Prop :=
  ∀ p q,
    Function.Injective
      (fun x : T (p + 1) (q + 1) =>
        (C.contract p q) x) →
    True

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
