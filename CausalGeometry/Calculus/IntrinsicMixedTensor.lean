import CausalGeometry.Calculus.GeneralTensor
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.Tactic

namespace CausalGeometry

noncomputable section

universe u v

open scoped TensorProduct

/-- Basis-free mixed tensor carrier:
p contravariant vector slots and q covariant dual slots. -/
abbrev IntrinsicMixedTensor
    (K : Type u)
    (V : Type v)
    [Field K]
    [AddCommGroup V]
    [Module K V]
    (p q : ℕ) :=
  TensorPower K p V ⊗[K]
    TensorPower K q (Module.Dual K V)

namespace IntrinsicMixedTensor

variable
    {K : Type u}
    {V : Type v}
    [Field K]
    [AddCommGroup V]
    [Module K V]

/-- Bilinear multiplication on tensor powers, exposed as a curried linear map. -/
def tensorPowerMul
    (M : Type v)
    [AddCommGroup M]
    [Module K M]
    (p r : ℕ) :
    TensorPower K p M →ₗ[K]
      TensorPower K r M →ₗ[K]
        TensorPower K (p + r) M :=
  (TensorProduct.mk K _ _).compr₂
    (TensorPower.mulEquiv
      (R := K) (M := M)).toLinearMap

/-- Rebracket and reorder two mixed tensors so vector powers and dual powers
become adjacent, then concatenate each pair of tensor powers. -/
def pairTensorMap
    (p q r s : ℕ) :
    (IntrinsicMixedTensor K V p q ⊗[K]
      IntrinsicMixedTensor K V r s) →ₗ[K]
      IntrinsicMixedTensor K V (p + r) (q + s) :=
  (TensorProduct.map
      (TensorPower.mulEquiv
        (R := K) (M := V)).toLinearMap
      (TensorPower.mulEquiv
        (R := K)
        (M := Module.Dual K V)).toLinearMap).comp
    (TensorProduct.tensorTensorTensorComm
      K
      (TensorPower K p V)
      (TensorPower K q (Module.Dual K V))
      (TensorPower K r V)
      (TensorPower K s (Module.Dual K V))).toLinearMap

/-- Basis-free mixed tensor product. -/
def tensor
    (p q r s : ℕ) :
    IntrinsicMixedTensor K V p q →ₗ[K]
      IntrinsicMixedTensor K V r s →ₗ[K]
        IntrinsicMixedTensor K V (p + r) (q + s) :=
  (TensorProduct.lift.equiv
    (RingHom.id K)
    (IntrinsicMixedTensor K V p q)
    (IntrinsicMixedTensor K V r s)
    (IntrinsicMixedTensor K V (p + r) (q + s))).symm
      (pairTensorMap
        (K := K) (V := V)
        p q r s)

/-- Canonical equivalence between the first tensor power and the underlying
module. -/
def tensorPowerOneEquiv
    (M : Type v)
    [AddCommGroup M]
    [Module K M] :
    TensorPower K 1 M ≃ₗ[K] M :=
  PiTensorProduct.subsingletonEquiv
    (R := K)
    (s := fun _ : Fin 1 => M)
    (0 : Fin 1)

/-- Evaluation of one vector slot against one covector slot. -/
def contractOne :
    (TensorPower K 1 V ⊗[K]
      TensorPower K 1 (Module.Dual K V)) →ₗ[K]
      K :=
  (TensorProduct.contractRight K V).comp
    (TensorProduct.map
      (tensorPowerOneEquiv
        (K := K) V).toLinearMap
      (tensorPowerOneEquiv
        (K := K) (Module.Dual K V)).toLinearMap)

/-- Split the final vector and covector slots from a mixed tensor. -/
def splitLast
    (p q : ℕ) :
    IntrinsicMixedTensor K V (p + 1) (q + 1) ≃ₗ[K]
      ((TensorPower K p V ⊗[K] TensorPower K 1 V) ⊗[K]
        (TensorPower K q (Module.Dual K V) ⊗[K]
          TensorPower K 1 (Module.Dual K V))) :=
  TensorProduct.congr
    (TensorPower.mulEquiv
      (R := K) (M := V)).symm
    (TensorPower.mulEquiv
      (R := K)
      (M := Module.Dual K V)).symm

/-- Reorder the split tensor so the uncontracted mixed tensor is separated
from the final V tensor V* pair. -/
def groupLastPair
    (p q : ℕ) :
    ((TensorPower K p V ⊗[K] TensorPower K 1 V) ⊗[K]
      (TensorPower K q (Module.Dual K V) ⊗[K]
        TensorPower K 1 (Module.Dual K V)))
      ≃ₗ[K]
    (IntrinsicMixedTensor K V p q ⊗[K]
      (TensorPower K 1 V ⊗[K]
        TensorPower K 1 (Module.Dual K V))) :=
  TensorProduct.tensorTensorTensorComm
    K
    (TensorPower K p V)
    (TensorPower K 1 V)
    (TensorPower K q (Module.Dual K V))
    (TensorPower K 1 (Module.Dual K V))

/-- Contract the final contravariant/covariant slot pair. -/
def contract
    (p q : ℕ) :
    IntrinsicMixedTensor K V (p + 1) (q + 1) →ₗ[K]
      IntrinsicMixedTensor K V p q :=
  (TensorProduct.rid K
      (IntrinsicMixedTensor K V p q)).toLinearMap.comp
    ((TensorProduct.map
      (LinearMap.id)
      (contractOne (K := K) (V := V))).comp
      ((groupLastPair
        (K := K) (V := V) p q).toLinearMap.comp
        (splitLast
          (K := K) (V := V) p q).toLinearMap))

/-- Reindex vector tensor-power slots. -/
def permuteContravariant
    (p q : ℕ)
    (sigma : Equiv (Fin p) (Fin p)) :
    IntrinsicMixedTensor K V p q ≃ₗ[K]
      IntrinsicMixedTensor K V p q :=
  TensorProduct.congr
    (PiTensorProduct.reindex
      K (fun _ : Fin p => V) sigma)
    (LinearEquiv.refl K
      (TensorPower K q (Module.Dual K V)))

/-- Reindex dual tensor-power slots. -/
def permuteCovariant
    (p q : ℕ)
    (sigma : Equiv (Fin q) (Fin q)) :
    IntrinsicMixedTensor K V p q ≃ₗ[K]
      IntrinsicMixedTensor K V p q :=
  TensorProduct.congr
    (LinearEquiv.refl K
      (TensorPower K p V))
    (PiTensorProduct.reindex
      K
      (fun _ : Fin q => Module.Dual K V)
      sigma)

/-- Basis-free realization of the arbitrary-rank tensor calculus interface. -/
def calculus :
    GeneralCausalTensorCalculus
      K
      (IntrinsicMixedTensor K V) where

  tensor :=
    tensor

  contract :=
    contract

  permuteContravariant :=
    permuteContravariant

  permuteCovariant :=
    permuteCovariant

/-- Product formula on pure mixed tensors. -/
@[simp] theorem tensor_tmul
    {p q r s : ℕ}
    (x : TensorPower K p V)
    (alpha : TensorPower K q (Module.Dual K V))
    (y : TensorPower K r V)
    (beta : TensorPower K s (Module.Dual K V)) :
    tensor (K := K) (V := V)
        p q r s
        (x ⊗ₜ[K] alpha)
        (y ⊗ₜ[K] beta)
      =
    TensorPower.mulEquiv
        (R := K) (M := V)
        (x ⊗ₜ[K] y)
      ⊗ₜ[K]
    TensorPower.mulEquiv
        (R := K)
        (M := Module.Dual K V)
        (alpha ⊗ₜ[K] beta) := by
  rfl

/-- Contraction formula after the final slots have been explicitly split. -/
@[simp] theorem contract_split_tmul
    {p q : ℕ}
    (x : TensorPower K p V)
    (v1 : TensorPower K 1 V)
    (alpha : TensorPower K q (Module.Dual K V))
    (f1 : TensorPower K 1 (Module.Dual K V)) :
    contract (K := K) (V := V) p q
      (TensorPower.mulEquiv
          (R := K) (M := V)
          (x ⊗ₜ[K] v1)
        ⊗ₜ[K]
       TensorPower.mulEquiv
          (R := K)
          (M := Module.Dual K V)
          (alpha ⊗ₜ[K] f1))
      =
    contractOne (K := K) (V := V)
        (v1 ⊗ₜ[K] f1) •
      (x ⊗ₜ[K] alpha) := by
  simp [contract, splitLast,
    groupLastPair, contractOne,
    tensorPowerOneEquiv]

/-- Identity slot permutations are identities in the basis-free realization. -/
theorem contravariantPermutationIdentity :
    (calculus (K := K) (V := V))
      .ContravariantPermutationIdentity := by
  intro p q
  apply LinearEquiv.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero =>
      simp [permuteContravariant]
  | tmul x alpha =>
      simp [permuteContravariant]
  | add x y hx hy =>
      simp [hx, hy]

theorem covariantPermutationIdentity :
    (calculus (K := K) (V := V))
      .CovariantPermutationIdentity := by
  intro p q
  apply LinearEquiv.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero =>
      simp [permuteCovariant]
  | tmul x alpha =>
      simp [permuteCovariant]
  | add x y hx hy =>
      simp [hx, hy]

end IntrinsicMixedTensor
end

end CausalGeometry
