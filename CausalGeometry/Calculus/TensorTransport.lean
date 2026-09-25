import CausalGeometry.Calculus.DependentLinearConnection
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.Lift

namespace CausalGeometry

universe u v w x
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalTensor

variable {K : Type w}
variable {Fiber : Configuration S → Type x}
variable [CommSemiring K]
variable [∀ C, AddCommMonoid (Fiber C)]
variable [∀ C, Module K (Fiber C)]

/-- Pure rank-two covariant tensor fiber. -/
abbrev Covariant2
    (C : Configuration S) :=
  Fiber C ⊗[K] Fiber C

/-- Mixed vector-covector tensor fiber. -/
abbrev Mixed11
    (C : Configuration S) :=
  Fiber C ⊗[K] Module.Dual K (Fiber C)

/-- Any dependent linear connection pushes rank-two covariant tensors forward
factorwise. -/
def transportCovariant2
    (∇ : DependentLinearCausalConnection K S Fiber)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    Covariant2 (Fiber := Fiber) C →ₗ[K]
      Covariant2 (Fiber := Fiber)
        (S.extend C e h) :=
  TensorProduct.map
    (∇.transport C e h)
    (∇.transport C e h)

@[simp] theorem transportCovariant2_tmul
    (∇ : DependentLinearCausalConnection K S Fiber)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e)
    (x y : Fiber C) :
    transportCovariant2 ∇ C e h
        (x ⊗ₜ[K] y) =
      (∇.transport C e h x) ⊗ₜ[K]
        (∇.transport C e h y) := by
  simp [transportCovariant2]

/-- Mixed tensors can be transported covariantly only when vector transport is
invertible, because the covector factor must use inverse vector transport. -/
def transportMixed11
    (∇ : DependentLinearEquivConnection K S Fiber)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    Mixed11 (Fiber := Fiber) C →ₗ[K]
      Mixed11 (Fiber := Fiber)
        (S.extend C e h) :=
  TensorProduct.map
    (∇.transport C e h).toLinearMap
    (∇.covectorPushforward C e h)

@[simp] theorem transportMixed11_tmul
    (∇ : DependentLinearEquivConnection K S Fiber)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e)
    (x : Fiber C)
    (ω : Module.Dual K (Fiber C)) :
    transportMixed11 ∇ C e h
        (x ⊗ₜ[K] ω) =
      (∇.transport C e h x) ⊗ₜ[K]
        (∇.covectorPushforward C e h ω) := by
  simp [transportMixed11]

/-- Canonical contraction V tensor V* -> K.

No metric, basis or identification V = V* is used. -/
def contract
    (C : Configuration S) :
    Mixed11 (K := K) (Fiber := Fiber) C →ₗ[K] K :=
  TensorProduct.lift
    (LinearMap.mk₂ K
      (fun x ω => ω x)
      (by
        intro x y ω
        simp)
      (by
        intro a x ω
        simp)
      (by
        intro x ω η
        simp)
      (by
        intro a x ω
        simp))

@[simp] theorem contract_tmul
    (C : Configuration S)
    (x : Fiber C)
    (ω : Module.Dual K (Fiber C)) :
    contract (K := K) (Fiber := Fiber) C
        (x ⊗ₜ[K] ω) =
      ω x := by
  rw [contract, TensorProduct.lift.tmul]
  rfl

/-- Contraction is preserved exactly by simultaneous forward transport of the
vector and covector factors. -/
theorem contract_transportMixed11
    (∇ : DependentLinearEquivConnection K S Fiber)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    (contract
        (K := K) (Fiber := Fiber)
        (S.extend C e h)).comp
        (transportMixed11 ∇ C e h) =
      contract
        (K := K) (Fiber := Fiber) C := by
  apply TensorProduct.ext'
  intro x ω
  simp [transportMixed11, contract,
    TensorProduct.map_tmul,
    DependentLinearEquivConnection.pairing_preserved]

/-- Pure tensor transport does not need invertibility, while contraction
compatibility does. This theorem records the exact boundary in one statement. -/
theorem covariant_transport_exists_without_inverse
    (∇ : DependentLinearCausalConnection K S Fiber)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    Nonempty
      (Covariant2 (Fiber := Fiber) C →ₗ[K]
        Covariant2 (Fiber := Fiber)
          (S.extend C e h)) :=
  ⟨transportCovariant2 ∇ C e h⟩

end CausalTensor
end CausalGeometry
