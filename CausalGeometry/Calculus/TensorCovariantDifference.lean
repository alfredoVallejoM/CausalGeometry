import CausalGeometry.Calculus.DependentCovariantDifference
import CausalGeometry.Calculus.TensorTransport

namespace CausalGeometry

universe u v w x
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalTensor

variable {K : Type w}
variable {Fiber : Configuration S → Type x}
variable [CommRing K]
variable [∀ C, AddCommGroup (Fiber C)]
variable [∀ C, Module K (Fiber C)]

/-- A dependent linear connection induces a connection on rank-two covariant
tensors by transporting each factor. -/
def covariant2Connection
    (∇ : DependentLinearCausalConnection K S Fiber) :
    DependentLinearCausalConnection K S
      (fun C => Covariant2 (K := K) (Fiber := Fiber) C) where
  transport :=
    fun C e h =>
      transportCovariant2 ∇ C e h

/-- Section of the rank-two covariant tensor bundle. -/
abbrev Covariant2Section :=
  (C : Configuration S) →
    Covariant2 (K := K) (Fiber := Fiber) C

/-- Covariant finite difference of a rank-two tensor section. -/
def covariantDifference2
    (∇ : DependentLinearCausalConnection K S Fiber)
    (T : Covariant2Section
      (K := K) (S := S) (Fiber := Fiber))
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    Covariant2 (K := K) (Fiber := Fiber)
      (S.extend C e h) :=
  (covariant2Connection ∇).covariantDifference
    T C e h

/-- Section of the mixed vector-covector tensor bundle. -/
abbrev Mixed11Section :=
  (C : Configuration S) →
    Mixed11 (K := K) (Fiber := Fiber) C

/-- Covariant finite difference for mixed tensors, using the invertible vector
transport to move the covector factor forward. -/
def covariantDifferenceMixed11
    (∇ : DependentLinearEquivConnection K S Fiber)
    (T : Mixed11Section
      (K := K) (S := S) (Fiber := Fiber))
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    Mixed11 (K := K) (Fiber := Fiber)
      (S.extend C e h) :=
  T (S.extend C e h) -
    transportMixed11 ∇ C e h (T C)

/-- Pointwise scalar contraction of a mixed tensor section. -/
def contractSection
    (T : Mixed11Section
      (K := K) (S := S) (Fiber := Fiber)) :
    Configuration S → K :=
  fun C =>
    contract (K := K) (Fiber := Fiber) C (T C)

/-- Contraction commutes with covariant finite difference.

This is the discrete dependent-fiber analogue of compatibility of a connection
with the canonical pairing. -/
theorem contract_covariantDifferenceMixed11
    (∇ : DependentLinearEquivConnection K S Fiber)
    (T : Mixed11Section
      (K := K) (S := S) (Fiber := Fiber))
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    contract (K := K) (Fiber := Fiber)
        (S.extend C e h)
        (covariantDifferenceMixed11 ∇ T C e h) =
      contractSection T (S.extend C e h) -
        contractSection T C := by
  unfold covariantDifferenceMixed11 contractSection
  rw [map_sub]
  have hcontract :=
    LinearMap.congr_fun
      (contract_transportMixed11
        (K := K) (Fiber := Fiber)
        ∇ C e h)
      (T C)
  rw [hcontract]

/-- A mixed tensor section is parallel at one event when it is exactly the
transport of its old value. -/
def MixedParallelAt
    (∇ : DependentLinearEquivConnection K S Fiber)
    (T : Mixed11Section
      (K := K) (S := S) (Fiber := Fiber))
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) : Prop :=
  T (S.extend C e h) =
    transportMixed11 ∇ C e h (T C)

theorem covariantDifferenceMixed11_eq_zero_iff
    (∇ : DependentLinearEquivConnection K S Fiber)
    (T : Mixed11Section
      (K := K) (S := S) (Fiber := Fiber))
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    covariantDifferenceMixed11 ∇ T C e h = 0 ↔
      MixedParallelAt ∇ T C e h := by
  unfold covariantDifferenceMixed11 MixedParallelAt
  exact sub_eq_zero

/-- Parallel mixed tensors have constant contraction along the causal step. -/
theorem contract_constant_of_parallel
    (∇ : DependentLinearEquivConnection K S Fiber)
    (T : Mixed11Section
      (K := K) (S := S) (Fiber := Fiber))
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e)
    (hparallel : MixedParallelAt ∇ T C e h) :
    contractSection T (S.extend C e h) =
      contractSection T C := by
  have hzero :
      covariantDifferenceMixed11 ∇ T C e h = 0 :=
    (covariantDifferenceMixed11_eq_zero_iff
      ∇ T C e h).2 hparallel
  have hc :=
    contract_covariantDifferenceMixed11
      ∇ T C e h
  rw [hzero, map_zero] at hc
  exact sub_eq_zero.mp hc.symm

end CausalTensor
end CausalGeometry
