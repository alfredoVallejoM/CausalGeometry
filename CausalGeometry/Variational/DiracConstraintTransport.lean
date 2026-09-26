import CausalGeometry.Variational.SingularLegendreConstraints
import Mathlib.Tactic

namespace CausalGeometry

universe u v w x
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalBilinear
namespace Field

variable {K : Type w}
variable {Fiber : Configuration S → Type x}
variable [CommRing K]
variable [∀ C, AddCommGroup (Fiber C)]
variable [∀ C, Module K (Fiber C)]

variable
    (B : Field (K := K) (S := S) (Fiber := Fiber))
    (nabla : DependentLinearEquivConnection K S Fiber)

/-- Vector transport descends to the physical quotient by gauge directions. -/
def reducedVelocityTransport
    (hpres : B.PreservedByEquiv nabla)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    B.ReducedVelocity C →ₗ[K]
      B.ReducedVelocity (S.extend C e h) :=

  (B.GaugeDirections C).mapQ
    (B.GaugeDirections (S.extend C e h))
    (nabla.transport C e h).toLinearMap
    (by
      intro x hx
      change
        nabla.transport C e h x ∈
          B.GaugeDirections (S.extend C e h)
      exact
        (B.gaugeDirectionTransport
          nabla hpres C e h)
          ⟨x, hx⟩ |>.2)

/-- Covector transport descends to the primary-constraint cokernel. -/
def constraintCokernelTransport
    (hpres : B.PreservedByEquiv nabla)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    B.ConstraintCokernel C →ₗ[K]
      B.ConstraintCokernel (S.extend C e h) :=

  (B.PrimaryConstraint C).mapQ
    (B.PrimaryConstraint (S.extend C e h))
    (nabla.covectorPushforward C e h)
    (by
      intro omega homega
      exact
        B.primaryConstraint_preserved
          nabla hpres C e h omega homega)

@[simp] theorem reducedVelocityTransport_mk
    (hpres : B.PreservedByEquiv nabla)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e)
    (x : Fiber C) :
    B.reducedVelocityTransport
        nabla hpres C e h
        (Submodule.Quotient.mk x)
      =
    Submodule.Quotient.mk
      (nabla.transport C e h x) :=
  rfl

@[simp] theorem constraintCokernelTransport_mk
    (hpres : B.PreservedByEquiv nabla)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e)
    (omega : Module.Dual K (Fiber C)) :
    B.constraintCokernelTransport
        nabla hpres C e h
        (Submodule.Quotient.mk omega)
      =
    Submodule.Quotient.mk
      (nabla.covectorPushforward C e h omega) :=
  rfl

/-- The physical quotient-to-primary-surface isomorphism is natural under
causal transport preserving the bilinear field. -/
theorem reducedPrimary_transport_commutes
    (hpres : B.PreservedByEquiv nabla)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e)
    (q : B.ReducedVelocity C) :
    B.primaryConstraintTransport
        nabla hpres C e h
        (B.reducedVelocityEquivPrimary C q)
      =
    B.reducedVelocityEquivPrimary
        (S.extend C e h)
        (B.reducedVelocityTransport
          nabla hpres C e h q) := by

  induction q using Submodule.Quotient.induction_on with
  | _ x =>
      apply Subtype.ext
      change
        nabla.covectorPushforward C e h
            (B.flat C x)
          =
        B.flat (S.extend C e h)
          (nabla.transport C e h x)
      exact
        (B.flat_natural
          nabla hpres C e h x).symm

/-- Primary-admissible covectors have zero obstruction class before and after
preserved transport. -/
theorem constraintClass_transport_zero_of_primary
    (hpres : B.PreservedByEquiv nabla)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e)
    (omega : Module.Dual K (Fiber C))
    (homega : omega ∈ B.PrimaryConstraint C) :
    B.primaryConstraintClass
        (S.extend C e h)
        (nabla.covectorPushforward C e h omega)
      =
    0 := by
  rw [B.primaryConstraintClass_eq_zero_iff]
  exact
    B.primaryConstraint_preserved
      nabla hpres C e h omega homega

end Field
end CausalBilinear
end CausalGeometry
