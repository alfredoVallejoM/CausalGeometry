import CausalGeometry.Calculus.Connection
import Mathlib.Tactic

namespace CausalGeometry

universe u v w
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

/-- Failure of an observable at the common square endpoint to be obtained by
transport along the e-then-f path. -/
def covariantSquareDefectEF {V : Type w} [AddCommGroup V]
    (∇ : CausalConnection S V)
    (F : Configuration S → V)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) : V :=
  F d.afterEF - ∇.transportEF d (F C)

/-- Same endpoint defect for the f-then-e path. -/
def covariantSquareDefectFE {V : Type w} [AddCommGroup V]
    (∇ : CausalConnection S V)
    (F : Configuration S → V)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) : V :=
  F d.afterFE - ∇.transportFE d (F C)

/-- Path dependence of the covariant endpoint defect is exactly negative
curvature acting on the starting observable. -/
theorem covariantSquareDefect_sub
    {V : Type w} [AddCommGroup V]
    (∇ : CausalConnection S V)
    (F : Configuration S → V)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    covariantSquareDefectEF ∇ F d -
        covariantSquareDefectFE ∇ F d =
      - ∇.curvature d (F C) := by
  unfold covariantSquareDefectEF covariantSquareDefectFE
    CausalConnection.curvature
  rw [ConcurrencyDiamond.endpoint_eq d]
  abel

/-- On a flat square the two covariant endpoint defects coincide. -/
theorem covariantSquareDefect_eq_of_flat
    {V : Type w} [AddCommGroup V]
    (∇ : CausalConnection S V)
    (F : Configuration S → V)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f)
    (h : ∇.FlatOn d) :
    covariantSquareDefectEF ∇ F d =
      covariantSquareDefectFE ∇ F d := by
  apply sub_eq_zero.mp
  rw [covariantSquareDefect_sub,
    ∇.curvature_eq_zero_of_flat d h (F C)]
  simp

end CausalGeometry
