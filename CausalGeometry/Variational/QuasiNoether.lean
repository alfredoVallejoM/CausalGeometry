import CausalGeometry.Variational.CausalSymmetry
import CausalGeometry.Variational.ActionGauge
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalVariational

variable {K : Type w} [AddCommGroup K]

/-- A quasi-symmetry preserves the Lagrangian up to one exact configuration
boundary term. -/
def LagrangianQuasiSymmetry
    (E : EventSystemEquiv S S)
    (L : CausalStepLagrangian S K)
    (B : Configuration S → K) : Prop :=
  pullStepLagrangian E L =
    addBoundary L B

/-- Boundary/Noether charge carried by an ordered pair of configurations. -/
def boundaryCharge
    (B : Configuration S → K)
    (C D : Configuration S) : K :=
  B D - B C

@[simp] theorem boundaryCharge_self
    (B : Configuration S → K)
    (C : Configuration S) :
    boundaryCharge B C C = 0 := by
  simp [boundaryCharge]

/-- Boundary charges compose additively along intermediate configurations. -/
theorem boundaryCharge_comp
    (B : Configuration S → K)
    (C D E : Configuration S) :
    boundaryCharge B C E =
      boundaryCharge B C D +
        boundaryCharge B D E := by
  unfold boundaryCharge
  abel

theorem boundaryCharge_symm
    (B : Configuration S → K)
    (C D : Configuration S) :
    boundaryCharge B D C =
      - boundaryCharge B C D := by
  unfold boundaryCharge
  abel

/-- Noether boundary law for arbitrary paths.

A quasi-symmetry changes the full causal action only by the endpoint charge. -/
theorem pathAction_quasiSymmetry
    (E : EventSystemEquiv S S)
    (L : CausalStepLagrangian S K)
    (B : Configuration S → K)
    (hQ : LagrangianQuasiSymmetry E L B)
    {C D : Configuration S}
    (p : CausalPath S C D) :
    pathAction L (E.mapPath p) =
      pathAction L p +
        boundaryCharge B C D := by
  rw [pathAction_natural]
  rw [hQ]
  rw [pathAction_addBoundary]
  rfl

/-- Fixed-endpoint form of the quasi-Noether law. -/
theorem noether_actionDifference_eq_boundaryCharge
    (E : EventSystemEquiv S S)
    (L : CausalStepLagrangian S K)
    (B : Configuration S → K)
    (hQ : LagrangianQuasiSymmetry E L B)
    {C D : Configuration S}
    (hC : E.mapConfiguration C = C)
    (hD : E.mapConfiguration D = D)
    (p : CausalPath S C D) :
    actionDifference L
        (fixedEndpointSymmetryPath
          E hC hD p)
        p
      =
    boundaryCharge B C D := by
  unfold actionDifference
  unfold fixedEndpointSymmetryPath
  rw [pathAction_castEnd, pathAction_castStart]
  rw [pathAction_quasiSymmetry E L B hQ p]
  abel

/-- A quasi-symmetry becomes action-preserving on any endpoint pair on which
its boundary charge vanishes. -/
theorem noether_actionDifference_zero_of_charge_zero
    (E : EventSystemEquiv S S)
    (L : CausalStepLagrangian S K)
    (B : Configuration S → K)
    (hQ : LagrangianQuasiSymmetry E L B)
    {C D : Configuration S}
    (hC : E.mapConfiguration C = C)
    (hD : E.mapConfiguration D = D)
    (hcharge : boundaryCharge B C D = 0)
    (p : CausalPath S C D) :
    actionDifference L
        (fixedEndpointSymmetryPath
          E hC hD p)
        p
      =
    0 := by
  rw [noether_actionDifference_eq_boundaryCharge
    E L B hQ hC hD p]
  exact hcharge

/-- Exact Lagrangian symmetry is the special quasi-symmetry with zero boundary
potential. -/
theorem quasiSymmetry_zero_of_symmetry
    (E : EventSystemEquiv S S)
    (L : CausalStepLagrangian S K)
    (hL : LagrangianSymmetry E L) :
    LagrangianQuasiSymmetry E L
      (fun _ => 0) := by
  unfold LagrangianQuasiSymmetry
  rw [hL]
  funext C e h
  simp [addBoundary]

/-- The previous exact Noether theorem is recovered from the quasi-symmetry
boundary law. -/
theorem noether_exact_as_quasi
    (E : EventSystemEquiv S S)
    (L : CausalStepLagrangian S K)
    (hL : LagrangianSymmetry E L)
    {C D : Configuration S}
    (hC : E.mapConfiguration C = C)
    (hD : E.mapConfiguration D = D)
    (p : CausalPath S C D) :
    actionDifference L
        (fixedEndpointSymmetryPath
          E hC hD p)
        p
      =
    0 := by
  have hQ :=
    quasiSymmetry_zero_of_symmetry E L hL
  have h :=
    noether_actionDifference_eq_boundaryCharge
      E L (fun _ => 0) hQ hC hD p
  simpa [boundaryCharge] using h

end CausalVariational
end CausalGeometry
