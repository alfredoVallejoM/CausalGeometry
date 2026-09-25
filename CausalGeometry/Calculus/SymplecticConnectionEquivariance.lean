import CausalGeometry.Calculus.ConnectionEquivariance
import CausalGeometry.Calculus.SymplecticEquivariance

namespace CausalGeometry

universe u₁ v₁ u₂ v₂ w x

open EventSystem

variable
    {Event₁ : Type u₁} {Label₁ : Type v₁}
    {Event₂ : Type u₂} {Label₂ : Type v₂}
    {S₁ : EventSystem Event₁ Label₁}
    {S₂ : EventSystem Event₂ Label₂}

namespace EventSystemEquiv

variable (E : EventSystemEquiv S₁ S₂)
variable {K : Type w}
variable {Fiber : Configuration S₂ → Type x}
variable [CommRing K]
variable [∀ C, AddCommGroup (Fiber C)]
variable [∀ C, Module K (Fiber C)]

/-- Preservation of a bilinear field survives reindexing of both the field and
the invertible dependent connection. -/
theorem pullBilinear_preservedByEquiv
    (B : CausalBilinear.Field
      (K := K) (S := S₂) (Fiber := Fiber))
    (∇ : DependentLinearEquivConnection K S₂ Fiber)
    (hB : B.PreservedByEquiv ∇) :
    (E.pullBilinearField B).PreservedByEquiv
      (E.pullDependentLinearEquivConnection ∇) := by
  intro C e h x y
  have hcfg :=
    E.map_extend C e h
  cases hcfg
  exact
    hB
      (E.mapConfiguration C)
      (E.eventEquiv e)
      ((E.enabled_iff C e).2 h)
      x y

/-- Preservation of the event-to-vector soldering also survives reindexing. -/
theorem pullSoldering_preservedBy
    (θ : CausalSoldering S₂ Fiber)
    (∇ : DependentLinearEquivConnection K S₂ Fiber)
    (hθ :
      θ.PreservedBy
        ∇.toLinearConnection) :
    (E.pullSoldering θ).PreservedBy
      (E.pullDependentLinearEquivConnection ∇)
        .toLinearConnection := by
  intro C e f d
  have htarget :=
    hθ (E.mapDiamond d)

  have hcfg :=
    E.map_afterE d
  cases hcfg

  have hafter :
      E.directionEquiv d.afterE
          (CausalOneForm.afterE_F d)
        =
      CausalOneForm.afterE_F
        (E.mapDiamond d) := by
    apply EventDirection.ext
    rfl

  have hbase :=
    E.directionEquiv_baseF d

  unfold pullSoldering
  rw [hafter, hbase]

  simpa [
    EventSystemEquiv.pullDependentLinearEquivConnection,
    DependentLinearEquivConnection.toLinearConnection
  ] using htarget

/-- Pull back a complete causal symplectic connection. -/
def pullSymplecticConnection
    (G : CausalSymplecticConnection K S₂ Fiber) :
    CausalSymplecticConnection
      K S₁ (E.pullFiber Fiber) where

  connection :=
    E.pullDependentLinearEquivConnection
      G.connection

  form :=
    E.pullSymplecticField
      G.form

  soldering :=
    E.pullSoldering
      G.soldering

  preservesForm :=
    E.pullBilinear_preservedByEquiv
      G.form.toField
      G.connection
      G.preservesForm

  preservesSoldering :=
    E.pullSoldering_preservedBy
      G.soldering
      G.connection
      G.preservesSoldering

/-- The closed event two-form produced from the pulled connection is exactly
the pullback of the original closed event two-form. -/
theorem pullSymplecticConnection_eventTwoForm
    (G : CausalSymplecticConnection K S₂ Fiber) :
    (E.pullSymplecticConnection G)
        .toGeometry.eventTwoForm
      =
    E.pullTwoForm
      G.toGeometry.eventTwoForm := by
  exact
    E.inducedTwoForm_pull
      G.soldering
      G.form.toField
      G.form.alternating

/-- Closedness is therefore representation invariant at the full connection
level. -/
theorem pullSymplecticConnection_closed
    (G : CausalSymplecticConnection K S₂ Fiber) :
    ((E.pullSymplecticConnection G)
      .toGeometry.eventTwoForm).Closed := by
  rw [E.pullSymplecticConnection_eventTwoForm]
  exact
    E.pullTwoForm_closed
      G.toGeometry.closed

/-- Pulling a Hamiltonian pair and then testing vector/covector parallelism in
the pulled symplectic connection yields a well-typed representation-independent
Hamiltonian system. -/
def pullHamiltonianPairForConnection
    (G : CausalSymplecticConnection K S₂ Fiber)
    (H : CausalHamiltonian.Pair G.form.toField) :
    CausalHamiltonian.Pair
      (E.pullSymplecticConnection G)
        .form.toField :=
  E.pullHamiltonianPair H

/-- The pulled symplectic connection retains the Hamiltonian vector/covector
parallelism equivalence. -/
theorem pullHamiltonian_parallel_iff
    (G : CausalSymplecticConnection K S₂ Fiber)
    (H : CausalHamiltonian.Pair G.form.toField)
    (C : Configuration S₁)
    (e : Event₁)
    (h : S₁.Enabled C e) :
    (E.pullHamiltonianPairForConnection G H)
        .VectorParallelAt
          (E.pullSymplecticConnection G).connection
          C e h
      ↔
    (E.pullHamiltonianPairForConnection G H)
        .CovectorParallelAt
          (E.pullSymplecticConnection G).connection
          C e h := by
  exact
    (E.pullSymplecticConnection G)
      .hamiltonian_parallel_iff
        (E.pullHamiltonianPairForConnection G H)
        C e h

end EventSystemEquiv
end CausalGeometry
