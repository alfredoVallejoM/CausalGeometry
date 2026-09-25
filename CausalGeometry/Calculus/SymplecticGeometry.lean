import CausalGeometry.Calculus.HamiltonianTransport
import CausalGeometry.Calculus.Soldering

namespace CausalGeometry

universe u v w x
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

/-- Causal symplectic geometry over a dependent vector fiber.

The algebraic symplectic form, the event-to-vector soldering, and exterior
closedness are independent data/obligations. -/
structure CausalSymplecticGeometry
    (K : Type w)
    (S : EventSystem Event Label)
    (Fiber : Configuration S → Type x)
    [CommRing K]
    [∀ C, AddCommGroup (Fiber C)]
    [∀ C, Module K (Fiber C)] where
  symplectic :
    CausalBilinear.SymplecticField
      (K := K) (S := S) (Fiber := Fiber)

  soldering :
    CausalSoldering S Fiber

  closed :
    (soldering.inducedTwoForm
      symplectic.toField
      symplectic.alternating).Closed

namespace CausalSymplecticGeometry

variable {K : Type w}
variable {Fiber : Configuration S → Type x}
variable [CommRing K]
variable [∀ C, AddCommGroup (Fiber C)]
variable [∀ C, Module K (Fiber C)]

variable
    (G : CausalSymplecticGeometry K S Fiber)

/-- Scalar causal two-form seen by primitive event directions. -/
def eventTwoForm :
    CausalTwoForm S K :=
  G.soldering.inducedTwoForm
    G.symplectic.toField
    G.symplectic.alternating

theorem eventTwoForm_closed :
    G.eventTwoForm.Closed :=
  G.closed

/-- Algebraic flat map at one configuration. -/
def flat
    (C : Configuration S) :
    Fiber C →ₗ[K]
      Module.Dual K (Fiber C) :=
  G.symplectic.toField.flat C

theorem flat_injective
    (C : Configuration S) :
    Function.Injective (G.flat C) :=
  G.symplectic.toField.flat_injective
    G.symplectic.nondegenerate C

end CausalSymplecticGeometry

/-- A connection compatible with a causal symplectic geometry.

Invertibility is required here because Hamiltonian covectors are transported
forward using inverse vector transport. -/
structure CausalSymplecticConnection
    (K : Type w)
    (S : EventSystem Event Label)
    (Fiber : Configuration S → Type x)
    [CommRing K]
    [∀ C, AddCommGroup (Fiber C)]
    [∀ C, Module K (Fiber C)] where
  connection :
    DependentLinearEquivConnection K S Fiber

  form :
    CausalBilinear.SymplecticField
      (K := K) (S := S) (Fiber := Fiber)

  soldering :
    CausalSoldering S Fiber

  preservesForm :
    form.toField.PreservedByEquiv connection

  preservesSoldering :
    soldering.PreservedBy
      connection.toLinearConnection

namespace CausalSymplecticConnection

variable {K : Type w}
variable {Fiber : Configuration S → Type x}
variable [CommRing K]
variable [∀ C, AddCommGroup (Fiber C)]
variable [∀ C, Module K (Fiber C)]

variable
    (G : CausalSymplecticConnection K S Fiber)

/-- Every compatible symplectic connection canonically generates a closed
causal symplectic geometry. -/
def toGeometry :
    CausalSymplecticGeometry K S Fiber where
  symplectic := G.form
  soldering := G.soldering
  closed :=
    G.soldering.inducedTwoForm_closed
      G.form.toField
      G.form.alternating
      G.connection.toLinearConnection
      G.preservesForm
      G.preservesSoldering

@[simp] theorem toGeometry_eventTwoForm :
    G.toGeometry.eventTwoForm =
      G.soldering.inducedTwoForm
        G.form.toField
        G.form.alternating :=
  rfl

/-- Compatible connection preserves flat under simultaneous vector/covector
transport. -/
theorem flat_natural
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e)
    (x : Fiber C) :
    G.form.toField.flat (S.extend C e h)
        (G.connection.transport C e h x) =
      G.connection.covectorPushforward C e h
        (G.form.toField.flat C x) :=
  G.form.toField.flat_natural
    G.connection G.preservesForm C e h x

/-- For any Hamiltonian pair defined by the same symplectic field, vector and
covector parallelism are equivalent. -/
theorem hamiltonian_parallel_iff
    (H : CausalHamiltonian.Pair G.form.toField)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    H.VectorParallelAt G.connection C e h ↔
      H.CovectorParallelAt G.connection C e h :=
  H.vectorParallel_iff_covectorParallel
    G.connection
    G.form.nondegenerate
    G.preservesForm
    C e h

/-- A Hamiltonian covector parallel under a symplectic connection determines
a parallel Hamiltonian vector. -/
theorem hamiltonian_vector_parallel
    (H : CausalHamiltonian.Pair G.form.toField)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e)
    (hcov :
      H.CovectorParallelAt
        G.connection C e h) :
    H.VectorParallelAt
      G.connection C e h :=
  (G.hamiltonian_parallel_iff
    H C e h).2 hcov

end CausalSymplecticConnection
end CausalGeometry
