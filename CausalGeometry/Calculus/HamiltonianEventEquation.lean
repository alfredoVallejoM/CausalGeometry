import CausalGeometry.Calculus.SymplecticGeometry
import CausalGeometry.Calculus.ExteriorComplex

namespace CausalGeometry

universe u v w x
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalHamiltonian

variable {K : Type w}
variable {Fiber : Configuration S → Type x}
variable [CommRing K]
variable [∀ C, AddCommGroup (Fiber C)]
variable [∀ C, Module K (Fiber C)]

/-- Observe a covector section only along primitive causal directions through a
chosen soldering. -/
def covectorOneForm
    (θ : CausalSoldering S Fiber)
    (α : CovectorSection
      (K := K) (S := S) (Fiber := Fiber)) :
    CausalOneForm S K where
  value := fun C d =>
    α C (θ.vector C d)

/-- Contract a vector section with a bilinear field, then observe the second
slot along soldered causal directions. -/
def contractionOneForm
    (B : CausalBilinear.Field
      (K := K) (S := S) (Fiber := Fiber))
    (θ : CausalSoldering S Fiber)
    (X : VectorSection (S := S) (Fiber := Fiber)) :
    CausalOneForm S K where
  value := fun C d =>
    B.form C (X C) (θ.vector C d)

@[simp] theorem covectorOneForm_value
    (θ : CausalSoldering S Fiber)
    (α : CovectorSection
      (K := K) (S := S) (Fiber := Fiber))
    (C : Configuration S)
    (d : EventDirection S C) :
    (covectorOneForm θ α).value C d =
      α C (θ.vector C d) :=
  rfl

@[simp] theorem contractionOneForm_value
    (B : CausalBilinear.Field
      (K := K) (S := S) (Fiber := Fiber))
    (θ : CausalSoldering S Fiber)
    (X : VectorSection (S := S) (Fiber := Fiber))
    (C : Configuration S)
    (d : EventDirection S C) :
    (contractionOneForm B θ X).value C d =
      B.form C (X C) (θ.vector C d) :=
  rfl

/-- Hamiltonian flatness converts vector contraction into the observed
covector one-form. -/
theorem Pair.contractionOneForm_eq_covectorOneForm
    {B : CausalBilinear.Field
      (K := K) (S := S) (Fiber := Fiber)}
    (H : Pair B)
    (θ : CausalSoldering S Fiber) :
    contractionOneForm B θ H.vector =
      covectorOneForm θ H.covector := by
  apply CausalOneForm.ext
  intro C d
  rw [contractionOneForm_value,
    covectorOneForm_value]
  exact LinearMap.congr_fun
    (H.hamiltonian C) (θ.vector C d)

/-- A Hamiltonian pair with a scalar causal potential.

The covector section is not defined to be a continuous differential.  The
only requirement is that, when evaluated on soldered primitive directions, it
reproduces the discrete causal difference of the scalar potential. -/
structure PotentialPair
    (B : CausalBilinear.Field
      (K := K) (S := S) (Fiber := Fiber))
    (θ : CausalSoldering S Fiber)
    extends Pair B where
  potential :
    Configuration S → K

  differential_on_directions :
    ∀ (C : Configuration S)
      (d : EventDirection S C),
      toPair.covector C
          (θ.vector C d) =
        causalDifference potential C
          d.event d.enabled

namespace PotentialPair

variable
    {B : CausalBilinear.Field
      (K := K) (S := S) (Fiber := Fiber)}
    {θ : CausalSoldering S Fiber}
    (H : PotentialPair B θ)

/-- The observed covector one-form is exactly the exact causal one-form of the
potential. -/
theorem covectorOneForm_eq_exact :
    covectorOneForm θ H.toPair.covector =
      CausalOneForm.exact H.potential := by
  apply CausalOneForm.ext
  intro C d
  exact H.differential_on_directions C d

/-- The vector contraction one-form is therefore also exact. -/
theorem contractionOneForm_eq_exact :
    contractionOneForm B θ H.toPair.vector =
      CausalOneForm.exact H.potential := by
  rw [H.toPair.contractionOneForm_eq_covectorOneForm θ]
  exact H.covectorOneForm_eq_exact

/-- Event-level Hamilton equation:
B(X,theta(e)) equals the causal difference of H along e. -/
theorem eventHamiltonEquation
    (C : Configuration S)
    (d : EventDirection S C) :
    B.form C
        (H.toPair.vector C)
        (θ.vector C d) =
      causalDifference H.potential C
        d.event d.enabled := by
  exact
    (LinearMap.congr_fun
      (H.toPair.hamiltonian C)
      (θ.vector C d)).trans
        (H.differential_on_directions C d)

/-- The Hamiltonian contraction one-form is closed because it is exact. -/
theorem contractionOneForm_closed :
    (contractionOneForm B θ
      H.toPair.vector).Closed := by
  rw [H.contractionOneForm_eq_exact]
  exact CausalOneForm.exact_closed H.potential

/-- Consequently its exterior two-form vanishes on every concurrency
diamond. -/
theorem exteriorContraction_zero
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    CausalOneForm.exteriorDerivative
        (contractionOneForm B θ
          H.toPair.vector) d =
      0 :=
  H.contractionOneForm_closed d

end PotentialPair

/-- Event-generated Hamiltonian vector at one configuration: the Hamiltonian
vector is represented by one primitive causal direction under the soldering. -/
def Pair.EventGeneratedAt
    {B : CausalBilinear.Field
      (K := K) (S := S) (Fiber := Fiber)}
    (H : Pair B)
    (θ : CausalSoldering S Fiber)
    (C : Configuration S) : Prop :=
  ∃ d : EventDirection S C,
    H.vector C = θ.vector C d

/-- If the Hamiltonian vector is exactly the first direction of a concurrency
diamond, the event two-form evaluated on that diamond equals the Hamiltonian
covector on the second direction. -/
theorem Pair.eventTwoForm_eq_covector
    {B : CausalBilinear.Field
      (K := K) (S := S) (Fiber := Fiber)}
    (H : Pair B)
    (θ : CausalSoldering S Fiber)
    (halt : B.Alternating)
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f)
    (hgen :
      H.vector C =
        θ.vector C
          (CausalOneForm.baseE d)) :
    (θ.inducedTwoForm B halt).value d =
      H.covector C
        (θ.vector C
          (CausalOneForm.baseF d)) := by
  change
    B.form C
        (θ.vector C
          (CausalOneForm.baseE d))
        (θ.vector C
          (CausalOneForm.baseF d)) =
      H.covector C
        (θ.vector C
          (CausalOneForm.baseF d))
  rw [← hgen]
  exact LinearMap.congr_fun
    (H.hamiltonian C)
    (θ.vector C
      (CausalOneForm.baseF d))

/-- For a Hamiltonian potential pair generated by the first event direction,
the causal symplectic two-form directly measures the scalar Hamiltonian
difference along the second event direction. -/
theorem PotentialPair.eventTwoForm_eq_potentialDifference
    {B : CausalBilinear.Field
      (K := K) (S := S) (Fiber := Fiber)}
    {θ : CausalSoldering S Fiber}
    (H : PotentialPair B θ)
    (halt : B.Alternating)
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f)
    (hgen :
      H.toPair.vector C =
        θ.vector C
          (CausalOneForm.baseE d)) :
    (θ.inducedTwoForm B halt).value d =
      causalDifference H.potential C f
        d.concurrent.2.1 := by
  rw [H.toPair.eventTwoForm_eq_covector
    θ halt d hgen]
  exact
    H.differential_on_directions C
      (CausalOneForm.baseF d)

end CausalHamiltonian
end CausalGeometry
