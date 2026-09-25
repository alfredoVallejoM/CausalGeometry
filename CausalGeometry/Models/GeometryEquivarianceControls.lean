import CausalGeometry.Calculus.SymplecticConnectionEquivariance
import CausalGeometry.Models.EventSystemEquivControls
import CausalGeometry.Models.HamiltonianEventControls
import CausalGeometry.Models.SymplecticGeometryControls
import Mathlib.Tactic

namespace CausalGeometry.Models

open EventSystem

/-- Pull the standard symplectic causal connection through the nontrivial
primitive-event swap. -/
def swappedSymplecticConnection :
    CausalSymplecticConnection
      ℤ twoEventSystem
      (fun _ => ℤ × ℤ) :=
  twoEventSwapEquiv.pullSymplecticConnection
    standardCausalSymplecticConnection

/-- The swap reverses the orientation of the basic false/true diamond, so the
causal symplectic two-form changes sign. -/
theorem swapped_eventTwoForm_basic :
    swappedSymplecticConnection
        .toGeometry.eventTwoForm.value
        twoEventDiamond =
      -1 := by
  rw [
    show
      swappedSymplecticConnection
          .toGeometry.eventTwoForm =
        twoEventSwapEquiv.pullTwoForm
          standardCausalSymplecticConnection
            .toGeometry.eventTwoForm
      from
        twoEventSwapEquiv
          .pullSymplecticConnection_eventTwoForm
            standardCausalSymplecticConnection
  ]
  change
    standardCausalSymplecticConnection
        .toGeometry.eventTwoForm.value
        (twoEventSwapEquiv.mapDiamond
          twoEventDiamond)
      =
    -1
  rw [twoEventSwap_diamond]
  rw [
    standardCausalSymplecticConnection
      .toGeometry.eventTwoForm.skew
        twoEventDiamond
  ]
  rw [standard_eventTwoForm_basic]
  norm_num

/-- The same swap sends the true-event scalar potential to the false-event
scalar potential. -/
theorem pulled_trueEventPotential_eq_falseEventPotential :
    twoEventSwapEquiv.pullObservable
        trueEventPotential
      =
    falseEventPotential := by
  funext C
  unfold
    EventSystemEquiv.pullObservable
    trueEventPotential
    falseEventPotential
  change
    (if true ∈
        twoEventSwapEquiv.mapConfiguration C
      then 1 else 0)
      =
    if false ∈ C then 1 else 0
  have hmem :
      (true ∈
        twoEventSwapEquiv.mapConfiguration C)
        ↔
      false ∈ C := by
    rfl
  simp [hmem]

/-- Pulled Hamiltonian potential pair. -/
def swappedTrueHamiltonianPotential :
    CausalHamiltonian.PotentialPair
      (twoEventSwapEquiv.pullBilinearField
        standardSymplecticField)
      (twoEventSwapEquiv.pullSoldering
        standardSoldering) :=
  twoEventSwapEquiv.pullHamiltonianPotentialPair
    trueEventHamiltonianPotential

@[simp] theorem swappedHamiltonian_potential :
    swappedTrueHamiltonianPotential.potential =
      falseEventPotential := by
  exact
    pulled_trueEventPotential_eq_falseEventPotential

/-- The fiber vector remains e1, but after reindexing it is represented by the
source event true, because true is sent to target false. -/
theorem swappedHamiltonian_generated_by_true :
    swappedTrueHamiltonianPotential.toPair.vector
        twoEventSystem.empty =
      (twoEventSwapEquiv.pullSoldering
        standardSoldering).vector
        twoEventSystem.empty
        (CausalOneForm.baseE
          twoEventDiamond.symm) := by
  rfl

/-- On the oppositely oriented diamond, the pulled event Hamilton equation is
again the nonzero identity 1=1. -/
theorem swappedHamilton_equation_symm :
    ((twoEventSwapEquiv.pullSoldering
        standardSoldering).inducedTwoForm
      (twoEventSwapEquiv.pullBilinearField
        standardSymplecticField)
      (twoEventSwapEquiv.pullBilinearField_alternating
        standardSymplecticField_alternating)).value
        twoEventDiamond.symm
      =
    causalDifference
      swappedTrueHamiltonianPotential.potential
      twoEventSystem.empty false
      twoEventDiamond.symm.concurrent.2.1 := by
  exact
    swappedTrueHamiltonianPotential
      .eventTwoForm_eq_potentialDifference
        (twoEventSwapEquiv.pullBilinearField_alternating
          standardSymplecticField_alternating)
        twoEventDiamond.symm
        swappedHamiltonian_generated_by_true

/-- Both sides of the swapped Hamilton equation evaluate to one. -/
theorem swappedHamilton_equation_symm_value :
    ((twoEventSwapEquiv.pullSoldering
        standardSoldering).inducedTwoForm
      (twoEventSwapEquiv.pullBilinearField
        standardSymplecticField)
      (twoEventSwapEquiv.pullBilinearField_alternating
        standardSymplecticField_alternating)).value
        twoEventDiamond.symm = 1
      ∧
    causalDifference
      falseEventPotential
      twoEventSystem.empty false
      twoEventDiamond.symm.concurrent.2.1 = 1 := by
  constructor
  · have hskew :=
      swappedSymplecticConnection
        .toGeometry.eventTwoForm.skew
          twoEventDiamond
    have hminus :=
      swapped_eventTwoForm_basic
    change
      swappedSymplecticConnection
          .toGeometry.eventTwoForm.value
          twoEventDiamond.symm =
        1
    rw [hskew, hminus]
    norm_num
  · norm_num [
      causalDifference,
      falseEventPotential,
      EventSystem.empty,
      EventSystem.extend,
      twoEventDiamond
    ]

/-- Presentation change is therefore genuinely nontrivial on oriented causal
forms while preserving the Hamiltonian equation. -/
theorem symplectic_equivariance_discriminator :
    standardCausalSymplecticConnection
          .toGeometry.eventTwoForm.value
          twoEventDiamond =
        1
      ∧
    swappedSymplecticConnection
          .toGeometry.eventTwoForm.value
          twoEventDiamond =
        -1
      ∧
    swappedTrueHamiltonianPotential.potential =
        falseEventPotential :=
  ⟨standard_eventTwoForm_basic,
    swapped_eventTwoForm_basic,
    swappedHamiltonian_potential⟩

end CausalGeometry.Models
