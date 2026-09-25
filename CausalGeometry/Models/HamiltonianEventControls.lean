import CausalGeometry.Calculus.HamiltonianEventEquation
import CausalGeometry.Models.SymplecticGeometryControls
import Mathlib.Tactic

namespace CausalGeometry.Models

open EventSystem

/-- Covector extracting the second coordinate. -/
def secondCoordinateCovector :
    CausalHamiltonian.CovectorSection
      (K := ℤ)
      (S := twoEventSystem)
      (Fiber := fun _ => ℤ × ℤ) :=
  fun _ =>
    { toFun := fun x => x.2
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro a x
        simp }

/-- The standard symplectic musical bridge turns dy into e1. -/
def trueEventHamiltonianPair :
    CausalHamiltonian.Pair
      standardSymplecticField :=
  CausalHamiltonian.Pair.ofMusical
    standardSymplecticMusicalBridge
    secondCoordinateCovector

@[simp] theorem trueEventHamiltonian_vector
    (C : Configuration twoEventSystem) :
    trueEventHamiltonianPair.vector C =
      (1, 0) := by
  rfl

/-- Scalar potential detecting whether the true event has occurred. -/
def trueEventPotential
    (C : Configuration twoEventSystem) : ℤ :=
  if true ∈ C then 1 else 0

/-- The covector dy is exactly the causal finite difference of the true-event
indicator when evaluated on soldered primitive directions. -/
theorem trueEventPotential_differential
    (C : Configuration twoEventSystem)
    (d : EventDirection twoEventSystem C) :
    trueEventHamiltonianPair.covector C
        (standardSoldering.vector C d) =
      causalDifference trueEventPotential C
        d.event d.enabled := by
  cases hd : d.event with
  | false =>
      have hmem :
          (true ∈
              twoEventSystem.extend C
                d.event d.enabled) ↔
            true ∈ C := by
        simp [hd, EventSystem.extend]
      simp [
        trueEventHamiltonianPair,
        secondCoordinateCovector,
        standardSoldering,
        causalDifference,
        trueEventPotential,
        hd,
        hmem
      ]
  | true =>
      have hnot : true ∉ C := by
        simpa [hd] using d.enabled.1
      simp [
        trueEventHamiltonianPair,
        secondCoordinateCovector,
        standardSoldering,
        causalDifference,
        trueEventPotential,
        hd,
        hnot,
        EventSystem.extend
      ]

/-- Fully concrete Hamiltonian potential pair. -/
def trueEventHamiltonianPotential :
    CausalHamiltonian.PotentialPair
      standardSymplecticField
      standardSoldering where
  toPair :=
    trueEventHamiltonianPair
  potential :=
    trueEventPotential
  differential_on_directions :=
    trueEventPotential_differential

/-- The Hamiltonian vector at the empty configuration is the soldered false
direction. -/
theorem trueEventHamiltonian_generated_by_false :
    trueEventHamiltonianPotential.toPair.vector
        twoEventSystem.empty =
      standardSoldering.vector
        twoEventSystem.empty
        (CausalOneForm.baseE twoEventDiamond) := by
  rfl

/-- Event-level Hamilton equation on the basic concurrency diamond. -/
theorem trueEventHamilton_equation_basic :
    (standardSoldering.inducedTwoForm
      standardSymplecticField
      standardSymplecticField_alternating).value
        twoEventDiamond =
      causalDifference
        trueEventHamiltonianPotential.potential
        twoEventSystem.empty true
        twoEventDiamond.concurrent.2.1 := by
  exact
    trueEventHamiltonianPotential.eventTwoForm_eq_potentialDifference
      standardSymplecticField_alternating
      twoEventDiamond
      trueEventHamiltonian_generated_by_false

/-- Both sides of the basic Hamilton equation are the nonzero value one. -/
theorem trueEventHamilton_equation_basic_value :
    (standardSoldering.inducedTwoForm
      standardSymplecticField
      standardSymplecticField_alternating).value
        twoEventDiamond = 1 ∧
      causalDifference
        trueEventPotential
        twoEventSystem.empty true
        twoEventDiamond.concurrent.2.1 = 1 := by
  constructor
  · simpa [
      CausalSymplecticConnection.toGeometry,
      CausalSymplecticGeometry.eventTwoForm
    ] using standard_eventTwoForm_basic
  · norm_num [
      causalDifference,
      trueEventPotential,
      EventSystem.empty,
      EventSystem.extend,
      twoEventDiamond
    ]

/-- The Hamiltonian contraction one-form is exact and hence closed. -/
theorem trueEventHamilton_contraction_closed :
    (CausalHamiltonian.contractionOneForm
      standardSymplecticField
      standardSoldering
      trueEventHamiltonianPotential.toPair.vector).Closed :=
  trueEventHamiltonianPotential.contractionOneForm_closed

/-- Adversarial potential mutation: detect false instead of true. -/
def falseEventPotential
    (C : Configuration twoEventSystem) : ℤ :=
  if false ∈ C then 1 else 0

/-- The mutated potential cannot realize the same covector section. -/
theorem falseEventPotential_not_differential :
    ¬ ∀ (C : Configuration twoEventSystem)
        (d : EventDirection twoEventSystem C),
      trueEventHamiltonianPair.covector C
          (standardSoldering.vector C d) =
        causalDifference falseEventPotential C
          d.event d.enabled := by
  intro h
  let d :
      EventDirection
        twoEventSystem twoEventSystem.empty :=
    ⟨true, twoEvent_enabled_empty true⟩
  have hd := h twoEventSystem.empty d
  norm_num [
    d,
    trueEventHamiltonianPair,
    secondCoordinateCovector,
    standardSoldering,
    causalDifference,
    falseEventPotential,
    EventSystem.empty,
    EventSystem.extend
  ] at hd

end CausalGeometry.Models
