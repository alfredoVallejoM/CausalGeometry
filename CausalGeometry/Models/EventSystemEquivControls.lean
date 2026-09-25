import CausalGeometry.Calculus.CohomologyEquivH1
import CausalGeometry.Calculus.CohomologyEquivH2
import CausalGeometry.Models.CalculusControls
import Mathlib.Tactic

namespace CausalGeometry.Models

open EventSystem

/-- Nontrivial permutation of the two primitive events. -/
def boolSwapEquiv : Bool ≃ Bool where
  toFun := not
  invFun := not
  left_inv := by
    intro b
    cases b <;> rfl
  right_inv := by
    intro b
    cases b <;> rfl

@[simp] theorem boolSwapEquiv_false :
    boolSwapEquiv false = true :=
  rfl

@[simp] theorem boolSwapEquiv_true :
    boolSwapEquiv true = false :=
  rfl

/-- The completely independent two-event causal system admits the nontrivial
event swap as a primitive causal-system automorphism. -/
def twoEventSwapEquiv :
    EventSystemEquiv
      twoEventSystem
      twoEventSystem where
  eventEquiv :=
    boolSwapEquiv
  labelEquiv :=
    Equiv.refl Unit

  precedes_iff := by
    intro e f
    simp [twoEventSystem]

  conflict_iff := by
    intro e f
    simp [twoEventSystem]

  label_compat := by
    intro e
    rfl

/-- The empty configuration is fixed by the event swap. -/
@[simp] theorem twoEventSwap_empty :
    twoEventSwapEquiv.mapConfiguration
        twoEventSystem.empty =
      twoEventSystem.empty := by
  apply twoEventSystem.configuration_eq_of_carrier_eq
  ext e
  simp [
    EventSystemEquiv.mapConfiguration,
    EventSystem.empty
  ]

/-- The basic false/true diamond is sent to the oppositely oriented
true/false diamond. -/
theorem twoEventSwap_diamond :
    let d :=
      twoEventSwapEquiv.mapDiamond
        twoEventDiamond
    d =
      (twoEventDiamond.symm :
        ConcurrencyDiamond
          twoEventSystem.empty true false) := by
  dsimp
  have hC := twoEventSwap_empty
  cases hC
  exact
    EventSystemEquiv.concurrencyDiamond_eq
      _ _

/-- A one-form that records event orientation. -/
def orientationOneForm :
    CausalOneForm twoEventSystem ℤ where
  value := fun _ d =>
    if d.event then 1 else -1

@[simp] theorem orientationOneForm_false
    (C : Configuration twoEventSystem)
    (h : twoEventSystem.Enabled C false) :
    orientationOneForm.value C
        ⟨false, h⟩ =
      -1 := by
  rfl

@[simp] theorem orientationOneForm_true
    (C : Configuration twoEventSystem)
    (h : twoEventSystem.Enabled C true) :
    orientationOneForm.value C
        ⟨true, h⟩ =
      1 := by
  rfl

/-- Pullback along the swap is not the identity on one-forms. -/
theorem swap_pull_orientation_false :
    (twoEventSwapEquiv.pullOneForm
      orientationOneForm).value
        twoEventSystem.empty
        ⟨false,
          twoEvent_enabled_empty false⟩ =
      1 := by
  rfl

theorem orientation_pullback_nontrivial :
    twoEventSwapEquiv.pullOneForm
        orientationOneForm ≠
      orientationOneForm := by
  intro h
  have hv :=
    congrArg
      (fun ω : CausalOneForm twoEventSystem ℤ =>
        ω.value
          twoEventSystem.empty
          ⟨false,
            twoEvent_enabled_empty false⟩)
      h
  norm_num [
    swap_pull_orientation_false
  ] at hv

/-- Nevertheless the pullback is involutive, because the causal-system
automorphism is involutive. -/
theorem orientation_pullback_roundtrip :
    twoEventSwapEquiv.pullOneForm
        (twoEventSwapEquiv.pullOneForm
          orientationOneForm) =
      orientationOneForm := by
  simpa using
    twoEventSwapEquiv
      .pullOneForm_symm_pullOneForm
        orientationOneForm

/-- H1 transport along the nontrivial automorphism is exactly invertible. -/
theorem twoEventSwap_H1_roundtrip
    (x :
      CausalCohomology.H1
        (S := twoEventSystem)
        (K := ℤ)) :
    (twoEventSwapEquiv.h1AddEquiv).symm
        (twoEventSwapEquiv.h1AddEquiv x)
      =
    x := by
  exact
    (twoEventSwapEquiv.h1AddEquiv)
      .symm_apply_apply x

/-- Same invariant statement for H2. -/
theorem twoEventSwap_H2_roundtrip
    (x :
      CausalCohomology.H2
        (S := twoEventSystem)
        (K := ℤ)) :
    (twoEventSwapEquiv.h2AddEquiv).symm
        (twoEventSwapEquiv.h2AddEquiv x)
      =
    x := by
  exact
    (twoEventSwapEquiv.h2AddEquiv)
      .symm_apply_apply x

/-- Scalar square variation is unchanged after renaming the primitive events,
provided the observable is transported contravariantly. -/
theorem twoEventSwap_squareVariation
    (F :
      Configuration twoEventSystem → ℤ) :
    causalSquareVariation F
        (twoEventSwapEquiv.mapDiamond
          twoEventDiamond)
      =
    causalSquareVariation
      (twoEventSwapEquiv.pullObservable F)
      twoEventDiamond := by
  exact
    twoEventSwapEquiv
      .causalSquareVariation_natural
        F twoEventDiamond

end CausalGeometry.Models
