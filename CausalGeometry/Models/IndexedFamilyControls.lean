import CausalGeometry.Realization.IndexedFamily
import Mathlib.Tactic

namespace CausalGeometry
namespace Models
namespace IndexedFamilyControls

/-- Two independent source coordinates. -/
abbrev Source :=
  Bool × Bool

/-- Two local places, selecting the two independent coordinates. -/
abbrev Place :=
  Bool

/-- The complete two-place family observes one source coordinate at each
place. -/
def coordinateFamily :
    IndexedRealizationFamily Source Place where
  Target := fun _ => Bool
  realize :=
    fun place source =>
      if place then source.2 else source.1

/-- Agreement at both places reconstructs the source pair. -/
theorem coordinateFamily_jointlyConservative :
    coordinateFamily.JointlyConservative := by
  intro x y h
  apply Prod.ext
  · have hfalse := h false
    simpa [
      IndexedRealizationFamily.CollapsesAt,
      coordinateFamily
    ] using hfalse
  · have htrue := h true
    simpa [
      IndexedRealizationFamily.CollapsesAt,
      coordinateFamily
    ] using htrue

/-- Explicit reconstruction of the source pair from the complete local
packet. -/
def coordinateReconstruction :
    IndexedRealizationFamily.Reconstruction
      coordinateFamily where
  recover :=
    fun packet =>
      (packet false, packet true)
  leftInverse := by
    intro source
    apply Prod.ext <;> rfl

/-- The explicit reconstruction data imply the already proved joint
conservativity without any appeal to choice. -/
theorem coordinateReconstruction_jointlyConservative :
    coordinateFamily.JointlyConservative :=
  coordinateReconstruction.jointlyConservative

/-- Mutation: both places observe only the first source coordinate. -/
def firstOnlyFamily :
    IndexedRealizationFamily Source Place where
  Target := fun _ => Bool
  realize :=
    fun _ source =>
      source.1

/-- The mutation is not jointly conservative: changing the hidden second
coordinate is invisible at every place. -/
theorem firstOnlyFamily_not_jointlyConservative :
    ¬ firstOnlyFamily.JointlyConservative := by
  intro hconservative
  have heq :
      (false, false) =
        (false, true) := by
    apply hconservative
    intro place
    cases place <;>
      rfl
  have hsecond :
      (false : Bool) = true :=
    congrArg Prod.snd heq
  cases hsecond

/-- Because the mutation is not jointly conservative, it cannot admit
explicit reconstruction data. -/
theorem firstOnlyFamily_noReconstruction :
    IsEmpty
      (IndexedRealizationFamily.Reconstruction
        firstOnlyFamily) := by
  constructor
  intro D
  exact
    firstOnlyFamily_not_jointlyConservative
      D.jointlyConservative

/-- Positive/control pair for the common-source local-family layer. -/
theorem joint_conservativity_discriminator :
    coordinateFamily.JointlyConservative ∧
      ¬ firstOnlyFamily.JointlyConservative :=
  ⟨coordinateFamily_jointlyConservative,
    firstOnlyFamily_not_jointlyConservative⟩

end IndexedFamilyControls
end Models
end CausalGeometry
