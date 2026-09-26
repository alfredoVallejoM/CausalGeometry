import CausalGeometry.Calculus.GradedCohomologyTransport
import Mathlib.Tactic

namespace CausalGeometry
namespace Models

/-- Constant rational cochain carrier used only as a finite algebraic control. -/
abbrev RationalDegree (_ : ℕ) := ℚ

/-- Completely flat graded control complex. -/
def zeroGradedComplex :
    GradedCausalCochainComplex ℚ RationalDegree where
  d := fun _ => 0
  d_sq := by
    intro n
    simp

/-- A one-step control complex with d_0=id and all higher differentials zero.

Its square is zero because d_1=0. -/
def firstSpikeGradedComplex :
    GradedCausalCochainComplex ℚ RationalDegree where
  d := fun n =>
    match n with
    | 0 => LinearMap.id
    | _ + 1 => 0
  d_sq := by
    intro n
    cases n <;> simp

/-- Forward-zero/backward-identity paired transport from the zero complex to
the first-spike complex. -/
def forwardNaturalBackwardDefective :
    PairedCochainTransport
      zeroGradedComplex firstSpikeGradedComplex where
  forward :=
    { map := fun _ => 0 }
  backward :=
    { map := fun _ => LinearMap.id }

theorem forwardNaturalBackwardDefective_forward :
    forwardNaturalBackwardDefective.forward.Natural := by
  intro n
  ext x
  simp [forwardNaturalBackwardDefective,
    zeroGradedComplex, firstSpikeGradedComplex]

theorem forwardNaturalBackwardDefective_backward_not :
    ¬ forwardNaturalBackwardDefective.backward.Natural := by
  intro h
  have h0 :=
    GradedLinearTransport.map_d h 0 (1 : ℚ)
  norm_num [forwardNaturalBackwardDefective,
    zeroGradedComplex, firstSpikeGradedComplex] at h0

/-- Forward-identity/backward-zero provides the opposite discriminator. -/
def forwardDefectiveBackwardNatural :
    PairedCochainTransport
      zeroGradedComplex firstSpikeGradedComplex where
  forward :=
    { map := fun _ => LinearMap.id }
  backward :=
    { map := fun _ => 0 }

theorem forwardDefectiveBackwardNatural_forward_not :
    ¬ forwardDefectiveBackwardNatural.forward.Natural := by
  intro h
  have h0 :=
    GradedLinearTransport.map_d h 0 (1 : ℚ)
  norm_num [forwardDefectiveBackwardNatural,
    zeroGradedComplex, firstSpikeGradedComplex] at h0

theorem forwardDefectiveBackwardNatural_backward :
    forwardDefectiveBackwardNatural.backward.Natural := by
  intro n
  ext x
  simp [forwardDefectiveBackwardNatural,
    zeroGradedComplex, firstSpikeGradedComplex]

end Models
end CausalGeometry
