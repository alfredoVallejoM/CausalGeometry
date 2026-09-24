import CausalGeometry.Foundation.AdjunctionBridge
import Mathlib.Tactic

namespace CausalGeometry.Models

/-- Positive control: the identity structural pair is adjoint on Nat. -/
def natIdentityAdjoint :
    AdjointBridge (PairedTransform.identity Nat) where
  adjunction := by
    intro a b
    rfl

/-- Mutation/control pair: Phi increments while Psi forgets that increment.
It is a valid PairedTransform but neither an inverse pair nor an adjunction. -/
def successorForgetPair : PairedTransform Nat Nat where
  forward := fun n => n + 1
  backward := id

theorem successorForget_sourceRoundTrip_zero :
    successorForgetPair.sourceRoundTrip 0 = 1 := by
  rfl

theorem successorForget_zero_not_fixed :
    ¬ successorForgetPair.SourceFixed 0 := by
  norm_num [PairedTransform.SourceFixed,
    PairedTransform.sourceRoundTrip, successorForgetPair]

/-- Same-type adversarial discriminator: structural pairing does not imply
adjunction. -/
theorem successorForget_not_adjoint :
    ¬ AdjointBridge successorForgetPair := by
  intro A
  have h := A.adjunction 0 0
  norm_num [successorForgetPair] at h

end CausalGeometry.Models
