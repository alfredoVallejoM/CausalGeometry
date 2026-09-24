import CausalGeometry.Calculus.RestrictionTransport
import Mathlib.Tactic

namespace CausalGeometry.Models

/-- Structural pair used to separate forward and backward dynamical
compatibility. -/
def doubleForgetPair : PairedTransform ℤ ℤ where
  forward := fun z => 2 * z
  backward := id

/-- Source advances by one while target advances by two. -/
def asymmetricDynamics : PairedDynamics doubleForgetPair where
  sourceStep := fun z => z + 1
  targetStep := fun z => z + 2

/-- Phi intertwines the chosen dynamics exactly. -/
theorem asymmetricDynamics_forward_natural :
    asymmetricDynamics.ForwardNatural := by
  intro z
  simp [PairedDynamics.ForwardNatural,
    asymmetricDynamics, doubleForgetPair]
  ring

/-- Psi does not intertwine the same dynamics. -/
theorem asymmetricDynamics_not_backward_natural :
    ¬ asymmetricDynamics.BackwardNatural := by
  intro h
  have h0 := h 0
  norm_num [asymmetricDynamics, doubleForgetPair] at h0

/-- Same-type discriminator: forward compatibility does not force backward
compatibility. -/
theorem forward_natural_does_not_force_backward :
    asymmetricDynamics.ForwardNatural ∧
      ¬ asymmetricDynamics.BackwardNatural :=
  ⟨asymmetricDynamics_forward_natural,
    asymmetricDynamics_not_backward_natural⟩

end CausalGeometry.Models
