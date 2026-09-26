import CausalGeometry.Calculus.FiniteRealHodge
import CausalGeometry.Calculus.GradedHodgeZero
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

namespace CausalGeometry

noncomputable section

universe v

namespace finiteRealHodgeData

variable
    {C : ℕ → Type v}
    [∀ n, NormedAddCommGroup (C n)]
    [∀ n, InnerProductSpace ℝ (C n)]
    [∀ n, FiniteDimensional ℝ (C n)]
    (G : GradedCausalCochainComplex ℝ C)

/-- Degree-zero Laplacian is d0^* d0. -/
theorem laplacian0_eq_adjoint_comp_self :
    (H G).laplacian0 =
      (G.d 0).adjoint.comp (G.d 0) :=
  rfl

/-- In the finite-dimensional real sector, harmonic degree zero is exactly
closed degree zero. -/
theorem harmonic0_eq_closed0 :
    (H G).Harmonic0 =
      G.Closed 0 := by
  change
    ((G.d 0).adjoint.comp
      (G.d 0)).ker =
    (G.d 0).ker
  exact
    LinearMap.ker_adjoint_comp_self
      (G.d 0)

/-- The degree-zero Hodge representation hypotheses are therefore derived
rather than assumed. -/
def representation0 :
    GradedCausalHodgeRepresentation0
      (H G) where

  harmonic_closed := by
    rw [harmonic0_eq_closed0 G]

  closed_harmonic := by
    rw [harmonic0_eq_closed0 G]

/-- Canonical finite-real degree-zero Hodge theorem. -/
def harmonicEquivH0 :
    (H G).Harmonic0 ≃ₗ[ℝ]
      G.H0 :=
  (representation0 G).harmonicEquivH0

end finiteRealHodgeData
end

end CausalGeometry
