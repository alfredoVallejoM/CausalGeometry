import CausalGeometry.Number.DivisibilityClasses
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

namespace CausalGeometry

universe u

namespace CausalDivisibilityClasses

variable (α : Type u) [Monoid α]

/-- Canonical Mobius function on left-divisibility classes, whenever the
antisymmetrized causal divisor order is locally finite. -/
def leftMobius
    [LocallyFiniteOrder (Left α)] [DecidableEq (Left α)] :
    IncidenceAlgebra ℤ (Left α) :=
  IncidenceAlgebra.mu ℤ

/-- Canonical incidence zeta on left-divisibility classes. -/
def leftZeta
    [DecidableLE (Left α)] :
    IncidenceAlgebra ℤ (Left α) :=
  IncidenceAlgebra.zeta ℤ

/-- Canonical Mobius function on right-divisibility classes. -/
def rightMobius
    [LocallyFiniteOrder (Right α)] [DecidableEq (Right α)] :
    IncidenceAlgebra ℤ (Right α) :=
  IncidenceAlgebra.mu ℤ

/-- Canonical incidence zeta on right-divisibility classes. -/
def rightZeta
    [DecidableLE (Right α)] :
    IncidenceAlgebra ℤ (Right α) :=
  IncidenceAlgebra.zeta ℤ

@[simp] theorem leftMobius_self
    [LocallyFiniteOrder (Left α)] [DecidableEq (Left α)]
    (x : Left α) :
    leftMobius α x x = 1 := by
  simp [leftMobius]

@[simp] theorem rightMobius_self
    [LocallyFiniteOrder (Right α)] [DecidableEq (Right α)]
    (x : Right α) :
    rightMobius α x x = 1 := by
  simp [rightMobius]

theorem leftMobius_eq_zero_of_not_divides
    [LocallyFiniteOrder (Left α)] [DecidableEq (Left α)]
    {x y : α} (h : ¬ CausalDivisibility.LeftDivides x y) :
    leftMobius α (leftClass α x) (leftClass α y) = 0 := by
  apply IncidenceAlgebra.apply_eq_zero_of_not_le
  intro hle
  exact h ((leftClass_le_iff α x y).mp hle)

theorem rightMobius_eq_zero_of_not_divides
    [LocallyFiniteOrder (Right α)] [DecidableEq (Right α)]
    {x y : α} (h : ¬ CausalDivisibility.RightDivides x y) :
    rightMobius α (rightClass α x) (rightClass α y) = 0 := by
  apply IncidenceAlgebra.apply_eq_zero_of_not_le
  intro hle
  exact h ((rightClass_le_iff α x y).mp hle)

theorem leftMobius_mul_zeta
    [LocallyFiniteOrder (Left α)]
    [DecidableEq (Left α)] [DecidableLE (Left α)] :
    leftMobius α * leftZeta α = 1 := by
  simpa [leftMobius, leftZeta] using
    (IncidenceAlgebra.mu_mul_zeta ℤ (Left α))

theorem leftZeta_mul_mobius
    [LocallyFiniteOrder (Left α)]
    [DecidableEq (Left α)] [DecidableLE (Left α)] :
    leftZeta α * leftMobius α = 1 := by
  simpa [leftMobius, leftZeta] using
    (IncidenceAlgebra.zeta_mul_mu
      (𝕜 := ℤ) (α := Left α))

theorem rightMobius_mul_zeta
    [LocallyFiniteOrder (Right α)]
    [DecidableEq (Right α)] [DecidableLE (Right α)] :
    rightMobius α * rightZeta α = 1 := by
  simpa [rightMobius, rightZeta] using
    (IncidenceAlgebra.mu_mul_zeta ℤ (Right α))

theorem rightZeta_mul_mobius
    [LocallyFiniteOrder (Right α)]
    [DecidableEq (Right α)] [DecidableLE (Right α)] :
    rightZeta α * rightMobius α = 1 := by
  simpa [rightMobius, rightZeta] using
    (IncidenceAlgebra.zeta_mul_mu
      (𝕜 := ℤ) (α := Right α))

end CausalDivisibilityClasses
end CausalGeometry
