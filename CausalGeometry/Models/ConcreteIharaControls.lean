import CausalGeometry.Cyclic.ConcreteIhara
import CausalGeometry.Models.HashimotoControls
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic

namespace CausalGeometry.Models

open Finset

/-- The two-orientation Hashimoto matrix is exactly the identity matrix. -/
theorem twoOrientationLoop_hashimoto_matrix :
    (twoOrientationLoop.hashimotoTransfer ℤ).matrix =
      (1 : Matrix Bool Bool ℤ) := by
  ext e f
  cases e <;> cases f <;>
    simp [
      FiniteTransferSystem.matrix,
      FiniteDirectedEdgeSystem.hashimotoTransfer,
      FiniteDirectedEdgeSystem.hashimotoWeight,
      FiniteDirectedEdgeSystem.Nonbacktracking,
      twoOrientationLoop,
      Matrix.one_apply
    ]

/-- Therefore every positive or zero power has trace two. -/
theorem twoOrientationLoop_tracePower
    (n : ℕ) :
    (twoOrientationLoop.hashimotoTransfer ℤ).tracePower n =
      2 := by
  unfold FiniteTransferSystem.tracePower
  rw [twoOrientationLoop_hashimoto_matrix]
  simp [Matrix.trace, Fintype.sum_bool,
    Matrix.one_apply]

/-- Primitive content: exactly two primitive oriented cycles, both of period
one. -/
def twoOrientationLoop_primitiveCounts :
    PrimitiveTraceCounts where
  primitive := fun n =>
    if n = 1 then 2 else 0
  closed := fun _ => 2
  decomposition := by
    intro n hn
    classical
    calc
      (∑ d ∈ n.divisors,
          (d : ℤ) *
            (if d = 1 then 2 else 0))
          =
        (1 : ℤ) * 2 := by
          rw [Finset.sum_eq_single 1]
          · simp
          · intro b hb hb1
            simp [hb1]
          · intro hnot
            exact
              (hnot
                (Nat.one_mem_divisors.2
                  hn.ne')).elim
      _ = 2 := by norm_num

/-- Concrete primitive/Hashimoto comparison for the control graph. -/
def twoOrientationLoop_primitiveComparison :
    HashimotoPrimitiveComparison
      twoOrientationLoop where
  counts :=
    twoOrientationLoop_primitiveCounts
  trace_matches := by
    intro n
    exact twoOrientationLoop_tracePower n

/-- Determinant polynomial is (1-X)^2. -/
theorem twoOrientationLoop_determinantPolynomial :
    twoOrientationLoop.hashimotoDeterminantPolynomial =
      (1 - Polynomial.X) ^ 2 := by
  unfold
    FiniteDirectedEdgeSystem.hashimotoDeterminantPolynomial
    FiniteTransferSystem.determinantPolynomial
  rw [twoOrientationLoop_hashimoto_matrix]
  simp only [
    Matrix.map_one,
    map_zero,
    map_one
  ]
  have hmatrix :
      (1 -
          (Polynomial.X : ℤ[X]) •
            (1 : Matrix Bool Bool ℤ[X]))
        =
      Matrix.diagonal
        (fun _ : Bool =>
          (1 - Polynomial.X : ℤ[X])) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [Matrix.one_apply]
    · simp [Matrix.one_apply, h]
  rw [hmatrix, Matrix.det_diagonal,
    Fintype.prod_bool]
  ring

/-- Same determinant after embedding into Q[[X]]. -/
theorem twoOrientationLoop_determinantPowerSeries :
    twoOrientationLoop.hashimotoDeterminantPowerSeries =
      (1 - PowerSeries.X) ^ 2 := by
  unfold
    FiniteDirectedEdgeSystem.hashimotoDeterminantPowerSeries
  rw [twoOrientationLoop_determinantPolynomial]
  simp

/-- Standard geometric formal power series 1+X+X^2+... . -/
def loopGeometric : PowerSeries ℚ :=
  PowerSeries.mk fun _ => 1

@[simp] theorem loopGeometric_coeff
    (n : ℕ) :
    PowerSeries.coeff n loopGeometric = 1 := by
  simp [loopGeometric]

/-- Geometric series is the inverse of 1-X. -/
theorem loopGeometric_mul_one_sub_X :
    loopGeometric *
        (1 - PowerSeries.X) =
      1 := by
  exact
    PowerSeries.mk_one_mul_one_sub_eq_one

/-- Its formal derivative is its square. -/
theorem derivative_loopGeometric :
    PowerSeries.derivative loopGeometric =
      loopGeometric ^ 2 := by
  rw [PowerSeries.ext_iff]
  intro n
  rw [PowerSeries.coeff_derivative]
  simp only [loopGeometric_coeff]
  rw [pow_two, PowerSeries.coeff_mul]
  rw [
    Nat.sum_antidiagonal_eq_sum_range_succ
      (fun _ _ : ℕ => (1 : ℚ) * 1)
      n
  ]
  simp

/-- Reciprocal determinant is the square of the geometric series. -/
theorem twoOrientationLoop_reciprocal_eq_geometric_sq :
    twoOrientationLoop.hashimotoDeterminantReciprocal =
      loopGeometric ^ 2 := by
  have hdet :=
    twoOrientationLoop_determinantPowerSeries
  have hgeom :=
    loopGeometric_mul_one_sub_X
  have hright :
      loopGeometric ^ 2 *
          twoOrientationLoop.hashimotoDeterminantPowerSeries =
        1 := by
    rw [hdet]
    rw [pow_two, pow_two]
    calc
      loopGeometric * loopGeometric *
            ((1 - PowerSeries.X) *
              (1 - PowerSeries.X))
          =
        (loopGeometric *
            (1 - PowerSeries.X)) *
          (loopGeometric *
            (1 - PowerSeries.X)) := by
              ring
      _ = 1 := by
        rw [hgeom]
        simp
  have hne :
      twoOrientationLoop.hashimotoDeterminantPowerSeries ≠
        0 := by
    intro hzero
    have hconst :=
      congrArg PowerSeries.constantCoeff hzero
    simpa using hconst
  apply mul_right_cancel₀ hne
  rw [
    twoOrientationLoop.reciprocal_mul_determinant,
    hright
  ]

/-- Hashimoto trace series is twice the geometric series. -/
theorem twoOrientationLoop_hashimotoTraceSeries :
    twoOrientationLoop_primitiveComparison.hashimotoTraceSeries =
      2 • loopGeometric := by
  rw [PowerSeries.ext_iff]
  intro n
  simp [
    HashimotoPrimitiveComparison.hashimotoTraceSeries,
    twoOrientationLoop_tracePower,
    loopGeometric
  ]

/-- The determinant reciprocal satisfies the required trace differential
equation. -/
def twoOrientationLoop_determinantTrace :
    HashimotoDeterminantTraceBridge
      twoOrientationLoop where
  differential := by
    rw [
      twoOrientationLoop_reciprocal_eq_geometric_sq
    ]
    have htrace :
        (PowerSeries.mk fun n =>
          ((twoOrientationLoop.hashimotoTransfer ℤ).tracePower
            (n + 1) : ℚ))
          =
        2 • loopGeometric := by
      rw [PowerSeries.ext_iff]
      intro n
      simp [
        twoOrientationLoop_tracePower,
        loopGeometric
      ]
    rw [htrace]
    rw [
      PowerSeries.derivative_pow,
      derivative_loopGeometric
    ]
    norm_num
    ring

/-- Fully concrete Ihara package for the smallest non-backtracking control. -/
def twoOrientationLoop_concreteIhara :
    ConcreteFiniteIhara
      twoOrientationLoop where
  primitive :=
    twoOrientationLoop_primitiveComparison
  determinantTrace :=
    twoOrientationLoop_determinantTrace

/-- End-to-end Ihara identity for the control graph. -/
theorem twoOrientationLoop_ihara :
    twoOrientationLoop.hashimotoDeterminantReciprocal =
      twoOrientationLoop_primitiveComparison.hashimotoEulerZetaSeries :=
  twoOrientationLoop_concreteIhara.ihara

end CausalGeometry.Models
