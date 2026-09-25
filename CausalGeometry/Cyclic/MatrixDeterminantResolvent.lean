import CausalGeometry.Cyclic.MatrixGeometricSeries
import CausalGeometry.Cyclic.MatrixJacobiGlobal
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

namespace CausalGeometry

universe u

namespace Matrix

variable
    {n : Type u}
    [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R]

/-- D_M(X)=det(I-XM), embedded into formal power series. -/
def determinantPowerSeries
    (M : Matrix n n R) :
    PowerSeries R :=
  (detOneSubX M : PowerSeries R)

@[simp] theorem determinantPowerSeries_constantCoeff
    (M : Matrix n n R) :
    PowerSeries.constantCoeff
        (determinantPowerSeries M) =
      1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  change
    (detOneSubX M).coeff 0 = 1
  rw [Polynomial.coeff_zero_eq_eval_zero]
  unfold detOneSubX
  rw [Matrix.eval_det]
  simp

/-- Formal reciprocal D_M(X)^(-1), available over any commutative ring because
D_M(0)=1. -/
def determinantReciprocal
    (M : Matrix n n R) :
    PowerSeries R :=
  PowerSeries.invOfUnit
    (determinantPowerSeries M) 1

@[simp] theorem determinant_mul_reciprocal
    (M : Matrix n n R) :
    determinantPowerSeries M *
        determinantReciprocal M =
      1 := by
  unfold determinantReciprocal
  exact
    PowerSeries.mul_invOfUnit
      (determinantPowerSeries M)
      1
      (by
        simpa using
          determinantPowerSeries_constantCoeff M)

@[simp] theorem reciprocal_mul_determinant
    (M : Matrix n n R) :
    determinantReciprocal M *
        determinantPowerSeries M =
      1 := by
  unfold determinantReciprocal
  exact
    PowerSeries.invOfUnit_mul
      (determinantPowerSeries M)
      1
      (by
        simpa using
          determinantPowerSeries_constantCoeff M)

/-- Adjugate of I-XM embedded entrywise into power series. -/
def adjugateResolventPowerSeries
    (M : Matrix n n R) :
    Matrix n n (PowerSeries R) :=
  (adjugate
    (1 -
      (Polynomial.X : R[X]) •
        M.map Polynomial.C)).map
      PowerSeries.coeToPowerSeries.ringHom

/-- Polynomial resolvent denominator embeds to the power-series denominator. -/
theorem resolventDenominator_eq_map
    (M : Matrix n n R) :
    resolventDenominator M =
      ((1 -
        (Polynomial.X : R[X]) •
          M.map Polynomial.C) :
        Matrix n n R[X]).map
          PowerSeries.coeToPowerSeries.ringHom := by
  ext i j
  simp [
    resolventDenominator,
    powerSeriesConstMatrix,
    Matrix.one_apply
  ]

/-- Adjugate identity after embedding into power series. -/
theorem resolvent_mul_adjugatePowerSeries
    (M : Matrix n n R) :
    resolventDenominator M *
        adjugateResolventPowerSeries M =
      determinantPowerSeries M •
        (1 : Matrix n n (PowerSeries R)) := by
  let A :
      Matrix n n R[X] :=
    1 -
      (Polynomial.X : R[X]) •
        M.map Polynomial.C
  have h :=
    congrArg
      (fun N : Matrix n n R[X] =>
        N.map
          PowerSeries.coeToPowerSeries.ringHom)
      (Matrix.mul_adjugate A)
  simpa [
    A,
    resolventDenominator_eq_map,
    adjugateResolventPowerSeries,
    determinantPowerSeries,
    detOneSubX,
    Matrix.map_mul
  ] using h

/-- The same identity with adjugate on the left. -/
theorem adjugatePowerSeries_mul_resolvent
    (M : Matrix n n R) :
    adjugateResolventPowerSeries M *
        resolventDenominator M =
      determinantPowerSeries M •
        (1 : Matrix n n (PowerSeries R)) := by
  let A :
      Matrix n n R[X] :=
    1 -
      (Polynomial.X : R[X]) •
        M.map Polynomial.C
  have h :=
    congrArg
      (fun N : Matrix n n R[X] =>
        N.map
          PowerSeries.coeToPowerSeries.ringHom)
      (Matrix.adjugate_mul A)
  simpa [
    A,
    resolventDenominator_eq_map,
    adjugateResolventPowerSeries,
    determinantPowerSeries,
    detOneSubX,
    Matrix.map_mul
  ] using h

/-- Adjugate formula for the formal inverse of I-XM. -/
def inverseFromAdjugate
    (M : Matrix n n R) :
    Matrix n n (PowerSeries R) :=
  determinantReciprocal M •
    adjugateResolventPowerSeries M

theorem resolvent_mul_inverseFromAdjugate
    (M : Matrix n n R) :
    resolventDenominator M *
        inverseFromAdjugate M =
      1 := by
  unfold inverseFromAdjugate
  rw [Matrix.mul_smul]
  rw [resolvent_mul_adjugatePowerSeries]
  rw [smul_smul]
  rw [reciprocal_mul_determinant]
  simp

theorem inverseFromAdjugate_mul_resolvent
    (M : Matrix n n R) :
    inverseFromAdjugate M *
        resolventDenominator M =
      1 := by
  unfold inverseFromAdjugate
  rw [Matrix.smul_mul]
  rw [adjugatePowerSeries_mul_resolvent]
  rw [smul_smul]
  rw [reciprocal_mul_determinant]
  simp

/-- The adjugate inverse is exactly the geometric matrix series. -/
theorem inverseFromAdjugate_eq_geometric
    (M : Matrix n n R) :
    inverseFromAdjugate M =
      geometricPowerSeries M := by
  calc
    inverseFromAdjugate M
        =
      1 * inverseFromAdjugate M := by
        simp
    _ =
      (geometricPowerSeries M *
        resolventDenominator M) *
          inverseFromAdjugate M := by
            rw [geometric_mul_resolvent]
    _ =
      geometricPowerSeries M *
        (resolventDenominator M *
          inverseFromAdjugate M) := by
            rw [Matrix.mul_assoc]
    _ = geometricPowerSeries M := by
      rw [resolvent_mul_inverseFromAdjugate]
      simp

/-- Trace of M adj(I-XM), multiplied by D^-1, is the shifted trace series. -/
theorem reciprocal_mul_trace_adjugate
    (M : Matrix n n R) :
    determinantReciprocal M *
        trace
          (powerSeriesConstMatrix M *
            adjugateResolventPowerSeries M)
      =
    tracePowerSeries M := by
  have hInv :=
    inverseFromAdjugate_eq_geometric M
  have htrace :=
    congrArg
      (fun N :
        Matrix n n (PowerSeries R) =>
          trace
            (powerSeriesConstMatrix M * N))
      hInv
  rw [trace_const_mul_geometric] at htrace
  unfold inverseFromAdjugate at htrace
  simpa [
    Matrix.mul_smul,
    Matrix.trace,
    Matrix.mul_apply,
    Finset.mul_sum
  ] using htrace

/-- Global Jacobi formula after embedding from polynomials to power series. -/
theorem derivative_determinantPowerSeries
    (M : Matrix n n R) :
    PowerSeries.derivative
        (determinantPowerSeries M)
      =
    -
      trace
        (powerSeriesConstMatrix M *
          adjugateResolventPowerSeries M) := by
  unfold determinantPowerSeries
  rw [PowerSeries.derivative_coe]
  rw [derivative_detOneSubX]
  simp [
    powerSeriesConstMatrix,
    adjugateResolventPowerSeries,
    Matrix.trace,
    Matrix.mul_apply,
    RingHom.map_adjugate
  ]

end Matrix

namespace Matrix

variable
    {n : Type u}
    [Fintype n] [DecidableEq n]
    {K : Type*} [Field K]

/-- Universal finite-matrix determinant/trace differential equation:
d(D^-1)/dX = D^-1 * sum tr(M^(n+1)) X^n.
-/
theorem derivative_determinantReciprocal
    (M : Matrix n n K) :
    PowerSeries.derivative
        (determinantReciprocal M)
      =
    determinantReciprocal M *
      tracePowerSeries M := by
  have hconst :
      PowerSeries.constantCoeff
          (determinantPowerSeries M) =
        (1 : K) :=
    determinantPowerSeries_constantCoeff M
  have hrec :
      determinantReciprocal M =
        (determinantPowerSeries M)⁻¹ := by
    unfold determinantReciprocal
    exact
      PowerSeries.invOfUnit_eq'
        (determinantPowerSeries M)
        1 hconst
  rw [hrec]
  rw [PowerSeries.derivative_inv']
  rw [derivative_determinantPowerSeries]
  rw [← hrec]
  calc
    -
        determinantReciprocal M ^ 2 *
          (-
            trace
              (powerSeriesConstMatrix M *
                adjugateResolventPowerSeries M))
        =
      determinantReciprocal M *
        (determinantReciprocal M *
          trace
            (powerSeriesConstMatrix M *
              adjugateResolventPowerSeries M)) := by
                ring
    _ =
      determinantReciprocal M *
        tracePowerSeries M := by
          rw [reciprocal_mul_trace_adjugate]

end Matrix
end CausalGeometry
