import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

namespace CausalGeometry

universe u

namespace Matrix

variable
    {n : Type u}
    [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R]

/-- Formal matrix geometric series G_M(X)=sum_{k>=0} M^k X^k, represented
entrywise as a matrix of power series. -/
def geometricPowerSeries
    (M : Matrix n n R) :
    Matrix n n (PowerSeries R) :=
  fun i j =>
    PowerSeries.mk fun k =>
      (M ^ k) i j

@[simp] theorem coeff_geometricPowerSeries
    (M : Matrix n n R)
    (k : ℕ) (i j : n) :
    PowerSeries.coeff k
        (geometricPowerSeries M i j) =
      (M ^ k) i j :=
  rfl

/-- Constant embedding of M into matrices over power series. -/
def powerSeriesConstMatrix
    (M : Matrix n n R) :
    Matrix n n (PowerSeries R) :=
  M.map PowerSeries.C

/-- Formal resolvent denominator I-XM. -/
def resolventDenominator
    (M : Matrix n n R) :
    Matrix n n (PowerSeries R) :=
  1 -
    PowerSeries.X •
      powerSeriesConstMatrix M

/-- Left recurrence G=I+X M G. -/
theorem geometric_eq_one_add_X_mul
    (M : Matrix n n R) :
    geometricPowerSeries M =
      1 +
        PowerSeries.X •
          (powerSeriesConstMatrix M *
            geometricPowerSeries M) := by
  ext i j k
  cases k with
  | zero =>
      simp [
        geometricPowerSeries,
        powerSeriesConstMatrix,
        Matrix.one_apply,
        Matrix.mul_apply
      ]
  | succ k =>
      simp only [
        geometricPowerSeries,
        powerSeriesConstMatrix,
        PowerSeries.coeff_mk,
        Matrix.add_apply,
        Matrix.smul_apply,
        PowerSeries.coeff_smul,
        PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_C_mul,
        Matrix.one_apply
      ]
      rw [pow_succ']
      simp [Matrix.mul_apply]

/-- Right recurrence G=I+X G M. -/
theorem geometric_eq_one_add_X_mul_right
    (M : Matrix n n R) :
    geometricPowerSeries M =
      1 +
        PowerSeries.X •
          (geometricPowerSeries M *
            powerSeriesConstMatrix M) := by
  ext i j k
  cases k with
  | zero =>
      simp [
        geometricPowerSeries,
        powerSeriesConstMatrix,
        Matrix.one_apply,
        Matrix.mul_apply
      ]
  | succ k =>
      simp only [
        geometricPowerSeries,
        powerSeriesConstMatrix,
        PowerSeries.coeff_mk,
        Matrix.add_apply,
        Matrix.smul_apply,
        PowerSeries.coeff_smul,
        PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_mul_C,
        Matrix.one_apply
      ]
      rw [pow_succ]
      simp [Matrix.mul_apply]

/-- The formal geometric matrix is a left inverse of I-XM. -/
theorem resolvent_mul_geometric
    (M : Matrix n n R) :
    resolventDenominator M *
        geometricPowerSeries M =
      1 := by
  have h := geometric_eq_one_add_X_mul M
  unfold resolventDenominator
  calc
    (1 -
        PowerSeries.X •
          powerSeriesConstMatrix M) *
        geometricPowerSeries M
        =
      geometricPowerSeries M -
        PowerSeries.X •
          (powerSeriesConstMatrix M *
            geometricPowerSeries M) := by
              simp [sub_mul, Matrix.smul_mul]
    _ = 1 := by
      rw [h]
      abel

/-- And also a right inverse. -/
theorem geometric_mul_resolvent
    (M : Matrix n n R) :
    geometricPowerSeries M *
        resolventDenominator M =
      1 := by
  have h :=
    geometric_eq_one_add_X_mul_right M
  unfold resolventDenominator
  calc
    geometricPowerSeries M *
        (1 -
          PowerSeries.X •
            powerSeriesConstMatrix M)
        =
      geometricPowerSeries M -
        PowerSeries.X •
          (geometricPowerSeries M *
            powerSeriesConstMatrix M) := by
              simp [Matrix.mul_sub, Matrix.mul_smul]
    _ = 1 := by
      rw [h]
      abel

/-- Trace of the geometric resolvent has coefficient tr(M^k). -/
theorem coeff_trace_geometricPowerSeries
    (M : Matrix n n R)
    (k : ℕ) :
    PowerSeries.coeff k
        (trace
          (geometricPowerSeries M)) =
      trace (M ^ k) := by
  unfold trace
  simp [
    geometricPowerSeries
  ]

/-- Trace of M*G has shifted power traces. -/
theorem coeff_trace_const_mul_geometric
    (M : Matrix n n R)
    (k : ℕ) :
    PowerSeries.coeff k
        (trace
          (powerSeriesConstMatrix M *
            geometricPowerSeries M)) =
      trace (M ^ (k + 1)) := by
  unfold trace
  simp only [
    Matrix.diag_apply,
    Matrix.mul_apply,
    powerSeriesConstMatrix,
    Matrix.map_apply,
    geometricPowerSeries,
    PowerSeries.coeff_sum,
    PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mk
  ]
  rw [pow_succ']
  simp [Matrix.mul_apply]

/-- Power-series trace sequence as an explicit series. -/
def tracePowerSeries
    (M : Matrix n n R) :
    PowerSeries R :=
  PowerSeries.mk fun k =>
    trace (M ^ (k + 1))

@[simp] theorem coeff_tracePowerSeries
    (M : Matrix n n R)
    (k : ℕ) :
    PowerSeries.coeff k
        (tracePowerSeries M) =
      trace (M ^ (k + 1)) :=
  rfl

/-- tr(MG)=sum tr(M^(k+1)) X^k. -/
theorem trace_const_mul_geometric
    (M : Matrix n n R) :
    trace
        (powerSeriesConstMatrix M *
          geometricPowerSeries M) =
      tracePowerSeries M := by
  rw [PowerSeries.ext_iff]
  intro k
  exact
    coeff_trace_const_mul_geometric M k

end Matrix
end CausalGeometry
