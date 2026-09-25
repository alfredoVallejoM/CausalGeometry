import CausalGeometry.Cyclic.EulerLogSeries
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution

namespace CausalGeometry

namespace PrimitiveTraceCounts

variable (P : PrimitiveTraceCounts)

/-- The Euler logarithm has vanishing constant term, so it is admissible as a
formal substitution parameter. -/
theorem constantCoeff_eulerLogSeries :
    PowerSeries.constantCoeff
        P.eulerLogSeries = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact P.coeff_eulerLogSeries_zero

/-- Formal substitution admissibility for the Euler logarithm. -/
theorem eulerLog_hasSubst :
    PowerSeries.HasSubst
      P.eulerLogSeries :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    P.constantCoeff_eulerLogSeries

/-- Formal Euler zeta series.

This is exp(L_P), with L_P the certified Euler logarithm.  It is a purely
formal power series and makes no analytic convergence claim. -/
def eulerZetaSeries :
    PowerSeries ℚ :=
  (PowerSeries.exp ℚ).subst
    P.eulerLogSeries

/-- Primitive-count presentation of the same zeta series. -/
def primitiveEulerZetaSeries :
    PowerSeries ℚ :=
  (PowerSeries.exp ℚ).subst
    P.primitiveEulerLogSeries

/-- The primitive and closed-count constructions agree before any matrix
comparison enters. -/
theorem primitiveEulerZetaSeries_eq :
    P.primitiveEulerZetaSeries =
      P.eulerZetaSeries := by
  unfold primitiveEulerZetaSeries
    eulerZetaSeries
  rw [P.primitiveEulerLogSeries_eq]

/-- Formal Euler zeta is normalized by Z(0)=1. -/
@[simp] theorem constantCoeff_eulerZetaSeries :
    PowerSeries.constantCoeff
        P.eulerZetaSeries = 1 := by
  unfold eulerZetaSeries
  rw [
    PowerSeries.constantCoeff_eq,
    PowerSeries.constantCoeff_subst_of_constantCoeff_zero
      P.constantCoeff_eulerLogSeries,
    PowerSeries.constantCoeff_exp,
    map_one
  ]

/-- Formal differential equation Z'=Z*T, where T stores the closed trace
sequence N_(n+1). -/
theorem derivative_eulerZetaSeries :
    PowerSeries.derivative
        P.eulerZetaSeries =
      P.eulerZetaSeries *
        P.traceSeries := by
  unfold eulerZetaSeries
  rw [
    PowerSeries.derivative_subst
      (hg := P.eulerLog_hasSubst),
    PowerSeries.derivative_exp,
    P.derivative_eulerLogSeries
  ]

/-- The primitive presentation satisfies the same differential equation. -/
theorem derivative_primitiveEulerZetaSeries :
    PowerSeries.derivative
        P.primitiveEulerZetaSeries =
      P.primitiveEulerZetaSeries *
        P.traceSeries := by
  rw [P.primitiveEulerZetaSeries_eq]
  exact P.derivative_eulerZetaSeries

/-- The formal zeta is a unit, because exp is a unit and substitution preserves
the explicit inverse relation. -/
theorem isUnit_eulerZetaSeries :
    IsUnit P.eulerZetaSeries := by
  unfold eulerZetaSeries
  exact
    (PowerSeries.isUnit_exp ℚ).map
      (PowerSeries.substAlgHom
        P.eulerLog_hasSubst)

/-- Therefore its logarithmic derivative is exactly the trace series. -/
theorem derivative_mul_inv_eq_traceSeries :
    PowerSeries.derivative
          P.eulerZetaSeries *
        P.eulerZetaSeries⁻¹ =
      P.traceSeries := by
  rw [P.derivative_eulerZetaSeries]
  have hunit := P.isUnit_eulerZetaSeries
  rw [mul_assoc]
  rw [IsUnit.mul_inv_cancel hunit]
  simp

end PrimitiveTraceCounts

namespace HashimotoPrimitiveComparison

variable
    {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    {G : FiniteDirectedEdgeSystem Vertex Edge}
    (C : HashimotoPrimitiveComparison G)

/-- Hashimoto Euler zeta attached to the independently certified primitive
comparison. -/
def hashimotoEulerZetaSeries :
    PowerSeries ℚ :=
  C.counts.eulerZetaSeries

@[simp] theorem constantCoeff_hashimotoEulerZetaSeries :
    PowerSeries.constantCoeff
        C.hashimotoEulerZetaSeries = 1 :=
  C.counts.constantCoeff_eulerZetaSeries

/-- Exact formal Hashimoto log-derivative identity. -/
theorem derivative_hashimotoEulerZetaSeries :
    PowerSeries.derivative
        C.hashimotoEulerZetaSeries =
      C.hashimotoEulerZetaSeries *
        C.hashimotoTraceSeries := by
  change
    PowerSeries.derivative
        C.counts.eulerZetaSeries =
      C.counts.eulerZetaSeries *
        C.hashimotoTraceSeries
  rw [
    C.counts.derivative_eulerZetaSeries,
    C.counts_traceSeries_eq_hashimoto
  ]

/-- Equivalent logarithmic-derivative formulation. -/
theorem hashimoto_logDerivative :
    PowerSeries.derivative
          C.hashimotoEulerZetaSeries *
        C.hashimotoEulerZetaSeries⁻¹ =
      C.hashimotoTraceSeries := by
  change
    PowerSeries.derivative
          C.counts.eulerZetaSeries *
        C.counts.eulerZetaSeries⁻¹ =
      C.hashimotoTraceSeries
  rw [
    C.counts.derivative_mul_inv_eq_traceSeries,
    C.counts_traceSeries_eq_hashimoto
  ]

end HashimotoPrimitiveComparison
end CausalGeometry
