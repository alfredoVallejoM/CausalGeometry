import CausalGeometry.Cyclic.PrimitiveTrace
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

namespace CausalGeometry

namespace PrimitiveTraceCounts

variable (P : PrimitiveTraceCounts)

/-- Closed-walk/trace generating series with the indexing shifted so that
coefficient n stores N_(n+1). This is exactly the natural target of a formal
derivative. -/
def traceSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    (P.closed (n + 1) : ℚ)

@[simp] theorem coeff_traceSeries
    (n : ℕ) :
    PowerSeries.coeff n P.traceSeries =
      (P.closed (n + 1) : ℚ) := by
  simp [traceSeries]

/-- Formal Euler logarithm built from the closed trace counts:
coefficient n>0 is N_n/n and the constant term is zero. -/
def eulerLogSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    if n = 0 then 0
    else (P.closed n : ℚ) / (n : ℚ)

@[simp] theorem coeff_eulerLogSeries_zero :
    PowerSeries.coeff 0 P.eulerLogSeries = 0 := by
  simp [eulerLogSeries]

theorem coeff_eulerLogSeries
    {n : ℕ} (hn : 0 < n) :
    PowerSeries.coeff n P.eulerLogSeries =
      (P.closed n : ℚ) / (n : ℚ) := by
  simp [eulerLogSeries,
    Nat.ne_of_gt hn]

/-- The derivative of the Euler logarithm is exactly the shifted trace
series. -/
theorem derivative_eulerLogSeries :
    PowerSeries.derivative P.eulerLogSeries =
      P.traceSeries := by
  rw [PowerSeries.ext_iff]
  intro n
  rw [PowerSeries.coeff_derivative]
  rw [P.coeff_eulerLogSeries
    (Nat.succ_pos n)]
  rw [P.coeff_traceSeries]
  have hn :
      ((n + 1 : ℕ) : ℚ) ≠ 0 := by
    positivity
  field_simp

/-- The same Euler logarithm coefficient expressed directly from primitive
period counts. -/
def primitiveEulerLogSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    if n = 0 then 0
    else
      (∑ d ∈ n.divisors,
        (d : ℚ) *
          (P.primitive d : ℚ)) /
        (n : ℚ)

@[simp] theorem coeff_primitiveEulerLogSeries_zero :
    PowerSeries.coeff 0
        P.primitiveEulerLogSeries =
      0 := by
  simp [primitiveEulerLogSeries]

theorem coeff_primitiveEulerLogSeries
    {n : ℕ} (hn : 0 < n) :
    PowerSeries.coeff n
        P.primitiveEulerLogSeries =
      (∑ d ∈ n.divisors,
        (d : ℚ) *
          (P.primitive d : ℚ)) /
        (n : ℚ) := by
  simp [primitiveEulerLogSeries,
    Nat.ne_of_gt hn]

/-- Primitive divisor data and closed-trace data define exactly the same formal
Euler logarithm. -/
theorem primitiveEulerLogSeries_eq :
    P.primitiveEulerLogSeries =
      P.eulerLogSeries := by
  rw [PowerSeries.ext_iff]
  intro n
  cases n with
  | zero =>
      simp
  | succ n =>
      rw [
        P.coeff_primitiveEulerLogSeries
          (Nat.succ_pos n),
        P.coeff_eulerLogSeries
          (Nat.succ_pos n)
      ]
      congr 1
      have h :=
        P.decomposition
          (n + 1) (Nat.succ_pos n)
      exact_mod_cast h

/-- Consequently the primitive Euler logarithm has trace series as its formal
derivative. -/
theorem derivative_primitiveEulerLogSeries :
    PowerSeries.derivative
        P.primitiveEulerLogSeries =
      P.traceSeries := by
  rw [P.primitiveEulerLogSeries_eq]
  exact P.derivative_eulerLogSeries

end PrimitiveTraceCounts

namespace HashimotoPrimitiveComparison

variable
    {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    {G : FiniteDirectedEdgeSystem Vertex Edge}
    (C : HashimotoPrimitiveComparison G)

/-- Formal series of Hashimoto power traces. -/
def hashimotoTraceSeries :
    PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    ((G.hashimotoTransfer ℤ).tracePower
      (n + 1) : ℚ)

@[simp] theorem coeff_hashimotoTraceSeries
    (n : ℕ) :
    PowerSeries.coeff n
        C.hashimotoTraceSeries =
      ((G.hashimotoTransfer ℤ).tracePower
        (n + 1) : ℚ) := by
  simp [hashimotoTraceSeries]

/-- The abstract closed-count trace series is the concrete Hashimoto trace
series whenever the primitive comparison is certified. -/
theorem counts_traceSeries_eq_hashimoto :
    C.counts.traceSeries =
      C.hashimotoTraceSeries := by
  rw [PowerSeries.ext_iff]
  intro n
  simp [
    PrimitiveTraceCounts.traceSeries,
    hashimotoTraceSeries,
    C.trace_matches
  ]

/-- Full primitive-to-Hashimoto formal logarithmic derivative identity. -/
theorem derivative_primitiveEulerLog_eq_hashimotoTrace :
    PowerSeries.derivative
        C.counts.primitiveEulerLogSeries =
      C.hashimotoTraceSeries := by
  rw [
    C.counts.derivative_primitiveEulerLogSeries,
    C.counts_traceSeries_eq_hashimoto
  ]

/-- Equivalent formulation through the closed-count Euler logarithm. -/
theorem derivative_eulerLog_eq_hashimotoTrace :
    PowerSeries.derivative
        C.counts.eulerLogSeries =
      C.hashimotoTraceSeries := by
  rw [
    C.counts.derivative_eulerLogSeries,
    C.counts_traceSeries_eq_hashimoto
  ]

end HashimotoPrimitiveComparison
end CausalGeometry
