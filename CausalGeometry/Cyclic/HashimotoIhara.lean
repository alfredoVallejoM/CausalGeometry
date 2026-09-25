import CausalGeometry.Cyclic.ConcreteIhara
import CausalGeometry.Cyclic.MatrixDeterminantResolvent
import Mathlib.Tactic

namespace CausalGeometry

namespace FiniteDirectedEdgeSystem

variable
    {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    (G : FiniteDirectedEdgeSystem Vertex Edge)

/-- Rational Hashimoto matrix obtained by coefficient extension from Z to Q. -/
def hashimotoMatrixQ :
    Matrix Edge Edge ℚ :=
  (G.hashimotoTransfer ℤ).matrix.map
    (Int.castRingHom ℚ)

@[simp] theorem hashimotoMatrixQ_apply
    (e f : Edge) :
    G.hashimotoMatrixQ e f =
      ((G.hashimotoTransfer ℤ).matrix e f : ℚ) :=
  rfl

/-- Power traces commute with coefficient extension from integers to
rationals. -/
theorem trace_hashimotoMatrixQ_pow
    (n : ℕ) :
    Matrix.trace
        (G.hashimotoMatrixQ ^ n) =
      ((G.hashimotoTransfer ℤ).tracePower n : ℚ) := by
  unfold hashimotoMatrixQ
  rw [← Matrix.map_pow]
  rw [← AddMonoidHom.map_trace]
  rfl

/-- The generic rational matrix trace series is exactly the previously defined
Hashimoto trace series. -/
theorem matrix_tracePowerSeries_eq_hashimoto
    :
    Matrix.tracePowerSeries
        G.hashimotoMatrixQ =
      PowerSeries.mk fun n =>
        ((G.hashimotoTransfer ℤ).tracePower
          (n + 1) : ℚ) := by
  rw [PowerSeries.ext_iff]
  intro n
  simp [
    Matrix.tracePowerSeries,
    G.trace_hashimotoMatrixQ_pow
  ]

/-- The generic determinant polynomial after rational extension is the mapped
integer Hashimoto determinant polynomial. -/
theorem determinantPolynomial_map_rat :
    G.hashimotoDeterminantPolynomial.map
        (Int.castRingHom ℚ) =
      Matrix.detOneSubX
        G.hashimotoMatrixQ := by
  unfold
    FiniteDirectedEdgeSystem.hashimotoDeterminantPolynomial
    FiniteTransferSystem.determinantPolynomial
    Matrix.detOneSubX
    hashimotoMatrixQ
  rw [RingHom.map_det]
  apply congrArg Matrix.det
  ext i j
  simp [
    Matrix.map_apply,
    Matrix.one_apply
  ]

/-- Consequently the determinant power series agrees with the generic matrix
construction over Q. -/
theorem determinantPowerSeries_eq_hashimoto :
    Matrix.determinantPowerSeries
        G.hashimotoMatrixQ =
      G.hashimotoDeterminantPowerSeries := by
  unfold
    Matrix.determinantPowerSeries
    FiniteDirectedEdgeSystem.hashimotoDeterminantPowerSeries
  rw [← G.determinantPolynomial_map_rat]

/-- And the reciprocal determinant series is the same object. -/
theorem determinantReciprocal_eq_hashimoto :
    Matrix.determinantReciprocal
        G.hashimotoMatrixQ =
      G.hashimotoDeterminantReciprocal := by
  unfold
    Matrix.determinantReciprocal
    FiniteDirectedEdgeSystem.hashimotoDeterminantReciprocal
  rw [G.determinantPowerSeries_eq_hashimoto]

end FiniteDirectedEdgeSystem

/-- The determinant/trace bridge is no longer an assumption: every finite
Hashimoto system has it canonically. -/
def canonicalHashimotoDeterminantTraceBridge
    {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    (G : FiniteDirectedEdgeSystem Vertex Edge) :
    HashimotoDeterminantTraceBridge G where
  differential := by
    have h :=
      Matrix.derivative_determinantReciprocal
        G.hashimotoMatrixQ
    rw [
      G.determinantReciprocal_eq_hashimoto,
      G.matrix_tracePowerSeries_eq_hashimoto
    ] at h
    exact h

namespace HashimotoPrimitiveComparison

variable
    {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    {G : FiniteDirectedEdgeSystem Vertex Edge}
    (C : HashimotoPrimitiveComparison G)

/-- Every primitive comparison now determines a completely concrete finite
Ihara package, with no additional determinant hypothesis. -/
def toConcreteFiniteIhara :
    ConcreteFiniteIhara G where
  primitive := C
  determinantTrace :=
    canonicalHashimotoDeterminantTraceBridge G

/-- General finite Ihara identity.

Once the combinatorial primitive decomposition has been certified, the
determinant identity is automatic for every finite graph. -/
theorem ihara :
    G.hashimotoDeterminantReciprocal =
      C.hashimotoEulerZetaSeries :=
  C.toConcreteFiniteIhara.ihara

/-- Equivalent differential form: determinant reciprocal and primitive Euler
zeta solve the same trace ODE with constant term one. -/
theorem determinantReciprocal_derivative :
    PowerSeries.derivative
        G.hashimotoDeterminantReciprocal =
      G.hashimotoDeterminantReciprocal *
        C.hashimotoTraceSeries := by
  exact
    (canonicalHashimotoDeterminantTraceBridge G)
      |>.differential_eq_hashimotoTraceSeries C

end HashimotoPrimitiveComparison
end CausalGeometry
