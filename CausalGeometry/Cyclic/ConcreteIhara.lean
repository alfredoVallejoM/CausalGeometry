import CausalGeometry.Cyclic.EulerZetaSeries
import CausalGeometry.Cyclic.TransferDeterminant
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic

namespace CausalGeometry

open Finset

namespace PowerSeries

/-- Uniqueness for the formal first-order equation F'=F*T over Q.

Unlike an analytic ODE theorem, this is purely coefficient-recursive: the
coefficient of degree n+1 is determined by the previous coefficients and the
fixed trace series T. -/
theorem eq_of_derivative_eq_mul
    {F G T : PowerSeries ℚ}
    (hzero :
      PowerSeries.coeff 0 F =
        PowerSeries.coeff 0 G)
    (hF :
      PowerSeries.derivative F =
        F * T)
    (hG :
      PowerSeries.derivative G =
        G * T) :
    F = G := by
  rw [PowerSeries.ext_iff]
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          exact hzero
      | succ n =>
          have hFc :=
            congrArg
              (PowerSeries.coeff n) hF
          have hGc :=
            congrArg
              (PowerSeries.coeff n) hG
          rw [
            PowerSeries.coeff_derivative,
            PowerSeries.coeff_mul
          ] at hFc hGc
          have hsum :
              (∑ x ∈ antidiagonal n,
                PowerSeries.coeff x.1 F *
                  PowerSeries.coeff x.2 T) =
                ∑ x ∈ antidiagonal n,
                  PowerSeries.coeff x.1 G *
                    PowerSeries.coeff x.2 T := by
            apply Finset.sum_congr rfl
            intro x hx
            have hxy :
                x.1 + x.2 = n :=
              Finset.mem_antidiagonal.mp hx
            have hlt :
                x.1 < n + 1 := by
              omega
            rw [ih x.1 hlt]
          rw [hsum] at hFc
          have hm :
              PowerSeries.coeff (n + 1) F *
                    ((n + 1 : ℕ) : ℚ) =
                PowerSeries.coeff (n + 1) G *
                    ((n + 1 : ℕ) : ℚ) :=
            hFc.trans hGc.symm
          exact
            mul_right_cancel₀
              (by positivity :
                ((n + 1 : ℕ) : ℚ) ≠ 0)
              hm

end PowerSeries

namespace FiniteDirectedEdgeSystem

variable
    {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    (G : FiniteDirectedEdgeSystem Vertex Edge)

/-- det(I-XH), now embedded concretely into Q[[X]]. -/
def hashimotoDeterminantPowerSeries :
    PowerSeries ℚ :=
  ((G.hashimotoDeterminantPolynomial.map
      (Int.castRingHom ℚ) : ℚ[X]) :
    PowerSeries ℚ)

@[simp] theorem hashimotoDeterminantPowerSeries_coeff_zero :
    PowerSeries.coeff 0
        G.hashimotoDeterminantPowerSeries =
      1 := by
  simp [
    hashimotoDeterminantPowerSeries,
    FiniteDirectedEdgeSystem.hashimotoDeterminantPolynomial,
    FiniteTransferSystem.determinantPolynomial_coeff_zero
  ]

@[simp] theorem hashimotoDeterminantPowerSeries_constantCoeff :
    PowerSeries.constantCoeff
        G.hashimotoDeterminantPowerSeries =
      1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact G.hashimotoDeterminantPowerSeries_coeff_zero

/-- Concrete reciprocal determinant series det(I-XH)^(-1). -/
def hashimotoDeterminantReciprocal :
    PowerSeries ℚ :=
  PowerSeries.invOfUnit
    G.hashimotoDeterminantPowerSeries 1

@[simp] theorem hashimotoDeterminantReciprocal_constantCoeff :
    PowerSeries.constantCoeff
        G.hashimotoDeterminantReciprocal =
      1 := by
  simp [hashimotoDeterminantReciprocal]

/-- The reciprocal is genuinely inverse to the determinant power series. -/
theorem determinant_mul_reciprocal :
    G.hashimotoDeterminantPowerSeries *
        G.hashimotoDeterminantReciprocal =
      1 := by
  unfold hashimotoDeterminantReciprocal
  exact
    PowerSeries.mul_invOfUnit
      G.hashimotoDeterminantPowerSeries
      1
      (by
        simpa using
          G.hashimotoDeterminantPowerSeries_constantCoeff)

theorem reciprocal_mul_determinant :
    G.hashimotoDeterminantReciprocal *
        G.hashimotoDeterminantPowerSeries =
      1 := by
  unfold hashimotoDeterminantReciprocal
  exact
    PowerSeries.invOfUnit_mul
      G.hashimotoDeterminantPowerSeries
      1
      (by
        simpa using
          G.hashimotoDeterminantPowerSeries_constantCoeff)

end FiniteDirectedEdgeSystem

/-- The sole nontrivial finite-matrix identity still required for a completely
concrete Ihara theorem.

Everything else -- primitive decomposition, Euler logarithm, Euler zeta,
normalization, and uniqueness -- is now proved independently. -/
structure HashimotoDeterminantTraceBridge
    {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    (G : FiniteDirectedEdgeSystem Vertex Edge) : Prop where

  differential :
    PowerSeries.derivative
        G.hashimotoDeterminantReciprocal =
      G.hashimotoDeterminantReciprocal *
        (PowerSeries.mk fun n =>
          ((G.hashimotoTransfer ℤ).tracePower
            (n + 1) : ℚ))

namespace HashimotoDeterminantTraceBridge

variable
    {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    {G : FiniteDirectedEdgeSystem Vertex Edge}
    (B : HashimotoDeterminantTraceBridge G)

theorem differential_eq_hashimotoTraceSeries
    (C : HashimotoPrimitiveComparison G) :
    PowerSeries.derivative
        G.hashimotoDeterminantReciprocal =
      G.hashimotoDeterminantReciprocal *
        C.hashimotoTraceSeries := by
  exact B.differential

/-- Once determinant-versus-trace is supplied, the determinant reciprocal and
the independently constructed primitive Euler zeta are forced to be equal. -/
theorem reciprocal_eq_eulerZeta
    (C : HashimotoPrimitiveComparison G) :
    G.hashimotoDeterminantReciprocal =
      C.hashimotoEulerZetaSeries := by
  apply PowerSeries.eq_of_derivative_eq_mul
    (T := C.hashimotoTraceSeries)
  · rw [
      PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_zero_eq_constantCoeff_apply
    ]
    simp
  · exact
      B.differential_eq_hashimotoTraceSeries C
  · exact
      C.derivative_hashimotoEulerZetaSeries

/-- Concrete finite Ihara identity in Q[[X]]. -/
theorem ihara_powerSeries_identity
    (C : HashimotoPrimitiveComparison G) :
    PowerSeries.invOfUnit
        G.hashimotoDeterminantPowerSeries 1 =
      C.hashimotoEulerZetaSeries := by
  exact B.reciprocal_eq_eulerZeta C

end HashimotoDeterminantTraceBridge

/-- Completely typed concrete finite Ihara package.

Unlike FiniteIharaCertificate, there is no arbitrary target object and no
arbitrary pair of interpretation functions. -/
structure ConcreteFiniteIhara
    {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    (G : FiniteDirectedEdgeSystem Vertex Edge) where
  primitive :
    HashimotoPrimitiveComparison G
  determinantTrace :
    HashimotoDeterminantTraceBridge G

namespace ConcreteFiniteIhara

variable
    {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    {G : FiniteDirectedEdgeSystem Vertex Edge}
    (I : ConcreteFiniteIhara G)

theorem ihara :
    G.hashimotoDeterminantReciprocal =
      I.primitive.hashimotoEulerZetaSeries :=
  I.determinantTrace.reciprocal_eq_eulerZeta
    I.primitive

end ConcreteFiniteIhara
end CausalGeometry
