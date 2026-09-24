import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

namespace CausalGeometry

universe u v

/-- Finite transfer system used by graph/Hashimoto/Ihara realizations.

The carrier only supplies a finite weighted transition matrix. Identifying its
trace sequence or determinant with a primitive-cycle Euler product is a
separate realization theorem. -/
structure FiniteTransferSystem
    (R : Type v) [CommRing R] where
  State : Type u
  finite : Fintype State
  decEq : DecidableEq State
  weight : State → State → R

namespace FiniteTransferSystem

variable {R : Type v} [CommRing R]
variable (T : FiniteTransferSystem.{u, v} R)

def matrix :
    Matrix T.State T.State R :=
  T.weight

/-- Closed-walk/transfer trace at iterate n. -/
def tracePower (n : ℕ) : R := by
  letI : Fintype T.State := T.finite
  letI : DecidableEq T.State := T.decEq
  exact Matrix.trace (T.matrix ^ n)

/-- Finite determinant kernel det(I - uT). This is algebraic data only; no
analytic continuation or zeta identification is assumed. -/
def determinantKernel (u : R) : R := by
  letI : Fintype T.State := T.finite
  letI : DecidableEq T.State := T.decEq
  exact Matrix.det (1 - u • T.matrix)

@[simp] theorem tracePower_one :
    T.tracePower 1 = Matrix.trace T.matrix := by
  letI : Fintype T.State := T.finite
  letI : DecidableEq T.State := T.decEq
  simp [tracePower]

@[simp] theorem determinantKernel_zero :
    T.determinantKernel 0 = 1 := by
  letI : Fintype T.State := T.finite
  letI : DecidableEq T.State := T.decEq
  simp [determinantKernel]

/-- The full finite trace sequence exposed as a typed observable. -/
def traceSequence : ℕ → R :=
  T.tracePower

end FiniteTransferSystem

/-- Explicit comparison boundary between a causal/cyclic trace sequence and a
finite transfer system. The source of the trace sequence is intentionally left
generic, so primitive-cycle counting must be proved by the consumer. -/
structure TransferTraceComparison
    {R : Type v} [CommRing R]
    (T : FiniteTransferSystem.{u, v} R)
    (sourceTrace : ℕ → R) : Prop where
  trace_matches :
    ∀ n, T.tracePower n = sourceTrace n

end CausalGeometry
