import CausalGeometry.Cyclic.FiniteTransfer
import Mathlib.RingTheory.MatrixPolynomialAlgebra

namespace CausalGeometry

universe u v

namespace FiniteTransferSystem

variable {R : Type v} [CommRing R]
variable (T : FiniteTransferSystem.{u, v} R)

/-- Universal finite determinant polynomial D_T(X)=det(I-XT). -/
def determinantPolynomial : R[X] := by
  letI : Fintype T.State := T.finite
  letI : DecidableEq T.State := T.decEq
  exact Matrix.det
    (1 - (Polynomial.X : R[X]) •
      T.matrix.map Polynomial.C)

/-- Evaluating the universal determinant polynomial at u gives exactly the
finite determinant kernel already attached to the transfer system. -/
theorem determinantPolynomial_eval
    (u : R) :
    (T.determinantPolynomial).eval u =
      T.determinantKernel u := by
  letI : Fintype T.State := T.finite
  letI : DecidableEq T.State := T.decEq
  unfold determinantPolynomial determinantKernel
  rw [eval_det]
  apply congrArg Matrix.det
  rw [matPolyEquiv_eval_eq_map]
  ext i j
  simp [Matrix.one_apply]

@[simp] theorem determinantPolynomial_eval_zero :
    (T.determinantPolynomial).eval 0 = 1 := by
  rw [T.determinantPolynomial_eval]
  exact T.determinantKernel_zero

/-- The constant coefficient of D_T is one. -/
@[simp] theorem determinantPolynomial_coeff_zero :
    T.determinantPolynomial.coeff 0 = 1 := by
  simpa [Polynomial.eval_zero] using
    T.determinantPolynomial_eval_zero

end FiniteTransferSystem

namespace FiniteDirectedEdgeSystem

variable
    {Vertex Edge : Type u}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    (G : FiniteDirectedEdgeSystem Vertex Edge)

/-- Hashimoto/Ihara determinant polynomial det(I-XH). -/
def hashimotoDeterminantPolynomial :
    ℤ[X] :=
  (G.hashimotoTransfer ℤ).determinantPolynomial

@[simp] theorem hashimotoDeterminantPolynomial_eval
    (u : ℤ) :
    G.hashimotoDeterminantPolynomial.eval u =
      (G.hashimotoTransfer ℤ).determinantKernel u :=
  (G.hashimotoTransfer ℤ).determinantPolynomial_eval u

end FiniteDirectedEdgeSystem

/-- Explicit boundary for calling a finite transfer determinant an Ihara
realization.  The primitive-cycle side is independent data and the equality
must be proved by the consumer rather than attached by name. -/
structure FiniteIharaCertificate
    {Vertex Edge : Type u}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    (G : FiniteDirectedEdgeSystem Vertex Edge) where
  primitiveComparison :
    HashimotoPrimitiveComparison G

  /-- Target-specific Ihara object. It can be a rational function, formal
  power series, or another exact finite representation. -/
  IharaObject : Type v

  fromDeterminant :
    ℤ[X] → IharaObject

  fromPrimitiveCounts :
    (ℕ → ℤ) → IharaObject

  determinant_primitive_agree :
    fromDeterminant G.hashimotoDeterminantPolynomial =
      fromPrimitiveCounts primitiveComparison.counts.primitive

end CausalGeometry
