import CausalGeometry.Cyclic.MatrixJacobi
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic

namespace CausalGeometry

open Polynomial

universe u

namespace Matrix

variable
    {n : Type u}
    [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R]

/-- Symbolic Jacobi formula for the characteristic-type determinant
D_M(X)=det(I-XM).

No invertibility assumption is needed. -/
theorem derivative_det_one_sub_X_smul
    (M : Matrix n n R) :
    derivative
        (det
          (1 -
            (X : R[X]) •
              M.map C))
      =
    - trace
        (M.map C *
          adjugate
            (1 -
              (X : R[X]) •
                M.map C)) := by
  let A :
      Matrix n n R[X] :=
    1 -
      (X : R[X]) •
        M.map C

  let B :
      Matrix n n R[X] :=
    -(M.map C)

  let D : R[X] :=
    det A

  let cR : R →+* R[X] :=
    C

  let cS :
      R[X] →+* (R[X])[X] :=
    C

  let mapVar :
      R[X] →+* (R[X])[X] :=
    Polynomial.mapRingHom cR

  let shift :
      (R[X])[X] →+* (R[X])[X] :=
    (Polynomial.taylorAlgHom
      (X : R[X])).toRingHom

  have hmapD :
      D.map cR =
        det (A.map mapVar) := by
    exact
      (RingHom.map_det mapVar A).symm

  have hTaylor :
      (D.map cR).taylor
          (X : R[X]) =
        det
          (A.map cS +
            (X : (R[X])[X]) •
              B.map cS) := by
    rw [hmapD]
    change
      shift (det (A.map mapVar)) =
        _
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [
      shift,
      mapVar,
      cR,
      cS,
      A,
      B,
      Polynomial.taylorAlgHom,
      Polynomial.taylor_apply,
      Polynomial.mapRingHom,
      Matrix.one_apply
    ]
    by_cases hij : i = j
    · subst j
      simp [Matrix.one_apply]
      ring
    · simp [Matrix.one_apply, hij]
      ring

  have hcoeff :
      ((D.map cR).taylor
        (X : R[X])).coeff 1 =
        derivative D := by
    rw [Polynomial.taylor_coeff_one]
    rw [Polynomial.derivative_map]
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_C_X

  have hdir :=
    Matrix.coeff_det_add_X_smul_one_eq_trace_mul_adjugate
      A B

  rw [← hTaylor] at hdir
  rw [hcoeff] at hdir

  change
    derivative
        (det
          (1 -
            (X : R[X]) •
              M.map C))
      =
    - trace
        (M.map C *
          adjugate
            (1 -
              (X : R[X]) •
                M.map C))

  change derivative D =
    - trace (M.map C * adjugate A)

  rw [hdir]
  unfold B
  simp [Matrix.neg_mul]

end Matrix
end CausalGeometry
