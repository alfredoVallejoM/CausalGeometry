import CausalGeometry.Cyclic.MatrixJacobi
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Tactic

namespace CausalGeometry

open Polynomial

universe u

namespace Matrix

variable
    {n : Type u}
    [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R]

/-- Reverse characteristic determinant D_M(X)=det(I-XM). -/
def detOneSubX
    (M : Matrix n n R) :
    R[X] :=
  det
    (1 -
      (X : R[X]) • M.map C)

/-- Taylor-shifting D_M by the symbolic base point X is the same as taking
the determinant after the matrix substitution
I-(X_inner+X_outer)M. -/
theorem taylor_map_detOneSubX
    (M : Matrix n n R) :
    taylor (X : R[X])
        ((detOneSubX M).map C) =
      det
        (((1 -
            (X : R[X]) • M.map C) :
              Matrix n n R[X]).map C
          +
          (X : R[X][X]) •
            (-(M.map C)).map C) := by
  let φ :
      R[X] →+* R[X][X] :=
    (taylorAlgHom
      (X : R[X])).toRingHom.comp
        (Polynomial.mapRingHom
          (C : R →+* R[X]))
  change
    φ
        (det
          (1 -
            (X : R[X]) • M.map C))
      =
    det
      (((1 -
          (X : R[X]) • M.map C) :
            Matrix n n R[X]).map C
        +
        (X : R[X][X]) •
          (-(M.map C)).map C)
  rw [RingHom.map_det]
  apply congrArg det
  ext i j
  simp [
    φ,
    Matrix.map_apply,
    Matrix.one_apply
  ]
  ring

/-- The linear Taylor coefficient of D_M at symbolic X is its ordinary
polynomial derivative. -/
theorem coeff_one_taylor_map_detOneSubX
    (M : Matrix n n R) :
    (taylor (X : R[X])
      ((detOneSubX M).map C)).coeff 1 =
      (detOneSubX M).derivative := by
  rw [taylor_coeff_one]
  rw [derivative_map]
  change
    ((detOneSubX M).derivative.map C).eval X =
      (detOneSubX M).derivative
  rw [← eval₂_eq_eval_map]
  exact eval₂_C_X

/-- Global polynomial Jacobi formula for D_M(X)=det(I-XM).

No invertibility of I-XM is required:
D'_M(X) = -tr(M adj(I-XM)).
-/
theorem derivative_detOneSubX
    (M : Matrix n n R) :
    (detOneSubX M).derivative =
      -
      trace
        ((M.map C) *
          adjugate
            (1 -
              (X : R[X]) •
                M.map C)) := by
  let A :
      Matrix n n R[X] :=
    1 -
      (X : R[X]) • M.map C
  let B :
      Matrix n n R[X] :=
    -(M.map C)
  have hshift :=
    congrArg
      (fun p : R[X][X] =>
        p.coeff 1)
      (taylor_map_detOneSubX M)
  have hj :=
    coeff_det_add_X_smul_one_eq_trace_mul_adjugate
      A B
  calc
    (detOneSubX M).derivative
        =
      (taylor (X : R[X])
        ((detOneSubX M).map C)).coeff 1 := by
          symm
          exact coeff_one_taylor_map_detOneSubX M
    _ =
      (det
        (A.map C +
          (X : R[X][X]) •
            B.map C)).coeff 1 := by
          simpa [A, B] using hshift
    _ = trace (B * adjugate A) := hj
    _ =
      -
      trace
        ((M.map C) *
          adjugate
            (1 -
              (X : R[X]) •
                M.map C)) := by
          simp [A, B]

/-- Equivalent sign-free form. -/
theorem neg_derivative_detOneSubX
    (M : Matrix n n R) :
    -
      (detOneSubX M).derivative =
      trace
        ((M.map C) *
          adjugate
            (1 -
              (X : R[X]) •
                M.map C)) := by
  rw [derivative_detOneSubX]
  simp

end Matrix
end CausalGeometry
