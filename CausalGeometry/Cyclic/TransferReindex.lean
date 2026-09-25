import CausalGeometry.Cyclic.TransferDeterminant
import Mathlib.LinearAlgebra.Matrix.Reindex

namespace CausalGeometry

universe u u' v

namespace FiniteTransferSystem

variable {R : Type v} [CommRing R]
variable (T : FiniteTransferSystem.{u, v} R)

/-- Reindex a finite transfer system along an equivalence of state types.

Only the presentation changes. The transition weight between new states is the
old weight between their inverse images. -/
def reindex
    {S : Type u'}
    [Fintype S] [DecidableEq S]
    (e : T.State ≃ S) :
    FiniteTransferSystem.{u', v} R where
  State := S
  finite := inferInstance
  decEq := inferInstance
  weight i j := T.weight (e.symm i) (e.symm j)

@[simp] theorem reindex_matrix
    {S : Type u'}
    [Fintype S] [DecidableEq S]
    (e : T.State ≃ S) :
    (T.reindex e).matrix =
      Matrix.reindex e e T.matrix := by
  rfl

/-- Reindexing commutes with every matrix power. -/
theorem reindex_matrix_pow
    {S : Type u'}
    [Fintype S] [DecidableEq S]
    (e : T.State ≃ S)
    (n : ℕ) :
    (T.reindex e).matrix ^ n =
      Matrix.reindex e e (T.matrix ^ n) := by
  letI : Fintype T.State := T.finite
  letI : DecidableEq T.State := T.decEq
  change
    (Matrix.reindex e e T.matrix) ^ n =
      Matrix.reindex e e (T.matrix ^ n)
  simpa [Matrix.coe_reindexAlgEquiv] using
    (map_pow
      (Matrix.reindexAlgEquiv R R e)
      T.matrix n).symm

/-- Matrix trace is invariant under simultaneous row/column reindexing. -/
theorem trace_reindex
    {S : Type u'}
    [Fintype S] [DecidableEq S]
    (e : T.State ≃ S)
    (M : Matrix T.State T.State R) :
    Matrix.trace (Matrix.reindex e e M) =
      Matrix.trace M := by
  letI : Fintype T.State := T.finite
  letI : DecidableEq T.State := T.decEq
  unfold Matrix.trace
  simpa [Matrix.reindex_apply] using
    (Equiv.sum_comp e.symm (fun i : T.State => M i i))

/-- Every transfer trace is invariant under state relabeling. -/
theorem reindex_tracePower
    {S : Type u'}
    [Fintype S] [DecidableEq S]
    (e : T.State ≃ S)
    (n : ℕ) :
    (T.reindex e).tracePower n =
      T.tracePower n := by
  letI : Fintype T.State := T.finite
  letI : DecidableEq T.State := T.decEq
  unfold tracePower
  rw [T.reindex_matrix_pow e n]
  exact T.trace_reindex e (T.matrix ^ n)

/-- The finite determinant kernel is presentation-invariant. -/
theorem reindex_determinantKernel
    {S : Type u'}
    [Fintype S] [DecidableEq S]
    (e : T.State ≃ S)
    (u : R) :
    (T.reindex e).determinantKernel u =
      T.determinantKernel u := by
  letI : Fintype T.State := T.finite
  letI : DecidableEq T.State := T.decEq
  unfold determinantKernel
  change
    Matrix.det
        (1 - u • Matrix.reindex e e T.matrix) =
      Matrix.det (1 - u • T.matrix)
  have hmatrix :
      (1 - u • Matrix.reindex e e T.matrix) =
        Matrix.reindex e e (1 - u • T.matrix) := by
    ext i j
    simp [Matrix.reindex_apply, Matrix.one_apply]
  rw [hmatrix]
  exact Matrix.det_reindex_self e (1 - u • T.matrix)

/-- The universal determinant polynomial is invariant under state relabeling. -/
theorem reindex_determinantPolynomial
    {S : Type u'}
    [Fintype S] [DecidableEq S]
    (e : T.State ≃ S) :
    (T.reindex e).determinantPolynomial =
      T.determinantPolynomial := by
  letI : Fintype T.State := T.finite
  letI : DecidableEq T.State := T.decEq
  unfold determinantPolynomial
  change
    Matrix.det
        (1 -
          (Polynomial.X : R[X]) •
            (Matrix.reindex e e T.matrix).map Polynomial.C) =
      Matrix.det
        (1 -
          (Polynomial.X : R[X]) •
            T.matrix.map Polynomial.C)
  have hmap :
      (Matrix.reindex e e T.matrix).map Polynomial.C =
        Matrix.reindex e e (T.matrix.map Polynomial.C) := by
    ext i j
    rfl
  rw [hmap]
  have hmatrix :
      (1 -
          (Polynomial.X : R[X]) •
            Matrix.reindex e e (T.matrix.map Polynomial.C)) =
        Matrix.reindex e e
          (1 -
            (Polynomial.X : R[X]) •
              T.matrix.map Polynomial.C) := by
    ext i j
    simp [Matrix.reindex_apply, Matrix.one_apply]
  rw [hmatrix]
  exact
    Matrix.det_reindex_self e
      (1 -
        (Polynomial.X : R[X]) •
          T.matrix.map Polynomial.C)

/-- The complete finite transfer observable is independent of the chosen
state labels. -/
theorem reindex_traceSequence
    {S : Type u'}
    [Fintype S] [DecidableEq S]
    (e : T.State ≃ S) :
    (T.reindex e).traceSequence =
      T.traceSequence := by
  funext n
  exact T.reindex_tracePower e n

end FiniteTransferSystem
end CausalGeometry
