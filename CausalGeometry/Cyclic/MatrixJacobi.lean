import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.RingTheory.MatrixPolynomialAlgebra
import Mathlib.Tactic

namespace CausalGeometry

open Finset Polynomial

universe u

namespace Matrix

variable
    {n : Type u}
    [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R]

/-- The coefficient linear in X of det(A + X B) is obtained by replacing
exactly one row of A by the corresponding row of B. -/
theorem coeff_det_add_X_smul_one_general
    (A B : Matrix n n R) :
    (det
      (A.map C +
        (X : R[X]) • B.map C)).coeff 1 =
      ∑ i : n,
        det (A.updateRow i (B i)) := by
  simp only [det]
  let D :=
    (detRowAlternating :
      (n → R[X]) [⋀^n]→ₗ[R[X]] R[X])
  change
    (D
      (fun i =>
        (A.map C) i +
          ((X : R[X]) • B.map C) i)).coeff 1 =
      _
  rw [add_comm]
  change
    (D
      (fun i =>
        ((X : R[X]) • B.map C) i +
          (A.map C) i)).coeff 1 =
      _
  conv_lhs =>
    rw [show
      (fun i =>
        ((X : R[X]) • B.map C) i +
          (A.map C) i) =
        (fun i =>
          ((X : R[X]) • B.map C) i) +
        (fun i => (A.map C) i) from rfl]
  conv_lhs => rw [D.map_add_univ]

  have h_map :
      ∀ s : Finset n,
        (s.piecewise
          (fun i => (B.map C) i)
          (fun i => (A.map C) i) :
          Matrix n n R[X]) =
        Matrix.map
          (s.piecewise B A) C := by
    intro s
    ext i j
    simp only [Finset.piecewise,
      Matrix.map_apply]
    split_ifs <;> rfl

  have h_det :
      ∀ s : Finset n,
        D
          (s.piecewise
            (fun i => (B.map C) i)
            (fun i => (A.map C) i)) =
          C (det (s.piecewise B A)) := by
    intro s
    change det _ = _
    rw [h_map]
    exact (RingHom.map_det C _).symm

  calc
    (∑ s : Finset n,
      D
        (s.piecewise
          (fun i =>
            ((X : R[X]) • B.map C) i)
          (fun i =>
            (A.map C) i))).coeff 1
        =
      (∑ s : Finset n,
        (X : R[X]) ^ s.card •
          D
            (s.piecewise
              (fun i => (B.map C) i)
              (fun i => (A.map C) i))).coeff 1 := by
          congr 2 with s
          have h_smul :
              s.piecewise
                  (fun i =>
                    ((X : R[X]) •
                      B.map C) i)
                  (fun i =>
                    (A.map C) i)
                =
              fun i =>
                (if i ∈ s
                  then (X : R[X])
                  else 1) •
                  s.piecewise
                    (fun i => (B.map C) i)
                    (fun i => (A.map C) i) i := by
            funext i j
            simp only [
              Finset.piecewise,
              Matrix.smul_apply,
              Pi.smul_apply,
              smul_eq_mul,
              ite_mul,
              one_mul
            ]
            split_ifs <;> rfl
          rw [h_smul, D.map_smul_univ]
          congr 1
          simp only [
            Finset.prod_ite_mem,
            Finset.univ_inter,
            Finset.prod_const
          ]
    _ =
      ∑ s : Finset n,
        ((X : R[X]) ^ s.card *
          C (det (s.piecewise B A))).coeff 1 := by
          congr 1
          apply Finset.sum_congr rfl
          intro s hs
          rw [h_det]
          rfl
    _ =
      ∑ s ∈
        (Finset.univ : Finset (Finset n)).powersetCard 1,
          det (s.piecewise B A) := by
          simp_rw [
            mul_comm (X ^ _) (C _),
            C_mul_X_pow_eq_monomial,
            coeff_monomial
          ]
          rw [← Finset.sum_filter]
          have h_set :
              (Finset.univ :
                Finset (Finset n)).filter
                  (fun s => s.card = 1)
                =
              (Finset.univ :
                Finset (Finset n)).powersetCard 1 := by
            ext s
            simp [Finset.mem_powersetCard]
          rw [h_set]
          apply Finset.sum_congr rfl
          intro s hs
          simp [Finset.mem_powersetCard] at hs
    _ =
      ∑ i : n,
        det (A.updateRow i (B i)) := by
          rw [Finset.powersetCard_one,
            Finset.sum_map]
          simp only [
            Function.Embedding.coeFn_mk,
            Finset.mem_univ,
            forall_const
          ]
          apply Finset.sum_congr rfl
          intro i hi
          congr 1
          ext r c
          by_cases hri : r = i
          · subst r
            simp [
              Matrix.updateRow_apply,
              Finset.piecewise
            ]
          · simp [
              Matrix.updateRow_apply,
              Finset.piecewise,
              hri
            ]

/-- Replacing one row is linear in the replacement row. -/
theorem det_updateRow_eq_sum_adjugate
    (A B : Matrix n n R)
    (i : n) :
    det (A.updateRow i (B i)) =
      ∑ j : n,
        B i j * adjugate A j i := by
  let L :
      (n → R) →ₗ[R] R :=
    ((detRowAlternating :
        (n → R) [⋀^n]→ₗ[R] R).toMultilinearMap
      .toLinearMap A i)

  have hL :
      ∀ v : n → R,
        L v =
          det (A.updateRow i v) := by
    intro v
    rfl

  calc
    det (A.updateRow i (B i))
        = L (B i) := by
            rw [hL]
    _ =
      L
        (∑ j : n,
          (B i j) •
            Pi.single
              (M := fun _ => R)
              j 1) := by
            rw [pi_eq_sum_univ']
    _ =
      ∑ j : n,
        L
          ((B i j) •
            Pi.single
              (M := fun _ => R)
              j 1) := by
            rw [map_sum]
    _ =
      ∑ j : n,
        B i j *
          L
            (Pi.single
              (M := fun _ => R)
              j 1) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [map_smul]
            rfl
    _ =
      ∑ j : n,
        B i j * adjugate A j i := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hL]
            rw [adjugate_apply]

/-- Jacobi directional coefficient formula, with no invertibility
assumption on A. -/
theorem coeff_det_add_X_smul_one_eq_adjugate
    (A B : Matrix n n R) :
    (det
      (A.map C +
        (X : R[X]) • B.map C)).coeff 1 =
      ∑ i : n, ∑ j : n,
        B i j * adjugate A j i := by
  rw [coeff_det_add_X_smul_one_general]
  apply Finset.sum_congr rfl
  intro i hi
  exact det_updateRow_eq_sum_adjugate
    A B i

/-- The same contraction is the trace of B * adj(A). -/
theorem coeff_det_add_X_smul_one_eq_trace_mul_adjugate
    (A B : Matrix n n R) :
    (det
      (A.map C +
        (X : R[X]) • B.map C)).coeff 1 =
      trace (B * adjugate A) := by
  rw [coeff_det_add_X_smul_one_eq_adjugate]
  unfold trace
  simp only [diag_apply, mul_apply]
  rw [Finset.sum_comm]

end Matrix
end CausalGeometry
