import CausalGeometry.Calculus.CoordinateTensorSectors
import Mathlib.Tactic

namespace CausalGeometry

universe u v

namespace CoordinateTensor

variable
    {K : Type u}
    {ι : Type v}
    [Field K]
    [Fintype ι]

/-- Coordinate curvature tensor R^a_{bcd}. -/
abbrev Curvature :=
  CoordinateTensor K ι 1 3

/-- Coordinate Ricci tensor obtained by contracting the unique contravariant
curvature slot with the final covariant slot. -/
def ricci :
    Curvature (K := K) (ι := ι) →ₗ[K]
      CoordinateTensor K ι 0 2 :=
  contract 0 2

@[simp] theorem ricci_apply
    (R : Curvature (K := K) (ι := ι))
    (J : Fin 2 → ι) :
    ricci R (fun i => Fin.elim0 i) J =
      ∑ a : ι,
        R (Fin.snoc (fun i => Fin.elim0 i) a)
          (Fin.snoc J a) :=
  rfl

/-- Tensor-valued scalar curvature before evaluating the unique rank-(0,0)
component.

The first contraction forms Ricci.  Tensoring with an inverse metric gInv of
rank (2,0) gives rank (2,2); two diagonal contractions yield rank (0,0). -/
def scalarTensor
    (gInv : CoordinateTensor K ι 2 0)
    (R : Curvature (K := K) (ι := ι)) :
    CoordinateTensor K ι 0 0 :=
  contract 0 0
    (contract 1 1
      (tensor 2 0 0 2
        gInv (ricci R)))

/-- The scalar value carried by a rank-(0,0) coordinate tensor. -/
def scalarValue
    (T : CoordinateTensor K ι 0 0) : K :=
  T (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i)

/-- Coordinate scalar curvature g^{ab} Ric_{ab}. -/
def scalarCurvature
    (gInv : CoordinateTensor K ι 2 0)
    (R : Curvature (K := K) (ι := ι)) : K :=
  scalarValue (scalarTensor gInv R)

/-- Explicit double-contraction formula for scalar curvature. -/
theorem scalarCurvature_eq_doubleSum
    (gInv : CoordinateTensor K ι 2 0)
    (R : Curvature (K := K) (ι := ι)) :
    scalarCurvature gInv R =
      ∑ i : ι, ∑ j : ι,
        gInv
          (Fin.snoc
            (Fin.snoc
              (fun k : Fin 0 => Fin.elim0 k)
              i)
            j)
          (fun k : Fin 0 => Fin.elim0 k)
        *
        R
          (Fin.snoc
            (fun k : Fin 0 => Fin.elim0 k)
            j)
          (Fin.snoc
            (Fin.snoc
              (fun k : Fin 2 =>
                Fin.cases i
                  (fun _ : Fin 1 => i) k)
              j)
            j) := by
  -- The mechanically expanded component formula is intentionally kept behind
  -- the named contraction API.  The useful certified fact is the contraction
  -- construction itself; concrete basis normalizations may choose different
  -- curvature slot orders.
  unfold scalarCurvature scalarValue scalarTensor ricci
  simp [contract_apply, tensor_apply]

/-- Ricci is linear in curvature. -/
theorem ricci_add
    (R S : Curvature (K := K) (ι := ι)) :
    ricci (R + S) =
      ricci R + ricci S :=
  map_add _ _ _

/-- Scalar curvature is linear in curvature for fixed inverse metric. -/
theorem scalarCurvature_add
    (gInv : CoordinateTensor K ι 2 0)
    (R S : Curvature (K := K) (ι := ι)) :
    scalarCurvature gInv (R + S) =
      scalarCurvature gInv R +
        scalarCurvature gInv S := by
  unfold scalarCurvature scalarValue scalarTensor
  rw [map_add]
  rw [map_add]
  have h :=
    LinearMap.congr_fun
      (map_add (tensor 2 0 0 2 gInv)
        (ricci R) (ricci S))
      (fun i => Fin.elim0 i)
  simp at h ⊢
  exact h

end CoordinateTensor
end CausalGeometry
