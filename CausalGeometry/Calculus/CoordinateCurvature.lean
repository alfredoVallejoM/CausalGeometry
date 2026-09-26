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

/-- Evaluation of the unique component of a rank-(0,0) coordinate tensor. -/
def scalarValueLinear :
    CoordinateTensor K ι 0 0 →ₗ[K] K where
  toFun := fun T =>
    T (fun i => Fin.elim0 i)
      (fun i => Fin.elim0 i)
  map_add' := by
    intro T U
    rfl
  map_smul' := by
    intro a T
    rfl

/-- For a fixed inverse metric gInv, scalar curvature is the linear composite

R
  -> Ric(R)                    : (0,2)
  -> gInv tensor Ric(R)        : (2,2)
  -> one contraction           : (1,1)
  -> second contraction        : (0,0)
  -> scalar.

The slot convention is therefore explicit and stable. -/
def scalarCurvatureLinear
    (gInv : CoordinateTensor K ι 2 0) :
    Curvature (K := K) (ι := ι) →ₗ[K] K :=
  scalarValueLinear.comp
    ((contract 0 0).comp
      ((contract 1 1).comp
        ((tensor 2 0 0 2 gInv).comp
          ricci)))

/-- Coordinate scalar curvature g^{ab} Ric_ab in the selected slot
convention. -/
def scalarCurvature
    (gInv : CoordinateTensor K ι 2 0)
    (R : Curvature (K := K) (ι := ι)) : K :=
  scalarCurvatureLinear gInv R

@[simp] theorem scalarCurvature_apply
    (gInv : CoordinateTensor K ι 2 0)
    (R : Curvature (K := K) (ι := ι)) :
    scalarCurvature gInv R =
      scalarCurvatureLinear gInv R :=
  rfl

/-- Ricci is linear in curvature. -/
theorem ricci_add
    (R T : Curvature (K := K) (ι := ι)) :
    ricci (R + T) =
      ricci R + ricci T :=
  map_add _ _ _

/-- Scalar curvature is linear in curvature for fixed inverse metric. -/
theorem scalarCurvature_add
    (gInv : CoordinateTensor K ι 2 0)
    (R T : Curvature (K := K) (ι := ι)) :
    scalarCurvature gInv (R + T) =
      scalarCurvature gInv R +
        scalarCurvature gInv T :=
  map_add (scalarCurvatureLinear gInv) R T

/-- Scalar curvature scales linearly with the curvature tensor for fixed
inverse metric. -/
theorem scalarCurvature_smul
    (gInv : CoordinateTensor K ι 2 0)
    (a : K)
    (R : Curvature (K := K) (ι := ι)) :
    scalarCurvature gInv (a • R) =
      a • scalarCurvature gInv R :=
  map_smul (scalarCurvatureLinear gInv) a R

end CoordinateTensor
end CausalGeometry
