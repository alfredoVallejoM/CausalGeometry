import CausalGeometry.Calculus.CubicalTwoFormBridge
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalCubicalCochain

variable {K : Type w} [Field K]

/-- Exterior differential in degree zero.

Degree-one alternation is vacuous, so the raw cubical differential lands
canonically in the exterior submodule. -/
def exteriorDifferential0 :
    CausalExteriorCochain
        (S := S) (K := K) 0
      →ₗ[K]
    CausalExteriorCochain
        (S := S) (K := K) 1 where

  toFun := fun ω =>
    ⟨differential (S := S) (K := K) 0 ω.1,
      alternating_one _⟩

  map_add' := by
    intro α β
    apply Subtype.ext
    simp

  map_smul' := by
    intro a α
    apply Subtype.ext
    simp

@[simp] theorem exteriorDifferential0_val
    (ω :
      CausalExteriorCochain
        (S := S) (K := K) 0) :
    ((exteriorDifferential0
        (S := S) (K := K) ω :
      CausalExteriorCochain
        (S := S) (K := K) 1) :
      CausalCubicalCochain S K 1)
      =
    differential (S := S) (K := K) 0 ω.1 :=
  rfl

/-- Legacy one-form represented by one exterior cubical degree-one cochain. -/
def exteriorOneToOneForm
    (ω :
      CausalExteriorCochain
        (S := S) (K := K) 1) :
    CausalOneForm S K :=
  (degreeOneLinearEquiv
    (S := S) (K := K)).symm ω.1

/-- Exterior differential in degree one.

Rather than reproving skewness from scratch, we use the already established
legacy exterior derivative and the proved equivalence between legacy
two-forms and alternating cubical degree two. -/
def exteriorDifferential1 :
    CausalExteriorCochain
        (S := S) (K := K) 1
      →ₗ[K]
    CausalExteriorCochain
        (S := S) (K := K) 2 where

  toFun := fun ω =>
    twoFormToExterior
      (CausalTwoForm.ofExteriorDerivative
        (exteriorOneToOneForm ω))

  map_add' := by
    intro α β
    apply Subtype.ext
    funext Q
    rfl

  map_smul' := by
    intro a α
    apply Subtype.ext
    funext Q
    simp [twoFormToExterior,
      twoFormToCubical,
      exteriorOneToOneForm,
      CausalTwoForm.ofExteriorDerivative,
      CausalOneForm.exteriorDerivative,
      CausalOneForm.variationEF,
      CausalOneForm.variationFE]
    module

/-- The degree-one exterior differential has exactly the same underlying raw
cochain as the arbitrary-degree cubical differential. -/
theorem exteriorDifferential1_val
    (ω :
      CausalExteriorCochain
        (S := S) (K := K) 1) :
    ((exteriorDifferential1
        (S := S) (K := K) ω :
      CausalExteriorCochain
        (S := S) (K := K) 2) :
      CausalCubicalCochain S K 2)
      =
    differential (S := S) (K := K) 1 ω.1 := by

  let η : CausalOneForm S K :=
    exteriorOneToOneForm ω

  have hη :
      degreeOneLinearEquiv
          (S := S) (K := K) η
        =
      ω.1 := by
    simp [η, exteriorOneToOneForm]

  rw [← hη]
  rw [differential_one_eq_d1Linear]

  funext Q
  rfl

/-- Low-degree exterior square-zero theorem. -/
theorem exteriorDifferential1_exteriorDifferential0
    (ω :
      CausalExteriorCochain
        (S := S) (K := K) 0) :
    exteriorDifferential1
        (S := S) (K := K)
        (exteriorDifferential0
          (S := S) (K := K) ω)
      =
    0 := by
  apply Subtype.ext
  rw [exteriorDifferential1_val]
  change
    differential (S := S) (K := K) 1
        (differential (S := S) (K := K) 0 ω.1)
      =
    0
  exact
    differential_squared
      (S := S) (K := K) 0 ω.1

/-- The first three exterior degrees therefore form a genuine linear cochain
complex. -/
def exteriorLowComplex :
    CausalCochainComplex
      K
      (CausalExteriorCochain
        (S := S) (K := K) 0)
      (CausalExteriorCochain
        (S := S) (K := K) 1)
      (CausalExteriorCochain
        (S := S) (K := K) 2) where

  d0 :=
    exteriorDifferential0

  d1 :=
    exteriorDifferential1

  d_sq := by
    apply LinearMap.ext
    intro ω
    exact
      exteriorDifferential1_exteriorDifferential0
        (S := S) (K := K) ω

end CausalCubicalCochain
end CausalGeometry
