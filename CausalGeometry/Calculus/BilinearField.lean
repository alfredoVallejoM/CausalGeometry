import CausalGeometry.Calculus.DependentLinearConnection

namespace CausalGeometry

universe u v w x
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalBilinear

variable {K : Type w}
variable {Fiber : Configuration S → Type x}
variable [CommRing K]
variable [∀ C, AddCommGroup (Fiber C)]
variable [∀ C, Module K (Fiber C)]

/-- Configuration-dependent bilinear form field.

No symmetry, alternation, nondegeneracy or positivity is bundled into the
carrier. -/
structure Field where
  form :
    ∀ C : Configuration S,
      Fiber C →ₗ[K] Fiber C →ₗ[K] K

namespace Field

variable (B : Field (K := K) (S := S) (Fiber := Fiber))

def Symmetric : Prop :=
  ∀ C x y,
    B.form C x y =
      B.form C y x

def Alternating : Prop :=
  ∀ C x,
    B.form C x x = 0

/-- Alternation forces skew-symmetry without any characteristic assumption. -/
theorem skew_of_alternating
    (halt : B.Alternating)
    (C : Configuration S)
    (x y : Fiber C) :
    B.form C y x =
      - B.form C x y := by
  have hsum := halt C (x + y)
  have hx := halt C x
  have hy := halt C y
  simp only [map_add] at hsum
  rw [hx, hy] at hsum
  abel

def LeftNondegenerate : Prop :=
  ∀ C x,
    (∀ y, B.form C x y = 0) →
      x = 0

/-- The bilinear field canonically maps vectors to covectors. This is the
flat/musical map, but it is not assumed invertible. -/
def flat
    (C : Configuration S) :
    Fiber C →ₗ[K] Module.Dual K (Fiber C) :=
  B.form C

@[simp] theorem flat_apply
    (C : Configuration S)
    (x y : Fiber C) :
    B.flat C x y =
      B.form C x y :=
  rfl

theorem flat_injective
    (hnd : B.LeftNondegenerate)
    (C : Configuration S) :
    Function.Injective (B.flat C) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply hnd C (x - y)
  intro z
  have hz :=
    LinearMap.congr_fun hxy z
  simpa using
    sub_eq_zero.mpr hz

/-- A dependent connection preserves B when event transport preserves its
pairing exactly. -/
def PreservedBy
    (∇ : DependentLinearCausalConnection K S Fiber) : Prop :=
  ∀ C e h x y,
    B.form (S.extend C e h)
        (∇.transport C e h x)
        (∇.transport C e h y) =
      B.form C x y

/-- Preserving a left-nondegenerate form forces every primitive vector
transport to be injective, even though invertibility is not assumed by the
connection carrier. -/
theorem transport_injective_of_preserved
    (∇ : DependentLinearCausalConnection K S Fiber)
    (hnd : B.LeftNondegenerate)
    (hpres : B.PreservedBy ∇)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    Function.Injective
      (∇.transport C e h) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply hnd C (x - y)
  intro z
  have hzero :
      ∇.transport C e h (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
    exact map_zero _
  calc
    B.form C (x - y) z
        =
      B.form (S.extend C e h)
        (∇.transport C e h (x - y))
        (∇.transport C e h z) := by
          symm
          exact hpres C e h (x - y) z
    _ = 0 := by
      rw [hzero]
      simp

end Field

/-- Optional inverse to the flat map.

This is intentionally separate from nondegeneracy: over arbitrary modules,
injectivity of flat does not imply a global inverse. -/
structure MusicalBridge
    (B : Field (K := K) (S := S) (Fiber := Fiber)) where
  sharp :
    ∀ C : Configuration S,
      Module.Dual K (Fiber C) →ₗ[K] Fiber C

  sharp_flat :
    ∀ C x,
      sharp C (B.flat C x) = x

  flat_sharp :
    ∀ C ω,
      B.flat C (sharp C ω) = ω

namespace MusicalBridge

variable
    {B : Field (K := K) (S := S) (Fiber := Fiber)}
    (M : MusicalBridge B)

/-- Every explicit musical bridge packages a true vector/covector linear
equivalence. -/
def equiv
    (C : Configuration S) :
    Fiber C ≃ₗ[K]
      Module.Dual K (Fiber C) where
  toFun := B.flat C
  invFun := M.sharp C
  left_inv := M.sharp_flat C
  right_inv := M.flat_sharp C
  map_add' := by
    intro x y
    exact map_add (B.flat C) x y
  map_smul' := by
    intro a x
    exact map_smul (B.flat C) a x

@[simp] theorem equiv_apply
    (C : Configuration S)
    (x : Fiber C) :
    M.equiv C x =
      B.flat C x :=
  rfl

@[simp] theorem equiv_symm_apply
    (C : Configuration S)
    (ω : Module.Dual K (Fiber C)) :
    (M.equiv C).symm ω =
      M.sharp C ω :=
  rfl

end MusicalBridge

/-- Alternating, left-nondegenerate bilinear field. This is the algebraic
symplectic layer; closedness of a differential form is a separate obligation. -/
structure SymplecticField extends
    Field (K := K) (S := S) (Fiber := Fiber) where
  alternating :
    toField.Alternating
  nondegenerate :
    toField.LeftNondegenerate

/-- Symmetric, left-nondegenerate bilinear field. Positivity/signature is not
assumed. -/
structure SymmetricField extends
    Field (K := K) (S := S) (Fiber := Fiber) where
  symmetric :
    toField.Symmetric
  nondegenerate :
    toField.LeftNondegenerate

end CausalBilinear
end CausalGeometry
