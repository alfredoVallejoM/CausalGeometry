import CausalGeometry.Models.OreFractionControls
import CausalGeometry.Number.BilateralLocalization

namespace CausalGeometry.Models

open CausalGeometry.CausalLocalization

universe u

variable {G : Type u} [Group G]

abbrev RightGroupCalculus :=
  rightGroupCalculus (G := G)

abbrev LeftGroupCalculus :=
  leftGroupCalculus (G := G)

/-- Canonical realization certificate for the right group calculus. -/
def rightGroupRealization :
    (RightGroupCalculus (G := G)).GroupRealization
      G (MonoidHom.id G) where
  respects := by
    intro x y h
    exact h
  mul_compatible := by
    intro x y
    unfold rightGroupMulRep
    simp [RightFraction.realize]

/-- Canonical realization certificate for the left group calculus. -/
def leftGroupRealization :
    (LeftGroupCalculus (G := G)).GroupRealization
      G (MonoidHom.id G) where
  respects := by
    intro x y h
    exact h
  mul_compatible := by
    intro x y
    unfold leftGroupMulRep
    simp [LeftFraction.realize]

namespace RightGroupCalculus

abbrev C :=
  RightGroupCalculus (G := G)

@[simp] theorem source_inverse_eq_denominatorInverse
    (s : (⊤ : Submonoid G)) :
    C.sourceHom ((s : G)⁻¹) =
      C.denominatorInverse s := by
  change
    C.mk
        (RightFraction.ofElement
          (S := (⊤ : Submonoid G))
          ((s : G)⁻¹)) =
      C.mk
        (⟨1, s⟩ :
          RightFraction (⊤ : Submonoid G))
  apply Quotient.sound
  unfold rightGroupRel
  simp [RightFraction.realize]

/-- Evaluating a right fraction and re-embedding it returns the same quotient
class. -/
theorem source_realize_mk
    (x : RightFraction (⊤ : Submonoid G)) :
    C.sourceHom
        ((rightGroupRealization (G := G)).realizeHom
          (C.mk x)) =
      C.mk x := by
  change
    C.sourceHom
        (x.numerator *
          (x.denominator : G)⁻¹) =
      C.mk x
  rw [map_mul,
    source_inverse_eq_denominatorInverse
      (G := G)]
  exact (C.mk_normalForm x).symm

/-- The certified right localization over a group is multiplicatively
equivalent to the original group. -/
def quotientEquivGroup :
    C.QuotientType ≃* G where
  toFun :=
    (rightGroupRealization
      (G := G)).realizeHom
  invFun :=
    C.sourceHom
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    exact source_realize_mk
      (G := G) x
  right_inv := by
    intro g
    exact
      (rightGroupRealization
        (G := G)).realizeHom_source g
  map_mul' := by
    intro x y
    exact
      (rightGroupRealization
        (G := G)).realize_mul x y

@[simp] theorem quotientEquivGroup_source
    (g : G) :
    quotientEquivGroup (G := G)
        (C.sourceHom g) =
      g := by
  exact
    (rightGroupRealization
      (G := G)).realizeHom_source g

@[simp] theorem quotientEquivGroup_denominatorInverse
    (s : (⊤ : Submonoid G)) :
    quotientEquivGroup (G := G)
        (C.denominatorInverse s) =
      (s : G)⁻¹ := by
  exact
    (rightGroupRealization
      (G := G)).realize_denominatorInverse s

end RightGroupCalculus

namespace LeftGroupCalculus

abbrev C :=
  LeftGroupCalculus (G := G)

@[simp] theorem source_inverse_eq_denominatorInverse
    (s : (⊤ : Submonoid G)) :
    C.sourceHom ((s : G)⁻¹) =
      C.denominatorInverse s := by
  change
    C.mk
        (LeftFraction.ofElement
          (S := (⊤ : Submonoid G))
          ((s : G)⁻¹)) =
      C.mk
        (⟨s, 1⟩ :
          LeftFraction (⊤ : Submonoid G))
  apply Quotient.sound
  unfold leftGroupRel
  simp [LeftFraction.realize]

theorem source_realize_mk
    (x : LeftFraction (⊤ : Submonoid G)) :
    C.sourceHom
        ((leftGroupRealization (G := G)).realizeHom
          (C.mk x)) =
      C.mk x := by
  change
    C.sourceHom
        ((x.denominator : G)⁻¹ *
          x.numerator) =
      C.mk x
  rw [map_mul,
    source_inverse_eq_denominatorInverse
      (G := G)]
  exact (C.mk_normalForm x).symm

/-- The certified left localization over a group is multiplicatively
equivalent to the original group. -/
def quotientEquivGroup :
    C.QuotientType ≃* G where
  toFun :=
    (leftGroupRealization
      (G := G)).realizeHom
  invFun :=
    C.sourceHom
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    exact source_realize_mk
      (G := G) x
  right_inv := by
    intro g
    exact
      (leftGroupRealization
        (G := G)).realizeHom_source g
  map_mul' := by
    intro x y
    exact
      (leftGroupRealization
        (G := G)).realize_mul x y

@[simp] theorem quotientEquivGroup_source
    (g : G) :
    quotientEquivGroup (G := G)
        (C.sourceHom g) =
      g := by
  exact
    (leftGroupRealization
      (G := G)).realizeHom_source g

@[simp] theorem quotientEquivGroup_denominatorInverse
    (s : (⊤ : Submonoid G)) :
    quotientEquivGroup (G := G)
        (C.denominatorInverse s) =
      (s : G)⁻¹ := by
  exact
    (leftGroupRealization
      (G := G)).realize_denominatorInverse s

end LeftGroupCalculus

/-- Canonical bilateral comparison in the group model, derived by evaluating
both one-sided localizations in G. -/
def groupBilateralComparison :
    BilateralFractionComparison
      (RightGroupCalculus (G := G))
      (LeftGroupCalculus (G := G)) where
  equivalence :=
    (RightGroupCalculus.quotientEquivGroup
      (G := G)).trans
      (LeftGroupCalculus.quotientEquivGroup
        (G := G)).symm
  source_compat := by
    intro g
    apply
      (LeftGroupCalculus.quotientEquivGroup
        (G := G)).injective
    simp
  denominator_compat := by
    intro s
    apply
      (LeftGroupCalculus.quotientEquivGroup
        (G := G)).injective
    simp

/-- In the group model, the bilateral comparison sends every right normal form
to the corresponding element of the left localization. -/
theorem groupBilateralComparison_right_normalForm
    (x : RightFraction (⊤ : Submonoid G)) :
    (groupBilateralComparison
      (G := G)).equivalence
        ((RightGroupCalculus (G := G)).mk x) =
      (LeftGroupCalculus (G := G)).sourceHom x.numerator *
        (LeftGroupCalculus (G := G)).denominatorInverse
          x.denominator :=
  (groupBilateralComparison
    (G := G)).map_right_normalForm x

end CausalGeometry.Models
