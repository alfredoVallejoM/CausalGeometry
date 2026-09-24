import CausalGeometry.Number.LeftFractionCalculus
import CausalGeometry.Number.RightFractionCalculus

namespace CausalGeometry.Models

open CausalGeometry.CausalLocalization

universe u

variable {G : Type u} [Group G]

/-- Evaluation relation for right fractions over a group, taking every group
element as an allowed denominator. -/
def rightGroupRel
    (x y : RightFraction (⊤ : Submonoid G)) : Prop :=
  RightFraction.realize (MonoidHom.id G) x =
    RightFraction.realize (MonoidHom.id G) y

theorem rightGroupRel_equivalence :
    Equivalence (rightGroupRel (G := G)) := by
  constructor
  · intro x
    rfl
  · intro x y h
    exact h.symm
  · intro x y z hxy hyz
    exact hxy.trans hyz

/-- Canonical representative product: evaluate both right fractions in the
group and return the product with denominator one. -/
def rightGroupMulRep
    (x y : RightFraction (⊤ : Submonoid G)) :
    RightFraction (⊤ : Submonoid G) :=
  RightFraction.ofElement
    (RightFraction.realize (MonoidHom.id G) x *
      RightFraction.realize (MonoidHom.id G) y)

/-- A group automatically supplies the right Ore square required to move a
denominator across the next numerator. -/
def rightGroupOreSquare
    (a : G) (s : (⊤ : Submonoid G)) :
    RightOreSquare (⊤ : Submonoid G) a s where
  numerator := (s : G)⁻¹ * a
  denominator := ⟨1, by simp⟩
  cross := by
    simp [mul_assoc]

/-- Every group is a positive model of the certified right-fraction calculus. -/
def rightGroupCalculus :
    RightFractionCalculus (⊤ : Submonoid G) where
  rel := rightGroupRel
  rel_equivalence := rightGroupRel_equivalence
  mulRep := rightGroupMulRep

  mul_from_ore := by
    intro x y
    let w := rightGroupOreSquare y.numerator x.denominator
    refine ⟨w, ?_⟩
    unfold rightGroupRel rightGroupMulRep
    simp [RightFraction.realize, RightFraction.mulWith,
      w, mul_assoc]

  mul_respects := by
    intro x x' y y' hx hy
    unfold rightGroupRel rightGroupMulRep at hx hy ⊢
    simp [RightFraction.realize, hx, hy]

  mul_assoc := by
    intro x y z
    unfold rightGroupRel rightGroupMulRep
    simp [RightFraction.realize, mul_assoc]

  one_mul := by
    intro x
    unfold rightGroupRel rightGroupMulRep
    simp [RightFraction.realize]

  mul_one := by
    intro x
    unfold rightGroupRel rightGroupMulRep
    simp [RightFraction.realize]

  source_mul := by
    intro a b
    unfold rightGroupRel rightGroupMulRep
    simp [RightFraction.realize]

  denominator_right_inverse := by
    intro s
    unfold rightGroupRel rightGroupMulRep
    simp [RightFraction.realize]

  denominator_left_inverse := by
    intro s
    unfold rightGroupRel rightGroupMulRep
    simp [RightFraction.realize]

  normalForm := by
    intro x
    unfold rightGroupRel rightGroupMulRep
    simp [RightFraction.realize, mul_assoc]

/-- Evaluation relation for left fractions over a group. -/
def leftGroupRel
    (x y : LeftFraction (⊤ : Submonoid G)) : Prop :=
  LeftFraction.realize (MonoidHom.id G) x =
    LeftFraction.realize (MonoidHom.id G) y

theorem leftGroupRel_equivalence :
    Equivalence (leftGroupRel (G := G)) := by
  constructor
  · intro x
    rfl
  · intro x y h
    exact h.symm
  · intro x y z hxy hyz
    exact hxy.trans hyz

def leftGroupMulRep
    (x y : LeftFraction (⊤ : Submonoid G)) :
    LeftFraction (⊤ : Submonoid G) :=
  LeftFraction.ofElement
    (LeftFraction.realize (MonoidHom.id G) x *
      LeftFraction.realize (MonoidHom.id G) y)

/-- Group form of the left Ore square. -/
def leftGroupOreSquare
    (a : G) (s : (⊤ : Submonoid G)) :
    LeftOreSquare (⊤ : Submonoid G) a s where
  numerator := a * (s : G)⁻¹
  denominator := ⟨1, by simp⟩
  cross := by
    simp [mul_assoc]

/-- Every group is also a positive model of the left-fraction calculus. -/
def leftGroupCalculus :
    LeftFractionCalculus (⊤ : Submonoid G) where
  rel := leftGroupRel
  rel_equivalence := leftGroupRel_equivalence
  mulRep := leftGroupMulRep

  mul_from_ore := by
    intro x y
    let w := leftGroupOreSquare x.numerator y.denominator
    refine ⟨w, ?_⟩
    unfold leftGroupRel leftGroupMulRep
    simp [LeftFraction.realize, LeftFraction.mulWith,
      w, mul_assoc]

  mul_respects := by
    intro x x' y y' hx hy
    unfold leftGroupRel leftGroupMulRep at hx hy ⊢
    simp [LeftFraction.realize, hx, hy]

  mul_assoc := by
    intro x y z
    unfold leftGroupRel leftGroupMulRep
    simp [LeftFraction.realize, mul_assoc]

  one_mul := by
    intro x
    unfold leftGroupRel leftGroupMulRep
    simp [LeftFraction.realize]

  mul_one := by
    intro x
    unfold leftGroupRel leftGroupMulRep
    simp [LeftFraction.realize]

  source_mul := by
    intro a b
    unfold leftGroupRel leftGroupMulRep
    simp [LeftFraction.realize]

  denominator_right_inverse := by
    intro s
    unfold leftGroupRel leftGroupMulRep
    simp [LeftFraction.realize]

  denominator_left_inverse := by
    intro s
    unfold leftGroupRel leftGroupMulRep
    simp [LeftFraction.realize]

  normalForm := by
    intro x
    unfold leftGroupRel leftGroupMulRep
    simp [LeftFraction.realize, mul_assoc]

end CausalGeometry.Models
