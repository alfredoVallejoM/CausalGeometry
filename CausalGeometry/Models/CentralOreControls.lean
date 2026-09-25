import CausalGeometry.Number.CentralBilateralLocalization

namespace CausalGeometry.Models

open CausalGeometry.CausalLocalization

universe u v

variable
    {G : Type u} [Group G]
    {C : Type v} [CommGroup C]

/-- Central second-factor denominators inside G×C.

The first factor G is unrestricted and may be noncommutative. -/
def secondFactorDenominators :
    Submonoid (G × C) where
  carrier := {x | x.1 = 1}
  one_mem' := rfl
  mul_mem' := by
    intro a b ha hb
    simp [ha, hb]

theorem secondFactorDenominators_central :
    CentralDenominators
      (secondFactorDenominators
        (G := G) (C := C)) := by
  intro s a
  rcases s with ⟨⟨g, c⟩, hg⟩
  rcases a with ⟨h, d⟩
  change
    (g * h, c * d) =
      (h * g, d * c)
  simp only at hg
  rw [hg]
  simp [mul_comm]

/-- The second-factor system satisfies both Ore conditions even when G itself
is noncommutative. -/
theorem secondFactor_bilateralOre :
    RightOreCondition
        (secondFactorDenominators
          (G := G) (C := C)) ∧
      LeftOreCondition
        (secondFactorDenominators
          (G := G) (C := C)) :=
  (secondFactorDenominators_central
    (G := G) (C := C)).bilateralOre

/-- Full certified bilateral fraction comparison for second-factor
localization. -/
def secondFactorBilateralComparison :
    BilateralFractionComparison
      (centralRightFractionCalculus
        (secondFactorDenominators_central
          (G := G) (C := C)))
      (centralLeftFractionCalculus
        (secondFactorDenominators_central
          (G := G) (C := C))) :=
  centralBilateralComparison
    (secondFactorDenominators_central
      (G := G) (C := C))

/-- A nonidentity central second-factor element gives a genuinely nontrivial
denominator. -/
theorem exists_nontrivial_denominator
    (c : C) (hc : c ≠ 1) :
    ∃ s :
        secondFactorDenominators
          (G := G) (C := C),
      (s : G × C) ≠ 1 := by
  let s :
      secondFactorDenominators
        (G := G) (C := C) :=
    ⟨(1, c), rfl⟩
  refine ⟨s, ?_⟩
  intro hs
  apply hc
  exact congrArg Prod.snd hs

end CausalGeometry.Models
