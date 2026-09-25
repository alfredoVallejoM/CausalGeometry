import CausalGeometry.Completion.RankTwoLattice
import Mathlib.Tactic

namespace CausalGeometry.Models

/-- Coordinatewise embedding Z^2 -> Q^2. -/
def integerPlaneMap :
    (ℤ × ℤ) →ₗ[ℤ] (ℚ × ℚ) where
  toFun := fun x =>
    ((x.1 : ℚ), (x.2 : ℚ))
  map_add' := by
    intro x y
    ext <;> simp
  map_smul' := by
    intro a x
    ext <;> simp

@[simp] theorem integerPlaneMap_apply
    (x : ℤ × ℤ) :
    integerPlaneMap x =
      ((x.1 : ℚ), (x.2 : ℚ)) :=
  rfl

/-- Standard integral lattice Z^2 inside Q^2. -/
def integerPlaneLattice :
    RankTwoLattice ℤ ℚ where
  carrier :=
    LinearMap.range integerPlaneMap
  fg := by
    rw [LinearMap.range_eq_map]
    exact
      Submodule.FG.map _
        (Module.Finite.fg_top :
          (⊤ : Submodule ℤ (ℤ × ℤ)).FG)
  spans := by
    apply top_unique
    intro x hx
    rcases x with ⟨a, b⟩
    let e1 : ℚ × ℚ := (1, 0)
    let e2 : ℚ × ℚ := (0, 1)
    have he1 :
        e1 ∈
          LinearMap.range integerPlaneMap := by
      exact ⟨(1, 0), by
        ext <;> norm_num [e1]⟩
    have he2 :
        e2 ∈
          LinearMap.range integerPlaneMap := by
      exact ⟨(0, 1), by
        ext <;> norm_num [e2]⟩
    have hs1 :
        e1 ∈
          Submodule.span ℚ
            (LinearMap.range integerPlaneMap :
              Set (ℚ × ℚ)) :=
      Submodule.subset_span he1
    have hs2 :
        e2 ∈
          Submodule.span ℚ
            (LinearMap.range integerPlaneMap :
              Set (ℚ × ℚ)) :=
      Submodule.subset_span he2
    have hdecomp :
        (a, b) =
          a • e1 + b • e2 := by
      ext <;> simp [e1, e2]
    rw [hdecomp]
    exact
      Submodule.add_mem _
        (Submodule.smul_mem _ a hs1)
        (Submodule.smul_mem _ b hs2)

/-- Rational unit two. -/
def rationalTwoUnit : ℚˣ :=
  Units.mk0 2 (by norm_num)

@[simp] theorem rationalTwoUnit_val :
    (rationalTwoUnit : ℚ) = 2 :=
  rfl

/-- Scaling Z^2 by two yields another certified lattice. -/
def doubledIntegerPlaneLattice :
    RankTwoLattice ℤ ℚ :=
  integerPlaneLattice.scale rationalTwoUnit

/-- The vector e1 belongs to the original integral lattice. -/
theorem e1_mem_integerPlaneLattice :
    ((1, 0) : ℚ × ℚ) ∈
      integerPlaneLattice.carrier := by
  exact ⟨(1, 0), by
    ext <;> norm_num
  ⟩

/-- e1 does not belong to 2 Z^2. -/
theorem e1_not_mem_doubledIntegerPlaneLattice :
    ((1, 0) : ℚ × ℚ) ∉
      doubledIntegerPlaneLattice.carrier := by
  intro h
  change
    (1, 0 : ℚ) ∈
      integerPlaneLattice.carrier.map
        (RankTwoLattice.scaleEquivO
          (O := ℤ) rationalTwoUnit).toLinearMap at h
  rcases h with ⟨y, hy, hyEq⟩
  rcases hy with ⟨z, hz⟩
  have hycoords :
      y = ((z.1 : ℚ), (z.2 : ℚ)) := by
    exact hz
  subst y
  have hfirst :=
    congrArg Prod.fst hyEq
  norm_num [
    RankTwoLattice.scaleEquivO,
    RankTwoLattice.scaleEquivK,
    rationalTwoUnit
  ] at hfirst
  have hzcast :
      (z.1 : ℚ) = 1 / 2 := by
    linarith
  have hzint :
      (2 * z.1 : ℤ) = 1 := by
    exact_mod_cast
      (show
        (2 : ℚ) * (z.1 : ℚ) = 1 by
          linarith [hfirst])
  omega

/-- The representatives are genuinely different. -/
theorem doubledIntegerPlaneLattice_ne :
    doubledIntegerPlaneLattice ≠
      integerPlaneLattice := by
  intro h
  apply e1_not_mem_doubledIntegerPlaneLattice
  rw [h]
  exact e1_mem_integerPlaneLattice

/-- But they are the same vertex after homothety quotienting. -/
theorem doubled_same_homothety_class :
    RankTwoLattice.classOf
        doubledIntegerPlaneLattice =
      RankTwoLattice.classOf
        integerPlaneLattice := by
  exact
    RankTwoLattice.classOf_scale
      rationalTwoUnit
      integerPlaneLattice

/-- Same-type discriminator: equality of representatives is strictly stronger
than equality of homothety classes. -/
theorem homothety_class_strictly_coarser :
    doubledIntegerPlaneLattice ≠
        integerPlaneLattice ∧
      RankTwoLattice.classOf
          doubledIntegerPlaneLattice =
        RankTwoLattice.classOf
          integerPlaneLattice :=
  ⟨doubledIntegerPlaneLattice_ne,
    doubled_same_homothety_class⟩

end CausalGeometry.Models
