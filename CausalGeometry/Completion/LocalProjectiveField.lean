import CausalGeometry.Completion.LocalProjectiveLine
import Mathlib.LinearAlgebra.Projectivization.Basic

namespace CausalGeometry

universe u

namespace LocalProjectivePair

variable {F : Type u} [Field F]

/-- Underlying nonzero vector of a local projective pair over a field. -/
def toNonzeroVector
    (p : LocalProjectivePair F) :
    {v : F × F // v ≠ 0} := by
  refine ⟨(p.x, p.y), ?_⟩
  intro hzero
  have hx : p.x = 0 :=
    congrArg Prod.fst hzero
  have hy : p.y = 0 :=
    congrArg Prod.snd hzero
  rcases p.unit_coord with hxu | hyu
  · exact (isUnit_iff_ne_zero.mp hxu) hx
  · exact (isUnit_iff_ne_zero.mp hyu) hy

/-- Every nonzero vector over a field is locally unimodular: at least one
coordinate is a unit. -/
def ofNonzeroVector
    (v : {v : F × F // v ≠ 0}) :
    LocalProjectivePair F where
  x := v.1.1
  y := v.1.2
  unit_coord := by
    by_cases hx : v.1.1 = 0
    · right
      apply isUnit_iff_ne_zero.mpr
      intro hy
      apply v.2
      apply Prod.ext <;> assumption
    · left
      exact isUnit_iff_ne_zero.mpr hx

@[simp] theorem toNonzeroVector_ofNonzeroVector
    (v : {v : F × F // v ≠ 0}) :
    toNonzeroVector (ofNonzeroVector v) = v := by
  apply Subtype.ext
  rfl

@[simp] theorem ofNonzeroVector_toNonzeroVector
    (p : LocalProjectivePair F) :
    ofNonzeroVector (toNonzeroVector p) = p := by
  apply LocalProjectivePair.ext <;> rfl

/-- A local projective representative determines a standard projective-space
point. -/
def pairToProjectivization
    (p : LocalProjectivePair F) :
    Projectivization F (F × F) :=
  Projectivization.mk F
    (toNonzeroVector p).1
    (toNonzeroVector p).2

/-- Unit scaling is invisible in standard projectivization. -/
theorem pairToProjectivization_scale
    (a : Fˣ)
    (p : LocalProjectivePair F) :
    pairToProjectivization (scale a p) =
      pairToProjectivization p := by
  apply
    (Projectivization.mk_eq_mk_iff F
      ((toNonzeroVector (scale a p)).1)
      ((toNonzeroVector p).1)
      ((toNonzeroVector (scale a p)).2)
      ((toNonzeroVector p).2)).2
  refine ⟨a, ?_⟩
  ext <;> simp [
    pairToProjectivization,
    toNonzeroVector,
    scale
  ]

/-- Map from the local-projective quotient to standard projectivization. -/
def lineToProjectivization :
    Line F →
      Projectivization F (F × F) :=
  Quotient.lift
    pairToProjectivization
    (by
      intro p q hpq
      rcases hpq with ⟨a, rfl⟩
      exact pairToProjectivization_scale a p)

/-- A nonzero vector determines a class in the local projective quotient. -/
def nonzeroVectorToLine
    (v : {v : F × F // v ≠ 0}) :
    Line F :=
  Quotient.mk _
    (ofNonzeroVector v)

/-- Scalar multiplication of nonzero vectors does not change the local
projective class. -/
theorem nonzeroVectorToLine_smul
    (a b : {v : F × F // v ≠ 0})
    (t : F)
    (h : a.1 = t • b.1) :
    nonzeroVectorToLine a =
      nonzeroVectorToLine b := by
  have ht : t ≠ 0 := by
    intro ht0
    apply a.2
    rw [h, ht0, zero_smul]
  let u : Fˣ := Units.mk0 t ht
  apply Quotient.sound
  refine ⟨u, ?_⟩
  apply LocalProjectivePair.ext
  · have hx :=
      congrArg Prod.fst h
    simpa [ofNonzeroVector, scale, u] using hx
  · have hy :=
      congrArg Prod.snd h
    simpa [ofNonzeroVector, scale, u] using hy

/-- Standard projectivization maps back to the local-projective quotient. -/
def projectivizationToLine :
    Projectivization F (F × F) →
      Line F :=
  Projectivization.lift
    nonzeroVectorToLine
    nonzeroVectorToLine_smul

@[simp] theorem projectivizationToLine_mk
    (v : F × F)
    (hv : v ≠ 0) :
    projectivizationToLine
        (Projectivization.mk F v hv) =
      Quotient.mk _
        (ofNonzeroVector ⟨v, hv⟩) :=
  rfl

/-- The two projective models are canonically equivalent over a field. -/
noncomputable def lineEquivProjectivization :
    Line F ≃
      Projectivization F (F × F) where
  toFun := lineToProjectivization
  invFun := projectivizationToLine
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro p
    change
      Quotient.mk _
          (ofNonzeroVector
            (toNonzeroVector p)) =
        Quotient.mk _ p
    rw [ofNonzeroVector_toNonzeroVector]
  right_inv := by
    intro q
    induction q using Projectivization.ind with
    | h v hv =>
        change
          pairToProjectivization
              (ofNonzeroVector ⟨v, hv⟩) =
            Projectivization.mk F v hv
        unfold pairToProjectivization
        rw [toNonzeroVector_ofNonzeroVector]

@[simp] theorem lineEquivProjectivization_apply_mk
    (p : LocalProjectivePair F) :
    lineEquivProjectivization
        (Quotient.mk _ p) =
      pairToProjectivization p :=
  rfl

/-- The standard one-dimensional subspace associated with a local-projective
point. -/
noncomputable def lineSubmodule
    (q : Line F) :
    Submodule F (F × F) :=
  (lineEquivProjectivization q).submodule

theorem lineSubmodule_finrank
    (q : Line F) :
    Module.finrank F
        (lineSubmodule q) = 1 :=
  (lineEquivProjectivization q).finrank_submodule

/-- Distinct local-projective points determine distinct one-dimensional
subspaces. -/
theorem lineSubmodule_injective :
    Function.Injective
      (lineSubmodule (F := F)) := by
  intro q r h
  apply lineEquivProjectivization.injective
  exact
    Projectivization.submodule_injective h

end LocalProjectivePair
end CausalGeometry
