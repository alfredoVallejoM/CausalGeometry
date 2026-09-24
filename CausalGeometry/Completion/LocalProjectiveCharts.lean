import CausalGeometry.Completion.LocalProjectiveLine
import Mathlib.Data.Fintype.Card

namespace CausalGeometry

universe u

namespace LocalProjectivePair

variable {R : Type u} [CommRing R]

/-- Explicit subtype of non-units used by the second local projective chart. -/
abbrev Nonunit (R : Type u) [CommRing R] :=
  {x : R // ¬ IsUnit x}

/-- Affine chart t |-> [1:t]. -/
def affine (t : R) : LocalProjectivePair R where
  x := 1
  y := t
  unit_coord := Or.inl isUnit_one

/-- Infinity chart u |-> [u:1], restricted to non-units so that it is disjoint
from the affine chart. -/
def infinityChart (u : Nonunit R) :
    LocalProjectivePair R where
  x := u.1
  y := 1
  unit_coord := Or.inr isUnit_one

/-- If the first coordinate is a unit, a projective pair has a canonical
affine representative. -/
theorem equivalent_affine_of_isUnit_x
    (p : LocalProjectivePair R)
    (hx : IsUnit p.x) :
    Equivalent p
      (affine (((hx.unit)⁻¹ : Rˣ) * p.y : R)) := by
  refine ⟨hx.unit⁻¹, ?_⟩
  ext
  · simp [affine, scale, hx.unit_spec]
  · simp [affine, scale]

/-- If the first coordinate is not a unit, admissibility forces the second
coordinate to be a unit and gives the canonical infinity-chart representative. -/
theorem equivalent_infinity_of_not_isUnit_x
    (p : LocalProjectivePair R)
    (hx : ¬ IsUnit p.x) :
    ∃ u : Nonunit R,
      Equivalent p (infinityChart u) := by
  have hy : IsUnit p.y :=
    p.unit_coord.resolve_left hx
  let uval : R := ((hy.unit)⁻¹ : Rˣ) * p.x
  have hu : ¬ IsUnit uval := by
    intro hunit
    have hx' : IsUnit p.x :=
      (IsUnit.mul_iff.mp hunit).2
    exact hx hx'
  let u : Nonunit R := ⟨uval, hu⟩
  refine ⟨u, hy.unit⁻¹, ?_⟩
  ext
  · rfl
  · simp [infinityChart, scale, hy.unit_spec]

/-- Every admitted local projective pair lies in exactly one of the two
canonical chart families, up to uniqueness proved below. -/
theorem exists_chart_normalForm
    (p : LocalProjectivePair R) :
    (∃ t : R, Equivalent p (affine t)) ∨
      (∃ u : Nonunit R, Equivalent p (infinityChart u)) := by
  by_cases hx : IsUnit p.x
  · exact Or.inl
      ⟨(((hx.unit)⁻¹ : Rˣ) * p.y : R),
        equivalent_affine_of_isUnit_x p hx⟩
  · exact Or.inr (equivalent_infinity_of_not_isUnit_x p hx)

/-- Affine normal forms are unique. -/
theorem affine_equivalent_iff
    (s t : R) :
    Equivalent (affine s) (affine t) ↔ s = t := by
  constructor
  · rintro ⟨a, h⟩
    have hx := congrArg LocalProjectivePair.x h
    have hy := congrArg LocalProjectivePair.y h
    change (1 : R) = (a : R) at hx
    change t = (a : R) * s at hy
    have ha : (a : R) = 1 := hx.symm
    simpa [ha] using hy.symm
  · rintro rfl
    exact equivalent_refl _

/-- Infinity-chart normal forms are unique. -/
theorem infinity_equivalent_iff
    (s t : Nonunit R) :
    Equivalent (infinityChart s) (infinityChart t) ↔ s = t := by
  constructor
  · rintro ⟨a, h⟩
    have hx := congrArg LocalProjectivePair.x h
    have hy := congrArg LocalProjectivePair.y h
    change t.1 = (a : R) * s.1 at hx
    change (1 : R) = (a : R) at hy
    have ha : (a : R) = 1 := hy.symm
    apply Subtype.ext
    simpa [ha] using hx.symm
  · rintro rfl
    exact equivalent_refl _

/-- The affine and infinity charts are disjoint. -/
theorem not_equivalent_affine_infinity
    (t : R) (u : Nonunit R) :
    ¬ Equivalent (affine t) (infinityChart u) := by
  rintro ⟨a, h⟩
  have hx := congrArg LocalProjectivePair.x h
  change u.1 = (a : R) at hx
  apply u.2
  rw [hx]
  exact a.isUnit

/-- Two-chart parameter space. -/
abbrev Chart (R : Type u) [CommRing R] :=
  Sum R (Nonunit R)

/-- Send a canonical chart coordinate to its projective class. -/
def chartToLine :
    Chart R → Line R
  | Sum.inl t => Quotient.mk _ (affine t)
  | Sum.inr u => Quotient.mk _ (infinityChart u)

theorem chartToLine_injective :
    Function.Injective (chartToLine (R := R)) := by
  intro x y hxy
  cases x with
  | inl s =>
      cases y with
      | inl t =>
          have hrel :
              Equivalent (affine s) (affine t) :=
            Quotient.exact hxy
          exact congrArg Sum.inl
            ((affine_equivalent_iff s t).mp hrel)
      | inr t =>
          exact False.elim
            ((not_equivalent_affine_infinity s t)
              (Quotient.exact hxy))
  | inr s =>
      cases y with
      | inl t =>
          have hrel :
              Equivalent (affine t) (infinityChart s) :=
            Quotient.exact hxy.symm
          exact False.elim
            ((not_equivalent_affine_infinity t s) hrel)
      | inr t =>
          have hrel :
              Equivalent (infinityChart s) (infinityChart t) :=
            Quotient.exact hxy
          exact congrArg Sum.inr
            ((infinity_equivalent_iff s t).mp hrel)

theorem chartToLine_surjective :
    Function.Surjective (chartToLine (R := R)) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro p
  rcases exists_chart_normalForm p with
    h | h
  · rcases h with ⟨t, ht⟩
    refine ⟨Sum.inl t, ?_⟩
    exact (Quotient.sound ht).symm
  · rcases h with ⟨u, hu⟩
    refine ⟨Sum.inr u, ?_⟩
    exact (Quotient.sound hu).symm

/-- Canonical chart equivalence for the local projective line. -/
noncomputable def chartEquiv :
    Chart R ≃ Line R :=
  Equiv.ofBijective chartToLine
    ⟨chartToLine_injective, chartToLine_surjective⟩

/-- Cardinal decomposition into affine and non-unit charts. -/
theorem natCard_line
    [Fintype R] :
    Nat.card (Line R) =
      Fintype.card R + Nat.card (Nonunit R) := by
  rw [← Nat.card_congr (chartEquiv (R := R))]
  simp

end LocalProjectivePair
end CausalGeometry
