import CausalGeometry.Completion.LocalProjectiveCharts
import Mathlib.RingTheory.LocalRing.RingHom.Basic

namespace CausalGeometry

universe u v

namespace LocalProjectivePair

variable
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S]

/-- A local ring hom sends non-units to non-units. -/
def mapNonunit
    (f : R →+* S) [IsLocalHom f]
    (u : Nonunit R) :
    Nonunit S where
  val := f u.1
  property := by
    intro h
    exact u.2 ((isUnit_map_iff f u.1).mp h)

@[simp] theorem mapNonunit_val
    (f : R →+* S) [IsLocalHom f]
    (u : Nonunit R) :
    (mapNonunit f u).1 = f u.1 := rfl

/-- Map between the two-chart parameter spaces induced by a local hom. -/
def chartMap
    (f : R →+* S) [IsLocalHom f] :
    Chart R → Chart S
  | Sum.inl t => Sum.inl (f t)
  | Sum.inr u => Sum.inr (mapNonunit f u)

/-- Naturality of the affine chart. -/
theorem map_affine
    (f : R →+* S)
    (t : R) :
    map f (Quotient.mk _ (affine t)) =
      Quotient.mk _ (affine (f t)) := by
  rfl

/-- Naturality of the non-unit infinity chart for a local hom. -/
theorem map_infinity
    (f : R →+* S) [IsLocalHom f]
    (u : Nonunit R) :
    map f (Quotient.mk _ (infinityChart u)) =
      Quotient.mk _ (infinityChart (mapNonunit f u)) := by
  rfl

/-- The canonical chart equivalence commutes with every local ring hom. -/
theorem chartEquiv_natural
    (f : R →+* S) [IsLocalHom f]
    (c : Chart R) :
    map f (chartEquiv c) =
      chartEquiv (chartMap f c) := by
  cases c with
  | inl t =>
      rfl
  | inr u =>
      rfl

/-- Projective fibers are canonically equivalent to fibers of the chart map. -/
noncomputable def mapFiberEquivChartFiber
    (f : R →+* S) [IsLocalHom f]
    (q : Line S) :
    {x : Line R // map f x = q} ≃
      {c : Chart R //
        chartMap f c = (chartEquiv (R := S)).symm q} where
  toFun := fun x => by
    let c := (chartEquiv (R := R)).symm x.1
    refine ⟨c, ?_⟩
    apply (chartEquiv (R := S)).injective
    rw [← chartEquiv_natural f c]
    simp [c, x.2]
  invFun := fun c => by
    refine ⟨chartEquiv c.1, ?_⟩
    rw [chartEquiv_natural f c.1]
    exact congrArg (chartEquiv (R := S)) c.2
      |>.trans ((chartEquiv (R := S)).apply_symm_apply q)
  left_inv := by
    intro x
    apply Subtype.ext
    simp
  right_inv := by
    intro c
    apply Subtype.ext
    simp

end LocalProjectivePair
end CausalGeometry
