import CausalGeometry.Realization.Basic

namespace CausalGeometry

universe u v w x

/-- A realization whose target type is part of the data.  This lets one causal
source have many target theories without storing them as fields of the source. -/
structure AnyRealization (α : Type u) where
  Target : Type v
  map : α → Target

namespace AnyRealization

instance {α : Type u} : CoeFun (AnyRealization.{u, v} α)
    (fun R => α → R.Target) :=
  ⟨AnyRealization.map⟩

/-- A typed comparison between two realizations of the same source. -/
structure Comparison {α : Type u}
    (R : AnyRealization.{u, v} α)
    (S : AnyRealization.{u, w} α) where
  map : R.Target → S.Target
  commutes : ∀ x, map (R x) = S x

namespace Comparison

def id {α : Type u} (R : AnyRealization.{u, v} α) :
    Comparison R R where
  map := id
  commutes := by intro x; rfl

def comp {α : Type u}
    {R : AnyRealization.{u, v} α}
    {S : AnyRealization.{u, w} α}
    {T : AnyRealization.{u, x} α}
    (η : Comparison R S) (θ : Comparison S T) :
    Comparison R T where
  map := θ.map ∘ η.map
  commutes := by
    intro a
    rw [Function.comp_apply, η.commutes, θ.commutes]

end Comparison

/-- Two source objects become indistinguishable in one realization. -/
def Collapses {α : Type u}
    (R : AnyRealization.{u, v} α) (x y : α) : Prop :=
  R x = R y

theorem collapses_refl {α : Type u}
    (R : AnyRealization.{u, v} α) (x : α) :
    R.Collapses x x := rfl

/-- Information loss can only increase after a realization factors through
another one. -/
theorem collapse_of_comparison {α : Type u}
    {R : AnyRealization.{u, v} α}
    {S : AnyRealization.{u, w} α}
    (η : Comparison R S) {x y : α}
    (h : R.Collapses x y) :
    S.Collapses x y := by
  unfold Collapses at h ⊢
  rw [← η.commutes x, ← η.commutes y, h]

/-- A family of realizations is jointly conservative when equality in all
targets forces equality in the source. -/
def JointlyConservative {α : Type u} {ι : Type v}
    (R : ι → AnyRealization.{u, w} α) : Prop :=
  ∀ x y, (∀ i, (R i).Collapses x y) → x = y

end AnyRealization
end CausalGeometry
