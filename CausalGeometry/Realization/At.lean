import CausalGeometry.Realization.Family

namespace CausalGeometry

universe u v w z

/-- One realization viewed at one fixed source object. The complete realization
map is retained, while the distinguished value records the object that CA-19
calls Real(X). -/
structure RealizationAt {α : Type u} (x : α) where
  realization : AnyRealization.{u, v} α

namespace RealizationAt

def Target {α : Type u} {x : α}
    (R : RealizationAt.{u, v} x) : Type v :=
  R.realization.Target

def value {α : Type u} {x : α}
    (R : RealizationAt.{u, v} x) : R.Target :=
  R.realization x

def of {α : Type u}
    (R : AnyRealization.{u, v} α) (x : α) :
    RealizationAt.{u, v} x :=
  ⟨R⟩

end RealizationAt

/-- A typed comparison between two realizations of the same fixed source
object. Unlike a global comparison, it only asserts compatibility at that
source object. -/
structure RealizationAtHom {α : Type u} {x : α}
    (R : RealizationAt.{u, v} x)
    (S : RealizationAt.{u, w} x) where
  map : R.Target → S.Target
  commutes : map R.value = S.value

namespace RealizationAtHom

def id {α : Type u} {x : α}
    (R : RealizationAt.{u, v} x) :
    RealizationAtHom R R where
  map := id
  commutes := rfl

def comp {α : Type u} {x : α}
    {R : RealizationAt.{u, v} x}
    {S : RealizationAt.{u, w} x}
    {T : RealizationAt.{u, z} x}
    (η : RealizationAtHom R S)
    (θ : RealizationAtHom S T) :
    RealizationAtHom R T where
  map := θ.map ∘ η.map
  commutes := by
    rw [Function.comp_apply, η.commutes, θ.commutes]

end RealizationAtHom

namespace AnyRealization.Comparison

/-- Every comparison natural on the whole source type restricts to a comparison
at a chosen source object. -/
def at {α : Type u}
    {R : AnyRealization.{u, v} α}
    {S : AnyRealization.{u, w} α}
    (η : AnyRealization.Comparison R S) (x : α) :
    RealizationAtHom (RealizationAt.of R x) (RealizationAt.of S x) where
  map := η.map
  commutes := η.commutes x

end AnyRealization.Comparison

/-- Semantic class of a realization comparison. Classification is explicit
data, never inferred from the existence of a map alone. -/
inductive ComparisonKind
  | equivalence
  | quotientLoss
  | completion
  | localization
  | analyticUpgrade
  | conditionalBridge
  deriving DecidableEq, Repr

/-- A pointwise comparison together with its declared semantic class. -/
structure ClassifiedRealizationAtHom {α : Type u} {x : α}
    (R : RealizationAt.{u, v} x)
    (S : RealizationAt.{u, w} x)
    extends RealizationAtHom R S where
  kind : ComparisonKind

end CausalGeometry
