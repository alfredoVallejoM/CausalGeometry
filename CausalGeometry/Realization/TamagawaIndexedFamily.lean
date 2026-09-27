import CausalGeometry.Realization.ECIATamagawaContract
import CausalGeometry.Realization.IndexedFamily

namespace CausalGeometry
namespace Tamagawa

universe u v w x y

/-- One local Tamagawa datum with its point carrier bundled.

Bundling the point type lets an indexed realization family expose local
Tamagawa quotients even when the point carrier varies with the source object
and the place. -/
structure LocalDatum where
  Point : Type x
  quotient :
    LocalComponentQuotient.{x, y} Point

namespace LocalDatum

/-- Derived local index of a bundled datum. -/
def tamagawaIndex
    (D : LocalDatum.{x, y}) : ℕ :=
  D.quotient.tamagawaIndex

theorem tamagawaIndex_pos
    (D : LocalDatum.{x, y}) :
    0 < D.tamagawaIndex :=
  D.quotient.tamagawaIndex_pos

end LocalDatum

namespace Family

variable
    {A : Type u}
    {Place : Type v}
    [DecidableEq Place]

/-- The local Tamagawa data of a common source form an indexed realization
family.

No local datum is free-floating: every placewise quotient is obtained by
evaluating the same source object through the supplied Tamagawa family. -/
def asIndexedRealization
    (F :
      CausalNumber A →
        Family.{v, x, y} Place) :
    IndexedRealizationFamily
      (CausalNumber A) Place where
  Target := fun _ => LocalDatum.{x, y}
  realize :=
    fun place source =>
      { Point :=
          (F source).LocalPoint place
        quotient :=
          (F source).local place }

/-- Evaluation of the indexed realization recovers the original local
component quotient definitionally. -/
@[simp]
theorem asIndexedRealization_quotient
    (F :
      CausalNumber A →
        Family.{v, x, y} Place)
    (source : CausalNumber A)
    (place : Place) :
    ((F.asIndexedRealization.realize
      place source).quotient) =
      (F source).local place :=
  rfl

/-- Consequently the indexed local index is exactly the original Tamagawa
family index. -/
@[simp]
theorem asIndexedRealization_tamagawaIndex
    (F :
      CausalNumber A →
        Family.{v, x, y} Place)
    (source : CausalNumber A)
    (place : Place) :
    (F.asIndexedRealization.realize
      place source).tamagawaIndex =
      ((F source).local place).tamagawaIndex :=
  rfl

/-- Restrict the common-source local realization to any admitted causal
subdomain.

This is the intended route for ECIA consumers whose local elliptic
realization exists only on a named arithmetic-geometric source domain. -/
def asIndexedRealizationOn
    (F :
      CausalNumber A →
        Family.{v, x, y} Place)
    (Domain : CausalNumber A → Prop) :
    IndexedRealizationFamily
      {source : CausalNumber A // Domain source}
      Place :=
  F.asIndexedRealization.restrict Domain

end Family
end Tamagawa
end CausalGeometry
