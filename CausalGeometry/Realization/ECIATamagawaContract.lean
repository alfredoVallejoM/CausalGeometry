import CausalGeometry.Realization.ECIAContract
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic

namespace CausalGeometry

open scoped BigOperators

universe u v w x y z

namespace Tamagawa

/-- A finite quotient recording the connected-component shadow of one local
realization.

The quotient map is structural data.  Its cardinality is *derived* from the
component carrier; the Tamagawa index is therefore not introduced as an
independent numeric field.  A downstream Neron model may identify this
component carrier with the rational points of the Neron component group.

No distinguished point is stored here: preservation of the group identity is
a target-side group-theoretic obligation, while this source contract records
only the quotient needed to derive the component cardinal. -/
structure LocalComponentQuotient (Point : Type u) where
  Component : Type v
  finiteComponent : Finite Component
  componentNonempty : Nonempty Component
  componentOf : Point → Component
  surjective :
    Function.Surjective componentOf

namespace LocalComponentQuotient

variable {Point : Type u}

/-- Structural local Tamagawa index: the number of components in the local
pointed quotient. -/
def tamagawaIndex
    (Q : LocalComponentQuotient.{u, v} Point) : ℕ :=
  Nat.card Q.Component


/-- Every structural Tamagawa index is positive: a component carrier is
finite and nonempty, as it must be for a component group. -/
theorem tamagawaIndex_pos
    (Q : LocalComponentQuotient.{u, v} Point) :
    0 < Q.tamagawaIndex := by
  letI : Finite Q.Component := Q.finiteComponent
  letI : Nonempty Q.Component := Q.componentNonempty
  exact Nat.card_pos

/-- In particular no structural Tamagawa factor can be zero. -/
theorem tamagawaIndex_ne_zero
    (Q : LocalComponentQuotient.{u, v} Point) :
    Q.tamagawaIndex ≠ 0 :=
  (Q.tamagawaIndex_pos).ne'

/-- An equivalence of component carriers preserves the local Tamagawa index. -/
theorem tamagawaIndex_eq_of_equiv
    (Q : LocalComponentQuotient.{u, v} Point)
    {Point' : Type w}
    (Q' : LocalComponentQuotient.{w, x} Point')
    (e : Q.Component ≃ Q'.Component) :
    Q.tamagawaIndex = Q'.tamagawaIndex := by
  simpa [tamagawaIndex] using
    (Nat.card_congr e)

/-- Comparison with a trivial component carrier forces Tamagawa index one.

This is the source-side shape of the classical good-reduction implication
(c_v=1); proving that a concrete elliptic target has trivial Neron component
group remains target mathematics. -/
theorem tamagawaIndex_eq_one_of_punit_equiv
    (Q : LocalComponentQuotient.{u, v} Point)
    (e : Q.Component ≃ PUnit) :
    Q.tamagawaIndex = 1 := by
  calc
    Q.tamagawaIndex =
        Nat.card PUnit := by
      simpa [tamagawaIndex] using
        (Nat.card_congr e)
    _ = 1 := by simp

end LocalComponentQuotient

/-- Finite-support local Tamagawa data over a place type.

The support is the finite set at which a nontrivial component contribution is
allowed.  Outside it the derived local index is required to be one. -/
structure Family
    (Place : Type w)
    [DecidableEq Place] where
  LocalPoint : Place → Type x
  local :
    (place : Place) →
      LocalComponentQuotient.{x, y}
        (LocalPoint place)
  support : Finset Place
  unit_outside_support :
    ∀ place,
      place ∉ support →
        (local place).tamagawaIndex = 1

namespace Family

variable
    {Place : Type w}
    [DecidableEq Place]

/-- Product of the nontrivial local component indices.

This is the finite structural precursor of the Tamagawa product appearing in
BSD.  No BSD equality is asserted here. -/
def globalTamagawaIndex
    (F : Family.{w, x, y} Place) : ℕ :=
  ∏ place in F.support,
    (F.local place).tamagawaIndex

@[simp] theorem outside_support
    (F : Family.{w, x, y} Place)
    (place : Place)
    (hplace : place ∉ F.support) :
    (F.local place).tamagawaIndex = 1 :=
  F.unit_outside_support place hplace

end Family

/-- Typed comparison with a concrete Neron component carrier.

The source does not define the Neron component group.  A downstream elliptic
realization supplies that carrier and an equivalence with the structural local
component quotient. -/
structure NeronComponentComparison
    {Point : Type u}
    (Q : LocalComponentQuotient.{u, v} Point)
    (NeronComponent : Type w)
    [Finite NeronComponent] where
  componentEquiv :
    Q.Component ≃ NeronComponent

namespace NeronComponentComparison

variable
    {Point : Type u}
    {Q : LocalComponentQuotient.{u, v} Point}
    {NeronComponent : Type w}
    [Finite NeronComponent]

/-- Once the component carrier is identified with the Neron component
carrier, the structural index is exactly its finite cardinality. -/
theorem tamagawaIndex_eq_neronCard
    (h : NeronComponentComparison
      Q NeronComponent) :
    Q.tamagawaIndex =
      Nat.card NeronComponent := by
  simpa [LocalComponentQuotient.tamagawaIndex] using
    (Nat.card_congr h.componentEquiv)

end NeronComponentComparison

/-- Regression contract for a split multiplicative Tate type (I_n).

A real elliptic target must prove independently that the selected local curve
has this reduction type and that its component carrier is equivalent to the
cyclic carrier `Multiplicative (ZMod n)`.  The source then derives
`c_v = n`. -/
structure TateTypeIComparison
    {Point : Type u}
    (Q : LocalComponentQuotient.{u, v} Point) where
  multiplicity : ℕ
  positive : 0 < multiplicity
  componentEquiv :
    Q.Component ≃ Multiplicative (ZMod multiplicity)

namespace TateTypeIComparison

variable
    {Point : Type u}
    {Q : LocalComponentQuotient.{u, v} Point}

/-- The type-I multiplicity is the local Tamagawa index after the explicit
component comparison. -/
theorem tamagawaIndex_eq_multiplicity
    (h : TateTypeIComparison Q) :
    Q.tamagawaIndex = h.multiplicity := by
  calc
    Q.tamagawaIndex =
        Nat.card (Multiplicative (ZMod h.multiplicity)) := by
      simpa [LocalComponentQuotient.tamagawaIndex] using
        (Nat.card_congr
          h.componentEquiv)
    _ = Nat.card (ZMod h.multiplicity) := by
      exact Nat.card_congr Multiplicative.toAdd
    _ = h.multiplicity := by
      rw [Nat.card_zmod]

end TateTypeIComparison

end Tamagawa

namespace ECIARealization

variable {A : Type u}
variable {sourceAdmissible : CausalNumber A → Prop}
variable {T : ECIAStructuralTarget.{u, v} A}
variable {Place : Type w}
variable [DecidableEq Place]

/-- Strong ECIA Tamagawa contract.

The consumer must preserve the finite set of potentially nontrivial places and
must identify the *component carriers themselves*.  Equality of numerical
Tamagawa indices alone is deliberately weaker and is not accepted as a
structural identification. -/
structure PreservesTamagawaComponents
    (R : ECIARealization A sourceAdmissible T)
    (source :
      CausalNumber A →
        Tamagawa.Family.{w, x, y} Place)
    (target :
      T.Target →
        Tamagawa.Family.{w, x, y} Place) : Prop where

  support_eq :
    ∀ X : CausalNumber A,
      (target (R.realize X)).support =
        (source X).support

  componentEquiv :
    ∀ (X : CausalNumber A)
      (place : Place),
      ((source X).local place).Component ≃
        ((target (R.realize X)).local place).Component

namespace PreservesTamagawaComponents

variable
    {R : ECIARealization A sourceAdmissible T}
    {source :
      CausalNumber A →
        Tamagawa.Family.{w, x, y} Place}
    {target :
      T.Target →
        Tamagawa.Family.{w, x, y} Place}
    (h :
      R.PreservesTamagawaComponents
        source target)

/-- Strong component preservation forces equality of every local Tamagawa
index. -/
theorem localTamagawaIndex_eq
    (X : CausalNumber A)
    (place : Place) :
    ((target (R.realize X)).local place)
        .tamagawaIndex =
      ((source X).local place)
        .tamagawaIndex := by
  exact
    (Tamagawa.LocalComponentQuotient
      .tamagawaIndex_eq_of_equiv
        ((source X).local place)
        ((target (R.realize X)).local place)
        (h.componentEquiv X place)).symm

/-- The finite global Tamagawa product is preserved once support and all local
component quotients are preserved. -/
theorem globalTamagawaIndex_eq
    (X : CausalNumber A) :
    (target (R.realize X))
        .globalTamagawaIndex =
      (source X).globalTamagawaIndex := by

  unfold Tamagawa.Family.globalTamagawaIndex

  rw [h.support_eq X]

  apply Finset.prod_congr rfl

  intro place hplace

  exact
    h.localTamagawaIndex_eq X place

end PreservesTamagawaComponents

/-- Weak numerical preservation predicate.

This is useful for loss accounting, but it is intentionally not equivalent to
`PreservesTamagawaComponents`: equal component counts need not identify the
underlying local quotient. -/
def PreservesTamagawaIndices
    (R : ECIARealization A sourceAdmissible T)
    (source :
      CausalNumber A →
        Tamagawa.Family.{w, x, y} Place)
    (target :
      T.Target →
        Tamagawa.Family.{w, x, y} Place) : Prop :=
  ∀ (X : CausalNumber A) (place : Place),
    ((target (R.realize X)).local place)
        .tamagawaIndex =
      ((source X).local place)
        .tamagawaIndex

/-- Strong component preservation implies the weak numerical contract. -/
theorem preservesTamagawaIndices_of_components
    (R : ECIARealization A sourceAdmissible T)
    (source :
      CausalNumber A →
        Tamagawa.Family.{w, x, y} Place)
    (target :
      T.Target →
        Tamagawa.Family.{w, x, y} Place)
    (h :
      R.PreservesTamagawaComponents
        source target) :
    R.PreservesTamagawaIndices
      source target := by
  intro X place
  exact h.localTamagawaIndex_eq X place

end ECIARealization
end CausalGeometry
