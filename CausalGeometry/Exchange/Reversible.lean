import CausalGeometry.Exchange.Path
import Mathlib.CategoryTheory.Groupoid.FreeGroupoid

/-!
# Formal reversal of causal exchanges, independent of coherence equations

Reuse mathlib's free groupoid on the actual exchange quiver. Its inverses
reverse transformations BETWEEN histories, not primitive causal executions.
An independently supplied arrow in the opposite direction is not identified
with a formal inverse. That identification needs an additional equation.
-/
namespace CausalGeometry.Exchange.Reversible

open CategoryTheory
universe uV vV uW vW uG vG
variable {V : Type uV} [Quiver.{vV} V]
variable {W : Type uW} [Quiver.{vW} W]
variable {G : Type uG} [Groupoid.{vG} G]

/-- Canonical functor from the free path category into the native free groupoid. -/
def positive : CategoryTheory.Paths V ⥤ Quiver.FreeGroupoid V :=
  CategoryTheory.Paths.lift (Quiver.FreeGroupoid.of V)

@[simp] theorem positive_nil (X : V) :
    (positive (V := V)).map (Quiver.Path.nil : Quiver.Path X X) =
      𝟙 ((Quiver.FreeGroupoid.of V).obj X) := rfl

@[simp] theorem positive_cons {X Y Z : V} (p : Quiver.Path X Y) (s : Y ⟶ Z) :
    (positive (V := V)).map (p.cons s) =
      (positive (V := V)).map p ≫ (Quiver.FreeGroupoid.of V).map s := rfl

/-- Every groupoid-valued interpretation of generators extends canonically. -/
abbrev extend (f : V ⥤q G) : Quiver.FreeGroupoid V ⥤ G :=
  Quiver.FreeGroupoid.lift f

@[simp] theorem extend_generator (f : V ⥤q G) {X Y : V} (s : X ⟶ Y) :
    (extend f).map ((Quiver.FreeGroupoid.of V).map s) = f.map s := by
  change (CategoryTheory.Paths.lift (Quiver.Symmetrify.lift f)).map
    s.toPos.toPath = f.map s
  rw [CategoryTheory.Paths.lift_toPath]
  rfl

@[simp] theorem extend_inverse (f : V ⥤q G)
    {X Y : Quiver.FreeGroupoid V} (s : X ⟶ Y) :
    (extend f).map (Groupoid.inv s) = Groupoid.inv ((extend f).map s) := by
  simp only [Groupoid.inv_eq_inv, Functor.map_inv]

theorem extend_spec (f : V ⥤q G) :
    Quiver.FreeGroupoid.of V ⋙q (extend f).toPrefunctor = f :=
  Quiver.FreeGroupoid.lift_spec f

theorem extend_unique (f : V ⥤q G) (F : Quiver.FreeGroupoid V ⥤ G)
    (h : Quiver.FreeGroupoid.of V ⋙q F.toPrefunctor = f) : F = extend f :=
  Quiver.FreeGroupoid.lift_unique f F h

/-- Extending to inverses agrees with the old interpretation on positive routes. -/
theorem positive_extend (f : V ⥤q G) :
    positive ⋙ extend f = CategoryTheory.Paths.lift f := by
  apply CategoryTheory.Paths.lift_unique
  rw [Functor.toPrefunctor_comp, ← Prefunctor.comp_assoc]
  change (CategoryTheory.Paths.of V ⋙q
    (CategoryTheory.Paths.lift (Quiver.FreeGroupoid.of V)).toPrefunctor) ⋙q
    (extend f).toPrefunctor = f
  rw [CategoryTheory.Paths.lift_spec]
  exact extend_spec f

/-- Actual inverse laws; no Yang–Baxter hypothesis occurs here. -/
theorem positive_comp_inverse {X Y : V} (p : Quiver.Path X Y) :
    (positive (V := V)).map p ≫ Groupoid.inv ((positive (V := V)).map p) =
      𝟙 ((positive (V := V)).obj X) :=
  Groupoid.comp_inv _

theorem inverse_comp_positive {X Y : V} (p : Quiver.Path X Y) :
    Groupoid.inv ((positive (V := V)).map p) ≫ (positive (V := V)).map p =
      𝟙 ((positive (V := V)).obj Y) :=
  Groupoid.inv_comp _

/-- A typed map of generators induces a functor, not merely an object map. -/
abbrev map (f : V ⥤q W) : Quiver.FreeGroupoid V ⥤ Quiver.FreeGroupoid W :=
  Quiver.freeGroupoidFunctor f

theorem map_id : map (Prefunctor.id V) = 𝟭 (Quiver.FreeGroupoid V) :=
  Quiver.freeGroupoidFunctor_id

theorem map_comp {U : Type*} [Quiver U] (f : V ⥤q W) (g : W ⥤q U) :
    map (f ⋙q g) = map f ⋙ map g :=
  Quiver.freeGroupoidFunctor_comp f g

end CausalGeometry.Exchange.Reversible

namespace CausalGeometry.Exchange

open EventSystem CategoryTheory
universe u v
variable {Event : Type u} {Label : Type v} {S : EventSystem Event Label}

abbrev HistoryGroupoid (C D : Configuration S) :=
  Quiver.FreeGroupoid (CausalPath S C D)

/-- Genuine causal prefix and suffix maps extend to formal reversals. -/
def prefixOnGroupoid {A C D : Configuration S} (r : CausalPath S A C) :
    HistoryGroupoid C D ⥤ HistoryGroupoid A D :=
  Reversible.map (prefixPrefunctor r)

def suffixOnGroupoid {C D E : Configuration S} (r : CausalPath S D E) :
    HistoryGroupoid C D ⥤ HistoryGroupoid C E :=
  Reversible.map (suffixPrefunctor r)

end CausalGeometry.Exchange
