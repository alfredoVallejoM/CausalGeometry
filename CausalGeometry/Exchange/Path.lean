import CausalGeometry.Exchange.Basic
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# The native free category of causal exchanges

We reuse Quiver.Path and CategoryTheory.Paths, including their actual universal
property. There is no project-local replacement for a path/category/functor.
This increment does not quotient routes by braid or inverse equations.
-/
namespace CausalGeometry.Exchange

universe u v uD vD
open CausalGeometry EventSystem CategoryTheory

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

instance exchangeQuiver (C D : Configuration S) : Quiver (CausalPath S C D) where
  Hom := Step

abbrev Route {C D : Configuration S} (p q : CausalPath S C D) :=
  Quiver.Path p q

abbrev HistoryCategory (C D : Configuration S) :=
  CategoryTheory.Paths (CausalPath S C D)

/-- A route conserves history length, independently of its own length. -/
theorem Route.historyLength_eq {C D : Configuration S} {p q : CausalPath S C D}
    (r : Route p q) : p.length = q.length := by
  induction r with
  | nil => rfl
  | cons t s ih => exact ih.trans s.length_eq

/-- The observer retains the positions of all the exchange witnesses. -/
def Route.positions {C D : Configuration S} {p : CausalPath S C D} :
    {q : CausalPath S C D} → Route p q → List Nat
  | _, .nil => []
  | _, .cons r s => r.positions ++ [s.position]

@[simp] theorem Route.positions_nil {C D : Configuration S} (p : CausalPath S C D) :
    (Quiver.Path.nil : Route p p).positions = [] := rfl

@[simp] theorem Route.positions_cons {C D : Configuration S}
    {p q r : CausalPath S C D} (a : Route p q) (s : Step q r) :
    (a.cons s).positions = a.positions ++ [s.position] := rfl

/-- Native universal extension of an interpretation of elementary exchanges. -/
abbrev interpret {C D : Configuration S} {T : Type uD} [Category.{vD} T]
    (f : CausalPath S C D ⥤q T) : HistoryCategory C D ⥤ T :=
  CategoryTheory.Paths.lift f

/-- Uniqueness is inherited from mathlib's proved free-category theorem. -/
theorem interpret_unique {C D : Configuration S} {T : Type uD} [Category.{vD} T]
    (f : CausalPath S C D ⥤q T) (F : HistoryCategory C D ⥤ T)
    (h : CategoryTheory.Paths.of (CausalPath S C D) ⋙q F.toPrefunctor = f) :
    F = interpret f :=
  CategoryTheory.Paths.lift_unique f F h

/-- Prefix contexts act on generators, using the actual causal composition. -/
def prefixPrefunctor {A C D : Configuration S} (r : CausalPath S A C) :
    CausalPath S C D ⥤q CausalPath S A D where
  obj p := r.comp p
  map s := Step.whiskerLeft r s

/-- Continuation contexts also act on the same quiver, without changing events. -/
def suffixPrefunctor {C D E : Configuration S} (r : CausalPath S D E) :
    CausalPath S C D ⥤q CausalPath S C E where
  obj p := p.comp r
  map s := Step.whiskerRight s r

/-- Contexts extend functorially to all routes, not only elementary swaps. -/
def prefixFunctor {A C D : Configuration S} (r : CausalPath S A C) :
    HistoryCategory C D ⥤ HistoryCategory A D :=
  interpret ((prefixPrefunctor r) ⋙q CategoryTheory.Paths.of (CausalPath S A D))

def suffixFunctor {C D E : Configuration S} (r : CausalPath S D E) :
    HistoryCategory C D ⥤ HistoryCategory C E :=
  interpret ((suffixPrefunctor r) ⋙q CategoryTheory.Paths.of (CausalPath S C E))

end CausalGeometry.Exchange
