import CausalGeometry.Exchange.ArtinPresentation
import CausalGeometry.Exchange.CausalOperator

/-!
# A typed positional realization from actual fixed-arity causal histories

The history still contains its EventSystem/CausalPath and all enabling data.
Only the realization forgets it to a one-object positive Artin presentation.
This is not an equality imposed on every source history or a faithful map.
-/
namespace CausalGeometry.Exchange.CausalArtin

open EventSystem CategoryTheory LocalOperator
universe u v w
variable {Event : Type u} {Label : Type v} {A : Type w}
variable {S : EventSystem Event Label}

structure ArityHistory (C D : Configuration S) (n : Nat) where
  path : CausalPath S C D
  length_eq : path.length = n + 1

instance (C D : Configuration S) (n : Nat) : Quiver (ArityHistory C D n) where
  Hom p q := Exchange.Step p.path q.path

def forget (C D : Configuration S) (n : Nat) :
    ArityHistory C D n ⥤q CausalPath S C D where
  obj := ArityHistory.path
  map s := s

/-- The generator index is produced by an admitted step and its size proof. -/
def generatorIndex {C D : Configuration S} {n : Nat}
    {p q : ArityHistory C D n} (s : p ⟶ q) : Fin n :=
  ⟨s.position, by have h := s.position_bound; have hp := p.length_eq; omega⟩

def positions (C D : Configuration S) (n : Nat) :
    ArityHistory C D n ⥤q Artin.Words n where
  obj _ := Artin.point n
  map s := Artin.letter (generatorIndex s)

abbrev words (C D : Configuration S) (n : Nat) :
    CategoryTheory.Paths (ArityHistory C D n) ⥤ Artin.Words n :=
  CategoryTheory.Paths.lift (positions C D n)

def realize (C D : Configuration S) (n : Nat) :
    CategoryTheory.Paths (ArityHistory C D n) ⥤ Artin.Positive n :=
  words C D n ⋙ Artin.projection n

/-- Observe first as positional words, or first realize in the Artin quotient:
both constructions agree once the actual two-component YB law is proved. -/
theorem realization_square (R : PairOperator A) (hR : YangBaxter R)
    (C D : Configuration S) (n : Nat) :
    realize C D n ⋙ Artin.positiveAction R hR n =
      words C D n ⋙ Artin.wordAction R n := by
  change (words C D n ⋙ Artin.projection n) ⋙ Artin.positiveAction R hR n = _
  rw [Functor.assoc, Artin.positiveAction_square]

/-- Observation cannot restore information forgotten by this realization. -/
theorem observation_respects_realization (R : PairOperator A) (hR : YangBaxter R)
    (C D : Configuration S) (n : Nat)
    {p q : CategoryTheory.Paths (ArityHistory C D n)} {P Q : p ⟶ q}
    (h : (realize C D n).map P = (realize C D n).map Q) :
    (words C D n ⋙ Artin.wordAction R n).map P =
      (words C D n ⋙ Artin.wordAction R n).map Q := by
  rw [← realization_square R hR C D n]
  exact congrArg (fun f => (Artin.positiveAction R hR n).map f) h

end CausalGeometry.Exchange.CausalArtin
