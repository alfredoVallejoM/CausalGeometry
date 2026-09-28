import CausalGeometry.Exchange.LocalOperator
import CausalGeometry.Exchange.EquationFamily
import Mathlib.CategoryTheory.Types.Basic

/-!
# All-rank positive Artin presentations and their constructed operator actions

This is a native path-category quotient on n generators (n+1 strands), not
an assertion that the chronological causal source already satisfies these
relations. The relation family has exactly the distant and adjacent Artin
relations. No inverses, squares, normal form or faithful representation is
silently added. n=0 is admitted: there are no generators.
-/
namespace CausalGeometry.Exchange.Artin

open CategoryTheory LocalOperator
universe u

/-- A dedicated one-object quiver avoids installing extra structure on Unit. -/
inductive Vertex (n : Nat) : Type where
  | base

instance (n : Nat) : Quiver (Vertex n) where
  Hom _ _ := Fin n

abbrev Words (n : Nat) := CategoryTheory.Paths (Vertex n)
abbrev point (n : Nat) : Words n := Vertex.base

def letter {n : Nat} (i : Fin n) : point n ⟶ point n :=
  Quiver.Hom.toPath (show (Vertex.base : Vertex n) ⟶ Vertex.base from i)

inductive Relation (n : Nat) : HomRel (Words n)
  | distant (i j : Fin n) (h : i.val + 1 < j.val) :
      Relation n (letter i ≫ letter j) (letter j ≫ letter i)
  | adjacent (i j : Fin n) (h : i.val + 1 = j.val) :
      Relation n (letter i ≫ letter j ≫ letter i) (letter j ≫ letter i ≫ letter j)

abbrev Positive (n : Nat) := CategoryTheory.Quotient (Relation n)
abbrev projection (n : Nat) : Words n ⥤ Positive n := CategoryTheory.Quotient.functor (Relation n)

theorem distant_identified {n : Nat} (i j : Fin n) (h : i.val + 1 < j.val) :
    (projection n).map (letter i ≫ letter j) =
      (projection n).map (letter j ≫ letter i) :=
  CategoryTheory.Quotient.sound (Relation n) (Relation.distant i j h)

theorem adjacent_identified {n : Nat} (i j : Fin n) (h : i.val + 1 = j.val) :
    (projection n).map (letter i ≫ letter j ≫ letter i) =
      (projection n).map (letter j ≫ letter i ≫ letter j) :=
  CategoryTheory.Quotient.sound (Relation n) (Relation.adjacent i j h)

variable {A : Type u}

def operatorPrefunctor (R : PairOperator A) (n : Nat) : Vertex n ⥤q Type u where
  obj _ := Sized A (n + 1)
  map i := TypeCat.ofHom (act R i)

abbrev wordAction (R : PairOperator A) (n : Nat) : Words n ⥤ Type u :=
  CategoryTheory.Paths.lift (operatorPrefunctor R n)

@[simp] theorem wordAction_letter (R : PairOperator A) {n : Nat} (i : Fin n) :
    (wordAction R n).map (letter i) = TypeCat.ofHom (act R i) :=
  CategoryTheory.Paths.lift_toPath _ _

/-- A two-component YB theorem produces every indexed relation in every rank. -/
theorem operator_respects (R : PairOperator A) (hR : YangBaxter R) (n : Nat) :
    Coherence.Respects (Relation n) (wordAction R n) := by
  intro X Y P Q h
  cases h with
  | distant i j hij =>
      simp only [Functor.map_comp, wordAction_letter]
      apply TypeCat.homEquiv.injective
      funext xs
      exact act_far R i j hij xs
  | adjacent i j hij =>
      simp only [Functor.map_comp, wordAction_letter]
      apply TypeCat.homEquiv.injective
      funext xs
      exact act_braid R hR i j hij xs

def positiveAction (R : PairOperator A) (hR : YangBaxter R) (n : Nat) :
    Positive n ⥤ Type u :=
  Coherence.descend (Relation n) (wordAction R n) (operator_respects R hR n)

theorem positiveAction_square (R : PairOperator A) (hR : YangBaxter R) (n : Nat) :
    projection n ⋙ positiveAction R hR n = wordAction R n :=
  Coherence.descend_spec _ _ _

/-- Involutivity is a different relation family, not a property of all braids. -/
inductive Squares (n : Nat) : HomRel (Words n)
  | square (i : Fin n) : Squares n (letter i ≫ letter i) (𝟙 (point n))

def SymmetricRelation (n : Nat) : HomRel (Words n) :=
  Coherence.joinRelation (Relation n) (Squares n)

abbrev SymmetricPresentation (n : Nat) := CategoryTheory.Quotient (SymmetricRelation n)

/-- This presentation adds squares explicitly. Its geometric permutation
classification is not claimed by the existence of this quotient. -/
theorem operator_respects_squares (R : PairOperator A) (hR : Function.Involutive R)
    (n : Nat) : Coherence.Respects (Squares n) (wordAction R n) := by
  intro X Y P Q h
  cases h with
  | square i =>
      simp only [Functor.map_comp, Functor.map_id, wordAction_letter]
      apply TypeCat.homEquiv.injective
      funext xs
      exact act_leftInverse R R hR i xs

def symmetricAction (R : PairOperator A) (hYB : YangBaxter R)
    (hInv : Function.Involutive R) (n : Nat) : SymmetricPresentation n ⥤ Type u :=
  Coherence.descend (SymmetricRelation n) (wordAction R n)
    ((Coherence.respects_join_iff _ _ _).mpr
      ⟨operator_respects R hYB n, operator_respects_squares R hInv n⟩)

/-- An explicit information-forgetting comparison, with no faithfulness claim. -/
def toSymmetric (n : Nat) : Positive n ⥤ SymmetricPresentation n :=
  Coherence.compare (Relation n) (SymmetricRelation n) (fun _ _ h => Or.inl h)

theorem toSymmetric_square (n : Nat) :
    projection n ⋙ toSymmetric n = CategoryTheory.Quotient.functor (SymmetricRelation n) :=
  Coherence.compare_spec _ _ _

end CausalGeometry.Exchange.Artin
