import CausalGeometry.Foundation.CorrelativeRestriction
import CausalGeometry.Process.Diary

namespace CausalGeometry

universe u v w

/-- A semantic relation between the input and output boundaries of a diary.
It is deliberately separate from the diary carrier: distinct semantics may be
compared on the same causal syntax. -/
structure BoundarySemantics
    {A : Type u} {B : Type v} (D : Diary A B) where
  relates : A → B → Prop

namespace BoundarySemantics

variable {A : Type u} {B : Type v}
variable {D : Diary A B}

/-- Every boundary semantics canonically induces forward extension and
correlative restriction of boundary conditions. -/
def extensionRestriction (S : BoundarySemantics D) :
    ExtensionRestriction (Set A) (Set B) :=
  CorrelativeRestriction.ofRelation S.relates

def extend (S : BoundarySemantics D) (P : Set A) : Set B :=
  CorrelativeRestriction.relExtend S.relates P

def restrict (S : BoundarySemantics D) (Q : Set B) : Set A :=
  CorrelativeRestriction.relRestrict S.relates Q

theorem adjunction (S : BoundarySemantics D) (P : Set A) (Q : Set B) :
    S.extend P ⊆ Q ↔ P ⊆ S.restrict Q :=
  CorrelativeRestriction.relAdjunction S.relates P Q

end BoundarySemantics
end CausalGeometry
