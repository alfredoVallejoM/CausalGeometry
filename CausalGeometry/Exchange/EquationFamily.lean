import CausalGeometry.Exchange.Quotient
import CausalGeometry.Exchange.Reversible

/-!
# Typed families of equations, with actual quotient constructors

The data below specify parallel routes, not proofs that they are equal.
In particular a ternary diagram is not automatically a Yang–Baxter diagram
on every configuration, and a reverse generator is not a formal inverse.
-/
namespace CausalGeometry.Exchange.Coherence

open CategoryTheory
universe uC vC uD vD uI
variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- A typed equation to be imposed, without assuming its conclusion. -/
structure ParallelEquation (C : Type uC) [Category.{vC} C] where
  source : C
  target : C
  left : source ⟶ target
  right : source ⟶ target

/-- The generated relation remembers exactly which indexed equations are given. -/
inductive FamilyRelation {I : Type uI} (e : I → ParallelEquation C) : HomRel C
  | equation (i : I) : FamilyRelation e (e i).left (e i).right

abbrev FamilyQuotient {I : Type uI} (e : I → ParallelEquation C) :=
  CategoryTheory.Quotient (FamilyRelation e)

theorem family_respects_iff {I : Type uI} (e : I → ParallelEquation C) (F : C ⥤ D) :
    Respects (FamilyRelation e) F ↔ ∀ i, F.map (e i).left = F.map (e i).right := by
  constructor
  · intro h i
    exact h _ _ (FamilyRelation.equation i)
  · intro h X Y a b w
    cases w with
    | equation i => exact h i

theorem family_factors_iff {I : Type uI} (e : I → ParallelEquation C) (F : C ⥤ D) :
    (∃ G : FamilyQuotient e ⥤ D, CategoryTheory.Quotient.functor (FamilyRelation e) ⋙ G = F)
      ↔ ∀ i, F.map (e i).left = F.map (e i).right := by
  rw [← respects_iff_factors]
  exact family_respects_iff e F

/-- A commuting square is a separate policy from a ternary comparison. -/
def squareEquation {X A B Y : C} (a : X ⟶ A) (b : A ⟶ Y)
    (c : X ⟶ B) (d : B ⟶ Y) : ParallelEquation C :=
  ⟨X, Y, a ≫ b, c ≫ d⟩

/-- A pair of actual three-step routes; causal admissibility is carried by the arrows. -/
def ternaryEquation {X A B E F Y : C}
    (a : X ⟶ A) (b : A ⟶ B) (c : B ⟶ Y)
    (d : X ⟶ E) (e : E ⟶ F) (f : F ⟶ Y) : ParallelEquation C :=
  ⟨X, Y, a ≫ b ≫ c, d ≫ e ≫ f⟩

/-- A round-trip equation does not also impose any three-strand equation. -/
def roundTripEquation {X Y : C} (a : X ⟶ Y) (b : Y ⟶ X) : ParallelEquation C :=
  ⟨X, X, a ≫ b, 𝟙 X⟩

/-- Joined policies remain explicit and feed the existing comparison API. -/
def joinRelation (r s : HomRel C) : HomRel C := fun _ _ P Q => r P Q ∨ s P Q

theorem respects_join_iff (r s : HomRel C) (F : C ⥤ D) :
    Respects (joinRelation r s) F ↔ Respects r F ∧ Respects s F := by
  constructor
  · intro h
    exact ⟨fun P Q w => h P Q (Or.inl w), fun P Q w => h P Q (Or.inr w)⟩
  · rintro ⟨hr, hs⟩ X Y P Q w
    exact w.elim (hr P Q) (hs P Q)

section Groupoid
variable {G : Type uC} [Groupoid.{vC} G]

/-- Comparing a chosen opposite-direction generator to the formal inverse
is additional quotient data, even though G is already a groupoid. -/
def reverseGeneratorEquation {X Y : G} (forward : X ⟶ Y) (backward : Y ⟶ X) :
    ParallelEquation G := ⟨Y, X, backward, Groupoid.inv forward⟩

end Groupoid
end CausalGeometry.Exchange.Coherence
