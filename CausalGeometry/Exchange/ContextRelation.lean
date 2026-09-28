import CausalGeometry.Exchange.Quotient

/-!
# Coherence equations stable under causal-history contexts

There are two different compositions: adding exchanges before/after a ROUTE,
and adding events before/after its two underlying HISTORIES. The native
quotient handles the former. This module constructs closure under the latter,
then proves that native congruence generation preserves it. No bicategory or
universal Yang–Baxter law is inferred.
-/
namespace CausalGeometry.Exchange

open CausalGeometry EventSystem CategoryTheory

universe u v
variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

/-- Parallel-route equations, indexed by the original causal endpoints. -/
abbrev RelationFamily (S : EventSystem Event Label) :=
  (C D : Configuration S) → HomRel (HistoryCategory C D)

/-- Only the additional causal context closure. Equivalence and route
composition closure are provided by the native quotient, not reimplemented. -/
inductive ContextClosure (K : RelationFamily S) : RelationFamily S
  | of {C D : Configuration S} {p q : HistoryCategory C D} {P Q : p ⟶ q}
      (w : K C D P Q) : ContextClosure K C D P Q
  | prefix {A C D : Configuration S} {p q : HistoryCategory C D} {P Q : p ⟶ q}
      (r : CausalPath S A C) (w : ContextClosure K C D P Q) :
      ContextClosure K A D ((prefixFunctor r).map P) ((prefixFunctor r).map Q)
  | suffix {C D E : Configuration S} {p q : HistoryCategory C D} {P Q : p ⟶ q}
      (r : CausalPath S D E) (w : ContextClosure K C D P Q) :
      ContextClosure K C E ((suffixFunctor r).map P) ((suffixFunctor r).map Q)

/-- Explicit law for an arbitrary family; it is not assumed of the generators. -/
structure ContextClosed (K : RelationFamily S) : Prop where
  prefix {A C D : Configuration S} {p q : HistoryCategory C D} {P Q : p ⟶ q}
      (r : CausalPath S A C) : K C D P Q →
      K A D ((prefixFunctor r).map P) ((prefixFunctor r).map Q)
  suffix {C D E : Configuration S} {p q : HistoryCategory C D} {P Q : p ⟶ q}
      (r : CausalPath S D E) : K C D P Q →
      K C E ((suffixFunctor r).map P) ((suffixFunctor r).map Q)

theorem contextClosure_closed (K : RelationFamily S) : ContextClosed (ContextClosure K) where
  prefix r w := ContextClosure.prefix r w
  suffix r w := ContextClosure.suffix r w

/-- The constructed closure is the least family closed under causal contexts. -/
theorem contextClosure_le (K L : RelationFamily S) (hL : ContextClosed L)
    (h : ∀ ⦃C D : Configuration S⦄ ⦃p q : HistoryCategory C D⦄ (P Q : p ⟶ q),
      K C D P Q → L C D P Q)
    {C D : Configuration S} {p q : HistoryCategory C D} {P Q : p ⟶ q}
    (w : ContextClosure K C D P Q) : L C D P Q := by
  induction w with
  | of w => exact h _ _ w
  | prefix r w ih => exact hL.prefix r ih
  | suffix r w ih => exact hL.suffix r ih

/-- Equivalence/congruence saturation of the causally contextual generators. -/
def Saturated (K : RelationFamily S) : RelationFamily S :=
  fun C D => Coherence.Generated (ContextClosure K C D)

instance saturatedCongruence (K : RelationFamily S) (C D : Configuration S) :
    CategoryTheory.Congruence (Saturated K C D) :=
  Coherence.generatedCongruence (ContextClosure K C D)

theorem saturated_of (K : RelationFamily S)
    {C D : Configuration S} {p q : HistoryCategory C D} {P Q : p ⟶ q}
    (w : K C D P Q) : Saturated K C D P Q :=
  Coherence.of_generator _ (ContextClosure.of w)

/-- The full generated congruence, not just the generating relations, is
stable under causal-history prefix and suffix contexts. -/
theorem saturated_contextClosed (K : RelationFamily S) : ContextClosed (Saturated K) where
  prefix r w :=
    Coherence.map_generated _ _ (prefixFunctor r)
      (fun _ _ h => Coherence.of_generator _ (ContextClosure.prefix r h)) w
  suffix r w :=
    Coherence.map_generated _ _ (suffixFunctor r)
      (fun _ _ h => Coherence.of_generator _ (ContextClosure.suffix r h)) w

/-- Leastness among families which are BOTH hom-set congruences and closed
under causal-history contexts. The two requirements are not conflated. -/
theorem saturated_le (K L : RelationFamily S) (hL : ContextClosed L)
    [hcong : ∀ C D, CategoryTheory.Congruence (L C D)]
    (h : ∀ ⦃C D : Configuration S⦄ ⦃p q : HistoryCategory C D⦄ (P Q : p ⟶ q),
      K C D P Q → L C D P Q)
    {C D : Configuration S} {p q : HistoryCategory C D} {P Q : p ⟶ q}
    (w : Saturated K C D P Q) : L C D P Q :=
  Coherence.generated_le (ContextClosure K C D) (L C D)
    (fun P Q hPQ => contextClosure_le K L hL h hPQ) w

abbrev CoherenceCategory (K : RelationFamily S) (C D : Configuration S) :=
  CategoryTheory.Quotient (ContextClosure K C D)

/-- Actual descended prefix functor between the two native quotient categories. -/
def prefixOnQuotient (K : RelationFamily S) {A C D : Configuration S}
    (r : CausalPath S A C) : CoherenceCategory K C D ⥤ CoherenceCategory K A D :=
  Coherence.mapQuotient _ _ (prefixFunctor r)
    (fun _ _ w => Coherence.of_generator _ (ContextClosure.prefix r w))

def suffixOnQuotient (K : RelationFamily S) {C D E : Configuration S}
    (r : CausalPath S D E) : CoherenceCategory K C D ⥤ CoherenceCategory K C E :=
  Coherence.mapQuotient _ _ (suffixFunctor r)
    (fun _ _ w => Coherence.of_generator _ (ContextClosure.suffix r w))

theorem prefixOnQuotient_square (K : RelationFamily S) {A C D : Configuration S}
    (r : CausalPath S A C) :
    CategoryTheory.Quotient.functor (ContextClosure K C D) ⋙ prefixOnQuotient K r =
      prefixFunctor r ⋙ CategoryTheory.Quotient.functor (ContextClosure K A D) :=
  Coherence.mapQuotient_spec _ _ _ _

theorem suffixOnQuotient_square (K : RelationFamily S) {C D E : Configuration S}
    (r : CausalPath S D E) :
    CategoryTheory.Quotient.functor (ContextClosure K C D) ⋙ suffixOnQuotient K r =
      suffixFunctor r ⋙ CategoryTheory.Quotient.functor (ContextClosure K C E) :=
  Coherence.mapQuotient_spec _ _ _ _

/-- Increasing a generating family increases the generated relation. -/
theorem saturated_mono (K L : RelationFamily S)
    (h : ∀ ⦃C D : Configuration S⦄ ⦃p q : HistoryCategory C D⦄ (P Q : p ⟶ q),
      K C D P Q → L C D P Q)
    {C D : Configuration S} {p q : HistoryCategory C D} {P Q : p ⟶ q}
    (w : Saturated K C D P Q) : Saturated L C D P Q :=
  saturated_le K (Saturated L) (saturated_contextClosed L)
    (fun P Q hPQ => saturated_of L (h P Q hPQ)) w

end CausalGeometry.Exchange
