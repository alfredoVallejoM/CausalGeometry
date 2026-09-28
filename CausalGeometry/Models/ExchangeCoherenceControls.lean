import CausalGeometry.Exchange.ContextRelation
import CausalGeometry.Models.ExchangeThreeEvents

/-!
# CX-I2: a generated quotient and its exact observational boundary

The only equation imposed here is the named ternary pair of CX-I1, with native
closure under composition of exchange ROUTES. The generic closure under causal
HISTORY contexts lives in ContextRelation; this finite local quotient is not
claimed to present every braid/twin/symmetric relation.
-/
namespace CausalGeometry.Models.ExchangeCoherenceControls

open CategoryTheory CausalGeometry.Exchange
open CausalGeometry.Models.ExchangeThreeEvents

abbrev Hist := HistoryCategory initial terminal

/-- A single equation, not universal equality on a hom-set. -/
inductive TernaryEquation : HomRel Hist
  | ternary : TernaryEquation route121 route212

abbrev QuotientHist := CategoryTheory.Quotient TernaryEquation
abbrev projection : Hist ⥤ QuotientHist := CategoryTheory.Quotient.functor TernaryEquation
abbrev memory (t : ZMod 5) : Hist ⥤ Type := interpret (memoryPrefunctor t)

/-- The requested pair really becomes equal in the constructed quotient. -/
theorem ternary_identified : projection.map route121 = projection.map route212 :=
  CategoryTheory.Quotient.sound TernaryEquation TernaryEquation.ternary

/-- The projection is genuinely lossy at the route level. -/
theorem distinct_routes_identified :
    route121 ≠ route212 ∧ projection.map route121 = projection.map route212 :=
  ⟨routes_distinct, ternary_identified⟩

theorem zero_respects : Coherence.Respects TernaryEquation (memory 0) := by
  intro p q P Q w
  cases w
  apply TypeCat.homEquiv.injective
  funext m
  exact zero_offset_forgets m

/-- Among this whole same-typed family, exactly offset zero descends. -/
theorem respects_iff_zero (t : ZMod 5) :
    Coherence.Respects TernaryEquation (memory t) ↔ t = 0 := by
  constructor
  · intro h
    have hmaps := h route121 route212 TernaryEquation.ternary
    have hv := congrArg (fun f : (ZMod 5 ⟶ ZMod 5) => f 0) hmaps
    change observed t route121 0 = observed t route212 0 at hv
    rw [observed_route121, observed_route212] at hv
    simp only [sub_zero] at hv
    have h3 : (3 : ZMod 5) * t = 0 := by
      calc
        3 * t = (t + t) - (-t) := by ring
        _ = 0 := sub_eq_zero.mpr hv.symm
    exact (mul_eq_zero.mp h3).resolve_left (by decide)
  · intro h
    subst t
    exact zero_respects

def descendedZero : QuotientHist ⥤ Type :=
  Coherence.descend TernaryEquation (memory 0) zero_respects

theorem descendedZero_square : projection ⋙ descendedZero = memory 0 :=
  Coherence.descend_spec TernaryEquation (memory 0) zero_respects

theorem factors_iff_zero (t : ZMod 5) :
    (∃ F : QuotientHist ⥤ Type, projection ⋙ F = memory t) ↔ t = 0 := by
  rw [← Coherence.respects_iff_factors TernaryEquation (memory t)]
  exact respects_iff_zero t

/-- Offset two cannot be repaired by choosing a different functor on the same
quotient while requiring the very same factorization square. -/
theorem offset_two_no_factor :
    ¬ ∃ F : QuotientHist ⥤ Type, projection ⋙ F = memory 2 := by
  rw [factors_iff_zero]
  decide

theorem factorsUpToIso_iff_zero (t : ZMod 5) :
    (∃ F : QuotientHist ⥤ Type, Nonempty (projection ⋙ F ≅ memory t)) ↔ t = 0 := by
  rw [← Coherence.respects_iff_factorsUpToIso TernaryEquation (memory t)]
  exact respects_iff_zero t

theorem offset_two_no_factor_upToIso :
    ¬ ∃ F : QuotientHist ⥤ Type, Nonempty (projection ⋙ F ≅ memory 2) := by
  rw [factorsUpToIso_iff_zero]
  decide

/-- No equation policy leaves this pair separate; equality is not implied by
having the same endpoints. -/
def NoEquation : HomRel Hist := fun _ _ _ _ => False

theorem empty_policy_separates :
    ¬ Coherence.Generated NoEquation route121 route212 :=
  Coherence.separated_not_generated NoEquation (𝟭 Hist)
    (fun _ _ h => False.elim h) routes_distinct

/-- A two-exchange loop: no inverse cancellation equation has been imposed. -/
def backAndForth : Route h012 h012 :=
  (Quiver.Path.nil.cons (swapFirst 0 1 2 (by decide) (by decide) (by decide))).cons
    (swapFirst 1 0 2 (by decide) (by decide) (by decide))

def longerRoute : Route h012 h210 := backAndForth.comp route121

/-- A second actual interpretation counts exchanges. It respects the ternary
equation without identifying every pair of parallel routes. -/
def counterPrefunctor : CausalPath system initial terminal ⥤q Type where
  obj _ := Nat
  map _ := TypeCat.ofHom Nat.succ

def counter : Hist ⥤ Type := interpret counterPrefunctor

theorem counter_respects : Coherence.Respects TernaryEquation counter := by
  intro p q P Q w
  cases w
  rfl

/-- Three and five exchanges remain distinguishable even AFTER the ternary
relation is imposed. This rejects an indiscrete/constant quotient mutation. -/
theorem longerRoute_not_identified :
    projection.map route121 ≠ projection.map longerRoute := by
  intro h
  have hh := Coherence.respects_generated TernaryEquation counter counter_respects
    route121 longerRoute h
  have hv := congrArg (fun f : (Nat ⟶ Nat) => f 0) hh
  have hbad : (3 : Nat) = 5 := hv
  cases hbad

theorem generated_pair_but_not_all :
    Coherence.Generated TernaryEquation route121 route212 ∧
      ¬ Coherence.Generated TernaryEquation route121 longerRoute :=
  ⟨ternary_identified, longerRoute_not_identified⟩

end CausalGeometry.Models.ExchangeCoherenceControls
