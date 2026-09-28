import CausalGeometry.Exchange.CausalArtinComparison
import CausalGeometry.Exchange.ArtinOperatorTransport
import CausalGeometry.Models.ExchangeOperatorControls

/-!
# Nonvacuous coefficient-transport controls over the existing causal source

Same-type counterexamples separate the two directions of PairedTransform.
Injectivity/surjectivity controls delimit transfer of YB. Group homomorphisms
supply a general Hurwitz consumer. No source route is replaced by a list model.
-/
namespace CausalGeometry.Models.ExchangeTransportControls

open CategoryTheory CausalGeometry.Exchange LocalOperator OperatorTransport
open CausalGeometry.Models.ExchangeOperatorControls
universe u
variable {A B : Type u}

theorem flip_intertwines (f : A → B) : Intertwines f flip flip := by
  rintro ⟨a, b⟩
  rfl

theorem copy_intertwines (f : A → B) : Intertwines f copyRight copyRight := by
  rintro ⟨a, b⟩
  rfl

/-- Source and target both satisfy YB; the two directions still need separate laws. -/
def forwardOnly : PairedTransform Bool Bool := ⟨fun _ => false, id⟩

theorem forward_only_intertwines : Intertwines forwardOnly.forward copyRight flip := by
  rintro ⟨a, b⟩
  rfl

theorem backward_fails : ¬ Intertwines forwardOnly.backward flip copyRight := by
  intro h
  have hbad : (false : Bool) = true := congrArg Prod.snd (h (false, true))
  cases hbad

theorem pair_not_compatible :
    ¬ CausalOperatorTransport.Compatible forwardOnly copyRight flip := by
  intro h
  exact backward_fails h.backward

/-- Both squares commute, but the pair remains a projection, not an equivalence. -/
def collapsingPair : PairedTransform Bool Bool := ⟨fun _ => false, fun _ => false⟩

theorem collapsingPair_compatible :
    CausalOperatorTransport.Compatible collapsingPair flip flip :=
  ⟨flip_intertwines _, flip_intertwines _⟩

theorem roundTrip_not_identity : collapsingPair.sourceRoundTrip true ≠ true := by decide

/-- A nonfaithful coefficient map can hide failure of YB. -/
def collapse : Bool → Unit := fun _ => ()
def singletonOperator : PairOperator Unit := fun _ => ((), ())

theorem collapse_intertwines : Intertwines collapse toggleFirst singletonOperator := by
  rintro ⟨a, b⟩
  rfl

theorem singleton_yb : YangBaxter singletonOperator := by
  rintro ⟨⟨⟩, ⟨⟩, ⟨⟩⟩
  rfl

theorem collapse_not_injective : ¬ Function.Injective collapse := by
  intro h
  have hbad : (false : Bool) = true := h rfl
  cases hbad

theorem yb_hidden_by_observation :
    Intertwines collapse toggleFirst singletonOperator ∧
      YangBaxter singletonOperator ∧ ¬ YangBaxter toggleFirst :=
  ⟨collapse_intertwines, singleton_yb, toggleFirst_not_yb⟩

/-- Fixes (false,false), but fails YB away from that image. -/
def controlledNot : PairOperator Bool := fun p =>
  (p.1, if p.1 then !p.2 else p.2)

theorem controlledNot_not_yb : ¬ YangBaxter controlledNot := by
  intro h
  have hbad : (false : Bool) = true := congrArg (fun t => t.2.1) (h (true, false, false))
  cases hbad

theorem nonsurjective_preserves_only_image :
    Intertwines (fun _ : Bool => false) flip controlledNot := by
  rintro ⟨a, b⟩
  rfl

theorem yb_not_transferred_without_surjectivity :
    YangBaxter (flip (A := Bool)) ∧
      Intertwines (fun _ : Bool => false) flip controlledNot ∧
        ¬ YangBaxter controlledNot :=
  ⟨flip_yb, nonsurjective_preserves_only_image, controlledNot_not_yb⟩

section Hurwitz
variable {G H : Type u} [Group G] [Group H]

/-- A genuine algebraic producer of an intertwiner, valid for any group homomorphism. -/
theorem hurwitz_hom_intertwines (f : G →* H) :
    Intertwines f (hurwitz (G := G)) (hurwitz (G := H)) := by
  rintro ⟨a, b⟩
  apply Prod.ext <;> simp [pairMap, hurwitz, mul_assoc]

variable {Event : Type*} {Label : Type*} {S : EventSystem Event Label}

/-- The group-homomorphism comparison holds along every actual causal route. -/
theorem causal_hurwitz_hom (f : G →* H)
    {U V : EventSystem.Configuration S} {p q : CausalPath S U V}
    (r : Route p q) (xs : Sized G p.length) :
    mapSized f (((CausalOperator.action hurwitz U V).map r) xs) =
      ((CausalOperator.action hurwitz U V).map r) (mapSized f xs) :=
  CausalOperatorTransport.map_route f _ _ (hurwitz_hom_intertwines f) r xs

/-- It also descends through the positive Artin presentation at every rank. -/
def positiveHurwitzTransport (f : G →* H) (n : Nat) :
    Artin.positiveAction (hurwitz (G := G)) hurwitz_yb n ⟶
      Artin.positiveAction (hurwitz (G := H)) hurwitz_yb n :=
  Artin.positiveTransport f _ _ (hurwitz_hom_intertwines f) hurwitz_yb hurwitz_yb n
end Hurwitz

section ExistingSource
open CausalGeometry.Models.ExchangeThreeEvents

/-- Lift the OLD route, with arity justified by its old causal length theorem. -/
def arityP := CausalArtin.reifyRoute initialArity.length_eq route121
def arityQ := CausalArtin.reifyRoute initialArity.length_eq route212

theorem arityP_forgets : (CausalArtin.forgetPaths initial terminal 2).map arityP = route121 :=
  CausalArtin.forget_reifyRoute _ _

theorem arityQ_forgets : (CausalArtin.forgetPaths initial terminal 2).map arityQ = route212 :=
  CausalArtin.forget_reifyRoute _ _

/-- This comparison is valid even for the non-YB control: it is not a quotient. -/
theorem toggle_actual_positional :
    (((CausalArtin.actualAction toggleFirst initial terminal 2).map arityP) zeroState).val =
      (((CausalArtin.positionalAction toggleFirst initial terminal 2).map arityP)
        (CausalArtin.castSize initialArity.length_eq zeroState)).val :=
  CausalArtin.actual_positional_values toggleFirst arityP zeroState

/-- Concrete noninverse paired transport, on the SAME histories as all prior controls. -/
def trueState : Sized Bool h012.length :=
  ⟨[true, true, true], zeroState.property⟩

theorem collapsingRoundTrip_changes_state :
    (mapSized collapsingPair.sourceRoundTrip trueState).val ≠ trueState.val := by decide

theorem collapsingRoundTrip_commutes :
    mapSized collapsingPair.sourceRoundTrip
        (((CausalOperator.action flip initial terminal).map route121) trueState) =
      ((CausalOperator.action flip initial terminal).map route121)
        (mapSized collapsingPair.sourceRoundTrip trueState) :=
  CausalOperatorTransport.sourceRoundTrip_route collapsingPair flip flip
    collapsingPair_compatible route121 trueState

/-- A genuine change-of-coefficients transformation can erase this distinction. -/
theorem collapsed_toggle_routes :
    mapSized collapse (((CausalOperator.action toggleFirst initial terminal).map route121) zeroState) =
      mapSized collapse (((CausalOperator.action toggleFirst initial terminal).map route212) zeroState) := by
  apply Subtype.ext
  rw [mapSized_val, mapSized_val, toggle_causal_left, toggle_causal_right]
  rfl

end ExistingSource
end CausalGeometry.Models.ExchangeTransportControls
