import CausalGeometry.Exchange.CausalArtin
import CausalGeometry.Exchange.CausalOperatorTransport

/-!
# The missing comparison: actual causal fibers versus positional Artin action

I4's realization_square compared two positional constructions. Here we also
compare the action obtained by forgetting the arity wrapper and using the
original CausalOperator.action. The comparison is an explicit natural
isomorphism, whose components only transport the certified list size.
-/
namespace CausalGeometry.Exchange.CausalArtin

open CategoryTheory EventSystem LocalOperator OperatorTransport
universe u v w
variable {Event : Type u} {Label : Type v} {S : EventSystem Event Label}
variable {A : Type w}

/-- Transport only the size certificate, never the coefficient list. -/
def castSize {a b : Nat} (h : a = b) (xs : Sized A a) : Sized A b :=
  ⟨xs.val, xs.property.trans h⟩

@[simp] theorem castSize_val {a b : Nat} (h : a = b) (xs : Sized A a) :
    (castSize h xs).val = xs.val := rfl

@[simp] theorem castSize_rfl {a : Nat} (xs : Sized A a) : castSize rfl xs = xs :=
  Subtype.ext rfl

theorem castSize_trans {a b c : Nat} (h : a = b) (k : b = c) (xs : Sized A a) :
    castSize k (castSize h xs) = castSize (h.trans k) xs := Subtype.ext rfl

/-- Coefficient changes and arity transport commute without an operator law. -/
theorem mapSized_castSize {B : Type w} (f : A → B) {a b : Nat}
    (h : a = b) (xs : Sized A a) :
    mapSized f (castSize h xs) = castSize h (mapSized f xs) := Subtype.ext rfl

def sizeIso {a b : Nat} (h : a = b) : Sized A a ≅ Sized A b where
  hom := TypeCat.ofHom (castSize h)
  inv := TypeCat.ofHom (castSize h.symm)
  hom_inv_id := by
    apply TypeCat.homEquiv.injective
    funext xs
    exact Subtype.ext rfl
  inv_hom_id := by
    apply TypeCat.homEquiv.injective
    funext xs
    exact Subtype.ext rfl

/-- Forget the proof of fixed arity, retaining each actual causal route. -/
def forgetPaths (U V : Configuration S) (n : Nat) :
    CategoryTheory.Paths (ArityHistory U V n) ⥤ HistoryCategory U V :=
  CategoryTheory.Paths.lift
    (forget U V n ⋙q CategoryTheory.Paths.of (CausalPath S U V))

/-- Every actual route from an arity-certified history has a canonical lift.
Its intermediate arities follow from the already proved historyLength_eq. -/
def reifyRoute {U V : Configuration S} {n : Nat} {p : CausalPath S U V}
    (hp : p.length = n + 1) : {q : CausalPath S U V} → (r : Route p q) →
      Quiver.Path (⟨p, hp⟩ : ArityHistory U V n)
        (⟨q, r.historyLength_eq.symm.trans hp⟩ : ArityHistory U V n)
  | _, .nil => .nil
  | _, .cons r s => (reifyRoute hp r).cons s

/-- Reifying only adds length proofs; forgetting recovers the original route. -/
theorem forget_reifyRoute {U V : Configuration S} {n : Nat} {p q : CausalPath S U V}
    (hp : p.length = n + 1) (r : Route p q) :
    (forgetPaths U V n).map (reifyRoute hp r) = r := by
  induction r with
  | nil => rfl
  | cons r s ih =>
      change ((forgetPaths U V n).map (reifyRoute hp r)).cons s = r.cons s
      rw [ih]

/-- The genuinely causal action, not defined via the Artin word action. -/
abbrev actualAction (R : PairOperator A) (U V : Configuration S) (n : Nat) :
    CategoryTheory.Paths (ArityHistory U V n) ⥤ Type w :=
  forgetPaths U V n ⋙ CausalOperator.action R U V

abbrev positionalAction (R : PairOperator A) (U V : Configuration S) (n : Nat) :
    CategoryTheory.Paths (ArityHistory U V n) ⥤ Type w :=
  words U V n ⋙ Artin.wordAction R n

/-- Equality of values for every route and every correctly sized input.
This precedes any quotient: even a non-YB operator satisfies this comparison. -/
theorem actual_positional_values (R : PairOperator A) {U V : Configuration S} {n : Nat}
    {p q : CategoryTheory.Paths (ArityHistory U V n)} (r : p ⟶ q)
    (xs : Sized A p.path.length) :
    (((actualAction R U V n).map r) xs).val =
      (((positionalAction R U V n).map r) (castSize p.length_eq xs)).val := by
  induction r with
  | nil => rfl
  | cons r s ih =>
      change stepList R s.position (((actualAction R U V n).map r) xs).val =
        stepList R s.position
          (((positionalAction R U V n).map r) (castSize p.length_eq xs)).val
      exact congrArg (stepList R s.position) ih

/-- Complete natural comparison between two independently constructed actions. -/
def actualPositionalIso (R : PairOperator A) (U V : Configuration S) (n : Nat) :
    actualAction R U V n ≅ positionalAction R U V n :=
  NatIso.ofComponents (fun p => sizeIso p.length_eq) (by
    intro p q r
    apply TypeCat.homEquiv.injective
    funext xs
    apply Subtype.ext
    exact actual_positional_values R r xs)

/-- The source action now compares to the action AFTER Artin realization,
not merely to another expression that already factors through that realization. -/
def actualArtinIso (R : PairOperator A) (hR : YangBaxter R)
    (U V : Configuration S) (n : Nat) :
    actualAction R U V n ≅ realize U V n ⋙ Artin.positiveAction R hR n :=
  actualPositionalIso R U V n ≪≫ eqToIso ((realization_square R hR U V n).symm)

/-- Loss in the positional realization propagates to the ACTUAL causal action.
This is not faithfulness of the source realization. -/
theorem actual_respects_realization (R : PairOperator A) (hR : YangBaxter R)
    (U V : Configuration S) (n : Nat)
    {p q : CategoryTheory.Paths (ArityHistory U V n)} {P Q : p ⟶ q}
    (h : (realize U V n).map P = (realize U V n).map Q) :
    (actualAction R U V n).map P = (actualAction R U V n).map Q := by
  let e := actualArtinIso R hR U V n
  have hm : (realize U V n ⋙ Artin.positiveAction R hR n).map P =
      (realize U V n ⋙ Artin.positiveAction R hR n).map Q :=
    congrArg (fun a => (Artin.positiveAction R hR n).map a) h
  apply (cancel_mono (e.hom.app q)).mp
  rw [e.hom.naturality P, e.hom.naturality Q, hm]

/-- A separated actual coefficient action certifies separation in Artin image. -/
theorem actual_separates_realization (R : PairOperator A) (hR : YangBaxter R)
    (U V : Configuration S) (n : Nat)
    {p q : CategoryTheory.Paths (ArityHistory U V n)} {P Q : p ⟶ q}
    (h : (actualAction R U V n).map P ≠ (actualAction R U V n).map Q) :
    (realize U V n).map P ≠ (realize U V n).map Q := by
  intro heq
  exact h (actual_respects_realization R hR U V n heq)

end CausalGeometry.Exchange.CausalArtin
