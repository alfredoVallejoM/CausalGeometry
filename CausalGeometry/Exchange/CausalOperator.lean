import CausalGeometry.Exchange.LocalOperator
import CausalGeometry.Exchange.Reversible
import Mathlib.CategoryTheory.Core

/-!
# Local operators on observation fibers of actual causal histories

Each history carries exactly as many coefficient slots as executed events.
Its witnessed exchange position selects the two slots. This construction
works for arbitrary EventSystem and arbitrary R; YB is not imposed on the
source. The groupoid lift needs an actual equivalence, not a mere YB law.
-/
namespace CausalGeometry.Exchange.CausalOperator

open CategoryTheory EventSystem LocalOperator
universe u v w
variable {Event : Type u} {Label : Type v} {A : Type w}
variable {S : EventSystem Event Label}

/-- The existing source supplies the index and proves there are two slots. -/
def prefunctor (R : PairOperator A) (C D : Configuration S) :
    CausalPath S C D ⥤q Type w where
  obj p := Sized A p.length
  map s := TypeCat.ofHom (fun xs =>
    ⟨stepList R s.position xs.val,
      ((stepList_length R s.position xs.val).trans xs.property).trans s.length_eq⟩)

abbrev action (R : PairOperator A) (C D : Configuration S) : HistoryCategory C D ⥤ Type w :=
  interpret (prefunctor R C D)

theorem step_has_two_slots {C D : Configuration S} {p q : CausalPath S C D}
    (s : Exchange.Step p q) (xs : Sized A p.length) : s.position + 2 ≤ xs.val.length := by
  rw [xs.property]
  exact s.position_bound

@[simp] theorem step_action_value (R : PairOperator A) {C D : Configuration S}
    {p q : CausalPath S C D} (s : Exchange.Step p q) (xs : Sized A p.length) :
    ((prefunctor R C D).map s xs).val = stepList R s.position xs.val := rfl

/-- Actual causal prefixing agrees with prefixing the observation fiber. -/
theorem prefix_compatibility (R : PairOperator A) {B C D : Configuration S}
    {p q : CausalPath S C D} (r : CausalPath S B C) (s : Exchange.Step p q)
    (us xs : List A) (h : us.length = r.length) :
    stepList R (Exchange.Step.whiskerLeft r s).position (us ++ xs) =
      us ++ stepList R s.position xs := by
  rw [Exchange.Step.whiskerLeft_position, ← h]
  exact stepList_prefix R us xs s.position

theorem suffix_compatibility (R : PairOperator A) {C D E : Configuration S}
    {p q : CausalPath S C D} (s : Exchange.Step p q) (r : CausalPath S D E)
    (xs : Sized A p.length) (ys : List A) :
    stepList R (Exchange.Step.whiskerRight s r).position (xs.val ++ ys) =
      stepList R s.position xs.val ++ ys :=
  stepList_suffix R s.position xs.val ys (step_has_two_slots s xs)

/-- A real inverse on pairs induces a real inverse between the dependent fibers. -/
def corePrefunctor (e : (A × A) ≃ (A × A)) (C D : Configuration S) :
    CausalPath S C D ⥤q Core (Type w) where
  obj p := ⟨Sized A p.length⟩
  map s := ⟨{
    hom := (prefunctor e C D).map s
    inv := TypeCat.ofHom (fun xs =>
      ⟨stepList e.symm s.position xs.val,
        ((stepList_length e.symm s.position xs.val).trans xs.property).trans s.length_eq.symm⟩)
    hom_inv_id := by
      apply TypeCat.homEquiv.injective
      funext xs
      apply Subtype.ext
      exact stepList_leftInverse e e.symm e.left_inv s.position xs.val
    inv_hom_id := by
      apply TypeCat.homEquiv.injective
      funext xs
      apply Subtype.ext
      exact stepList_leftInverse e.symm e e.right_inv s.position xs.val
  }⟩

abbrev reversibleAction (e : (A × A) ≃ (A × A)) (C D : Configuration S) :
    HistoryGroupoid C D ⥤ Core (Type w) :=
  Reversible.extend (corePrefunctor e C D)

/-- No new or reconstructed state is assigned after localization: the lift
agrees with the original core-valued interpretation on positive histories. -/
theorem reversibleAction_positive (e : (A × A) ≃ (A × A)) (C D : Configuration S) :
    Reversible.positive ⋙ reversibleAction e C D =
      CategoryTheory.Paths.lift (corePrefunctor e C D) :=
  Reversible.positive_extend _

end CausalGeometry.Exchange.CausalOperator
