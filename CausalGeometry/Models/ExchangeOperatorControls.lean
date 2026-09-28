import CausalGeometry.Exchange.CausalArtin
import CausalGeometry.Models.ExchangeThreeEvents
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Local operators: directed YB, symmetric exchange, reversible non-YB,
# and general-group Hurwitz, all with actual causal consumers

These models do not assert a faithful representation of a braid group.
General identities are proved algebraically; finite witnesses only refute
stronger claims. The old three-event source is reused unchanged.
-/
namespace CausalGeometry.Models.ExchangeOperatorControls

open CategoryTheory CausalGeometry.Exchange LocalOperator
universe u
variable {A : Type u}

def flip : PairOperator A := fun p => (p.2, p.1)

theorem flip_yb : YangBaxter (flip (A := A)) := by rintro ⟨a, b, c⟩; rfl

theorem flip_involutive : Function.Involutive (flip (A := A)) := by rintro ⟨a, b⟩; rfl

def copyRight : PairOperator A := fun p => (p.2, p.2)

theorem copyRight_yb : YangBaxter (copyRight (A := A)) := by rintro ⟨a, b, c⟩; rfl

theorem copyRight_not_injective : ¬ Function.Injective (copyRight (A := Bool)) := by
  intro h
  have hh := h (show copyRight (false, false) = copyRight (true, false) from rfl)
  have impossible : (false : Bool) = true := congrArg Prod.fst hh
  cases impossible

/-- No output component is forgotten, yet the ternary coherence can fail. -/
def toggleFirst : PairOperator Bool := fun p => (!p.1, p.2)

theorem toggleFirst_involutive : Function.Involutive toggleFirst := by
  rintro ⟨a, b⟩
  cases a <;> rfl

theorem toggleFirst_not_yb : ¬ YangBaxter toggleFirst := by
  intro h
  have hh := h (false, false, false)
  have impossible : (false : Bool) = true := congrArg Prod.fst hh
  cases impossible

/-- A concrete reason the three-slot hypothesis in stepList_braid cannot be dropped. -/
theorem invalid_slot_breaks_braid :
    stepList flip 0 (stepList flip 1 (stepList flip 0 [false, true])) ≠
      stepList flip 1 (stepList flip 0 (stepList flip 1 [false, true])) := by decide

abbrev flipPositive (n : Nat) := Artin.positiveAction (flip (A := A)) flip_yb n
abbrev flipSymmetric (n : Nat) := Artin.symmetricAction (flip (A := A)) flip_yb flip_involutive n
abbrev directedPositive (n : Nat) := Artin.positiveAction (copyRight (A := A)) copyRight_yb n

section Hurwitz
variable {G : Type u} [Group G]

def hurwitz : PairOperator G := fun p => (p.1 * p.2 * p.1⁻¹, p.1)

def hurwitzInverse : PairOperator G := fun p => (p.2, p.2⁻¹ * p.1 * p.2)

theorem hurwitz_left_inverse : Function.LeftInverse (hurwitzInverse (G := G)) hurwitz := by
  rintro ⟨a, b⟩
  apply Prod.ext <;> simp [hurwitz, hurwitzInverse, mul_assoc]

theorem hurwitz_right_inverse : Function.RightInverse (hurwitzInverse (G := G)) hurwitz := by
  rintro ⟨a, b⟩
  apply Prod.ext <;> simp [hurwitz, hurwitzInverse, mul_assoc]

def hurwitzEquiv : (G × G) ≃ (G × G) where
  toFun := hurwitz
  invFun := hurwitzInverse
  left_inv := hurwitz_left_inverse
  right_inv := hurwitz_right_inverse

theorem hurwitz_yb : YangBaxter (hurwitz (G := G)) := by
  rintro ⟨a, b, c⟩
  apply Prod.ext
  · simp [leftTriple, rightTriple, hurwitz, mul_assoc]
  · apply Prod.ext <;> simp [leftTriple, rightTriple, hurwitz, mul_assoc]

theorem hurwitz_product (a b : G) : (hurwitz (a, b)).1 * (hurwitz (a, b)).2 = a * b := by
  simp [hurwitz, mul_assoc]

/-- The ordered product is preserved for arbitrary lists, positions and groups. -/
theorem hurwitz_list_product (i : Nat) (xs : List G) :
    (stepList hurwitz i xs).prod = xs.prod := by
  induction i generalizing xs with
  | zero =>
      cases xs with
      | nil => rfl
      | cons a xs => cases xs with
        | nil => rfl
        | cons b xs => simp [stepList, hurwitz, mul_assoc]
  | succ i ih => cases xs <;> simp [stepList, ih]

abbrev hurwitzPositive (n : Nat) := Artin.positiveAction (hurwitz (G := G)) hurwitz_yb n

variable {Event : Type*} {Label : Type*} {S : EventSystem Event Label}

/-- An invariant of actual causal exchange routes, not only of an abstract word. -/
theorem causal_hurwitz_product {C D : EventSystem.Configuration S}
    {p q : CausalPath S C D} (r : Exchange.Route p q) (xs : Sized G p.length) :
    (((CausalOperator.action hurwitz C D).map r) xs).val.prod = xs.val.prod := by
  induction r with
  | nil => rfl
  | cons r s ih =>
      change (stepList hurwitz s.position
        (((CausalOperator.action hurwitz C D).map r) xs).val).prod = xs.val.prod
      rw [hurwitz_list_product]
      exact ih

end Hurwitz

section ExistingSource
open CausalGeometry.Models.ExchangeThreeEvents

def zeroState : Sized Bool h012.length :=
  ⟨[false, false, false], by
    have h := CausalPath.eventList_length h012
    rw [history_eventList] at h
    exact h⟩

/-- Concrete source-connected failure of ternary coherence despite involutivity. -/
theorem toggle_causal_left :
    (((CausalOperator.action toggleFirst initial terminal).map route121) zeroState).val =
      [false, true, false] := rfl

theorem toggle_causal_right :
    (((CausalOperator.action toggleFirst initial terminal).map route212) zeroState).val =
      [true, false, false] := rfl

theorem toggle_causal_separates :
    (CausalOperator.action toggleFirst initial terminal).map route121 ≠
      (CausalOperator.action toggleFirst initial terminal).map route212 := by
  intro h
  have hh := congrArg (fun f : Sized Bool h012.length ⟶ Sized Bool h210.length => (f zeroState).val) h
  rw [toggle_causal_left, toggle_causal_right] at hh
  cases hh

/-- An actual source object for the three-strand Artin realization. -/
def initialArity : CausalArtin.ArityHistory initial terminal 2 :=
  ⟨h012, by
    have h := CausalPath.eventList_length h012
    rw [history_eventList] at h
    exact h.symm⟩

end ExistingSource
end CausalGeometry.Models.ExchangeOperatorControls
