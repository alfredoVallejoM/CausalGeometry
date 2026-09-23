import CausalGeometry.Number.Divisibility

namespace CausalGeometry

universe u

namespace CausalDivisibility

variable {α : Type u} [Monoid α]

/-- Universal left gcd in the causal divisibility preorder. -/
def IsLeftGCD (g x y : α) : Prop :=
  LeftDivides g x ∧
  LeftDivides g y ∧
  ∀ d, LeftDivides d x → LeftDivides d y → LeftDivides d g

/-- Universal right gcd in the causal divisibility preorder. -/
def IsRightGCD (g x y : α) : Prop :=
  RightDivides g x ∧
  RightDivides g y ∧
  ∀ d, RightDivides d x → RightDivides d y → RightDivides d g

/-- Universal left lcm in the causal divisibility preorder. -/
def IsLeftLCM (m x y : α) : Prop :=
  LeftDivides x m ∧
  LeftDivides y m ∧
  ∀ z, LeftDivides x z → LeftDivides y z → LeftDivides m z

/-- Universal right lcm in the causal divisibility preorder. -/
def IsRightLCM (m x y : α) : Prop :=
  RightDivides x m ∧
  RightDivides y m ∧
  ∀ z, RightDivides x z → RightDivides y z → RightDivides m z

theorem leftGCD_unique_up_to_divisibility {g h x y : α}
    (hg : IsLeftGCD g x y) (hh : IsLeftGCD h x y) :
    LeftDivides g h ∧ LeftDivides h g := by
  constructor
  · exact hh.2.2 g hg.1 hg.2.1
  · exact hg.2.2 h hh.1 hh.2.1

theorem leftLCM_unique_up_to_divisibility {m n x y : α}
    (hm : IsLeftLCM m x y) (hn : IsLeftLCM n x y) :
    LeftDivides m n ∧ LeftDivides n m := by
  constructor
  · exact hm.2.2 n hn.1 hn.2.1
  · exact hn.2.2 m hm.1 hm.2.1

end CausalDivisibility
end CausalGeometry
