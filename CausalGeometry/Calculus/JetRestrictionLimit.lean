import CausalGeometry.Calculus.JetRestriction

namespace CausalGeometry

universe u v

namespace JetRestrictionTower

/-- A coherent infinite jet history through all finite orders. -/
structure JetSection (T : JetRestrictionTower.{u, v}) where
  value : (n : Nat) → T.Jet n
  compatible :
    ∀ n, T.jetTruncate n (value (n + 1)) = value n

/-- A coherent infinite restriction history through all finite orders. -/
structure RestrictionSection (T : JetRestrictionTower.{u, v}) where
  value : (n : Nat) → T.Restriction n
  compatible :
    ∀ n, T.restrictionTruncate n (value (n + 1)) = value n

/-- Forward structural transport lifts from every finite order to coherent
infinite sections when forward truncation compatibility is proved. -/
def forwardSection
    (T : JetRestrictionTower.{u, v})
    (hF : T.ForwardCompatible)
    (J : T.JetSection) :
    T.RestrictionSection where
  value := fun n => (T.pair n).forward (J.value n)
  compatible := by
    intro n
    rw [hF n (J.value (n + 1))]
    rw [J.compatible n]

/-- Backward structural transport lifts independently when backward truncation
compatibility is proved. -/
def backwardSection
    (T : JetRestrictionTower.{u, v})
    (hB : T.BackwardCompatible)
    (R : T.RestrictionSection) :
    T.JetSection where
  value := fun n => (T.pair n).backward (R.value n)
  compatible := by
    intro n
    rw [hB n (R.value (n + 1))]
    rw [R.compatible n]

/-- Compatible finite-order pairs induce one structural pair on the inverse
limits. No inverse or adjunction law is added at the limit. -/
def limitPair
    (T : JetRestrictionTower.{u, v})
    (h : T.Compatible) :
    PairedTransform T.JetSection T.RestrictionSection where
  forward := T.forwardSection h.1
  backward := T.backwardSection h.2

@[simp] theorem limitPair_forward_value
    (T : JetRestrictionTower.{u, v})
    (h : T.Compatible)
    (J : T.JetSection) (n : Nat) :
    ((T.limitPair h).forward J).value n =
      (T.pair n).forward (J.value n) := rfl

@[simp] theorem limitPair_backward_value
    (T : JetRestrictionTower.{u, v})
    (h : T.Compatible)
    (R : T.RestrictionSection) (n : Nat) :
    ((T.limitPair h).backward R).value n =
      (T.pair n).backward (R.value n) := rfl

end JetRestrictionTower
end CausalGeometry
