import CausalGeometry.Foundation.PairedTransform

namespace CausalGeometry

universe u v

/-- A tower pairing finite jet data with finite restriction data.

No compatibility between truncation and the two structural directions is
assumed in the carrier. Forward/backward naturality are separate properties so
one direction may hold without the other. -/
structure JetRestrictionTower where
  Jet : Nat → Type u
  Restriction : Nat → Type v
  pair : (n : Nat) → PairedTransform (Jet n) (Restriction n)
  jetTruncate : (n : Nat) → Jet (n + 1) → Jet n
  restrictionTruncate :
    (n : Nat) → Restriction (n + 1) → Restriction n

namespace JetRestrictionTower

def ForwardCompatible (T : JetRestrictionTower.{u, v}) : Prop :=
  ∀ n (x : T.Jet (n + 1)),
    T.restrictionTruncate n ((T.pair (n + 1)).forward x) =
      (T.pair n).forward (T.jetTruncate n x)

def BackwardCompatible (T : JetRestrictionTower.{u, v}) : Prop :=
  ∀ n (r : T.Restriction (n + 1)),
    T.jetTruncate n ((T.pair (n + 1)).backward r) =
      (T.pair n).backward (T.restrictionTruncate n r)

def Compatible (T : JetRestrictionTower.{u, v}) : Prop :=
  T.ForwardCompatible ∧ T.BackwardCompatible

/-- Source-side round trip at a finite jet order. -/
def jetRoundTrip (T : JetRestrictionTower.{u, v})
    (n : Nat) : T.Jet n → T.Jet n :=
  (T.pair n).sourceRoundTrip

/-- Restriction-side round trip at a finite order. -/
def restrictionRoundTrip (T : JetRestrictionTower.{u, v})
    (n : Nat) : T.Restriction n → T.Restriction n :=
  (T.pair n).targetRoundTrip

theorem jetRoundTrip_truncate
    (T : JetRestrictionTower.{u, v})
    (hF : T.ForwardCompatible)
    (hB : T.BackwardCompatible)
    (n : Nat) (x : T.Jet (n + 1)) :
    T.jetTruncate n (T.jetRoundTrip (n + 1) x) =
      T.jetRoundTrip n (T.jetTruncate n x) := by
  unfold jetRoundTrip PairedTransform.sourceRoundTrip
  change
    T.jetTruncate n
        ((T.pair (n + 1)).backward ((T.pair (n + 1)).forward x)) =
      (T.pair n).backward
        ((T.pair n).forward (T.jetTruncate n x))
  rw [hB n ((T.pair (n + 1)).forward x)]
  rw [hF n x]

theorem restrictionRoundTrip_truncate
    (T : JetRestrictionTower.{u, v})
    (hF : T.ForwardCompatible)
    (hB : T.BackwardCompatible)
    (n : Nat) (r : T.Restriction (n + 1)) :
    T.restrictionTruncate n (T.restrictionRoundTrip (n + 1) r) =
      T.restrictionRoundTrip n (T.restrictionTruncate n r) := by
  unfold restrictionRoundTrip PairedTransform.targetRoundTrip
  change
    T.restrictionTruncate n
        ((T.pair (n + 1)).forward ((T.pair (n + 1)).backward r)) =
      (T.pair n).forward
        ((T.pair n).backward (T.restrictionTruncate n r))
  rw [hF n ((T.pair (n + 1)).backward r)]
  rw [hB n r]

end JetRestrictionTower
end CausalGeometry
