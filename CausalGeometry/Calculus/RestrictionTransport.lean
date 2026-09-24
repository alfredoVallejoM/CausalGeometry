import CausalGeometry.Foundation.PairedTransform

namespace CausalGeometry

universe u v

/-- Dynamics carried on both sides of a structural pair Phi/Psi. No
compatibility with the structural transport is assumed in the carrier. -/
structure PairedDynamics
    {α : Type u} {β : Type v}
    (P : PairedTransform α β) where
  sourceStep : α → α
  targetStep : β → β

namespace PairedDynamics

variable {α : Type u} {β : Type v}
variable {P : PairedTransform α β}

/-- Covariant square for Phi. -/
def ForwardNatural (D : PairedDynamics P) : Prop :=
  ∀ a,
    P.forward (D.sourceStep a) =
      D.targetStep (P.forward a)

/-- Contravariant/correlative square for Psi. This is independent of
ForwardNatural unless a theorem connects them. -/
def BackwardNatural (D : PairedDynamics P) : Prop :=
  ∀ b,
    P.backward (D.targetStep b) =
      D.sourceStep (P.backward b)

def Natural (D : PairedDynamics P) : Prop :=
  D.ForwardNatural ∧ D.BackwardNatural

/-- Failure of causal evolution and forward structural transport to commute. -/
def forwardDefect [AddGroup β]
    (D : PairedDynamics P) (a : α) : β :=
  P.forward (D.sourceStep a) -
    D.targetStep (P.forward a)

/-- Failure of causal evolution and backward/restriction transport to commute. -/
def backwardDefect [AddGroup α]
    (D : PairedDynamics P) (b : β) : α :=
  P.backward (D.targetStep b) -
    D.sourceStep (P.backward b)

theorem forwardNatural_iff_defect_zero [AddGroup β]
    (D : PairedDynamics P) :
    D.ForwardNatural ↔ ∀ a, D.forwardDefect a = 0 := by
  constructor
  · intro h a
    exact sub_eq_zero.mpr (h a)
  · intro h a
    exact sub_eq_zero.mp (h a)

theorem backwardNatural_iff_defect_zero [AddGroup α]
    (D : PairedDynamics P) :
    D.BackwardNatural ↔ ∀ b, D.backwardDefect b = 0 := by
  constructor
  · intro h b
    exact sub_eq_zero.mpr (h b)
  · intro h b
    exact sub_eq_zero.mp (h b)

/-- If both structural directions are natural, the source round trip commutes
with source dynamics. -/
theorem sourceRoundTrip_natural
    (D : PairedDynamics P)
    (hF : D.ForwardNatural)
    (hB : D.BackwardNatural)
    (a : α) :
    P.sourceRoundTrip (D.sourceStep a) =
      D.sourceStep (P.sourceRoundTrip a) := by
  unfold PairedTransform.sourceRoundTrip
  simp only [Function.comp_apply]
  rw [hF a, hB (P.forward a)]

/-- If both directions are natural, the target round trip commutes with target
dynamics. -/
theorem targetRoundTrip_natural
    (D : PairedDynamics P)
    (hF : D.ForwardNatural)
    (hB : D.BackwardNatural)
    (b : β) :
    P.targetRoundTrip (D.targetStep b) =
      D.targetStep (P.targetRoundTrip b) := by
  unfold PairedTransform.targetRoundTrip
  simp only [Function.comp_apply]
  rw [hB b, hF (P.backward b)]

end PairedDynamics
end CausalGeometry
