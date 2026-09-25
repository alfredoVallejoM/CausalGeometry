import CausalGeometry.Realization.PairedCompatibility

namespace CausalGeometry

universe u v w x

/-- Backward/restriction compatibility restricted to an admissible target
locus. -/
def BackwardPairedCompatibilityOn
    {α : Type u} {β : Type v}
    {γ : Type w} {δ : Type x}
    (Rα : Realization α γ)
    (Rβ : Realization β δ)
    (P : PairedTransform α β)
    (Q : PairedTransform γ δ)
    (Admissible : β → Prop) : Prop :=
  ∀ b, Admissible b →
    Rα (P.backward b) =
      Q.backward (Rβ b)

/-- A partial paired realization.

Forward/Phi compatibility is global.  Backward/Psi compatibility is required
only on an explicit target locus.  Phi must land in that locus, so source
round trips can still be compared everywhere. -/
structure PairedRealizationCompatibilityOn
    {α : Type u} {β : Type v}
    {γ : Type w} {δ : Type x}
    (Rα : Realization α γ)
    (Rβ : Realization β δ)
    (P : PairedTransform α β)
    (Q : PairedTransform γ δ)
    (Admissible : β → Prop) : Prop where
  forward :
    ForwardPairedCompatibility Rα Rβ P Q

  forward_admissible :
    ∀ a, Admissible (P.forward a)

  backward_on :
    BackwardPairedCompatibilityOn
      Rα Rβ P Q Admissible

namespace PairedRealizationCompatibilityOn

variable
    {α : Type u} {β : Type v}
    {γ : Type w} {δ : Type x}
    {Rα : Realization α γ}
    {Rβ : Realization β δ}
    {P : PairedTransform α β}
    {Q : PairedTransform γ δ}
    {Admissible : β → Prop}
    (h :
      PairedRealizationCompatibilityOn
        Rα Rβ P Q Admissible)

/-- Source round-trip comparison remains global because every Phi-image is
certified admissible. -/
theorem sourceRoundTrip
    (a : α) :
    Rα (P.sourceRoundTrip a) =
      Q.sourceRoundTrip (Rα a) := by
  unfold PairedTransform.sourceRoundTrip
  simp only [Function.comp_apply]
  rw [h.backward_on
    (P.forward a)
    (h.forward_admissible a)]
  rw [h.forward a]

/-- Target round-trip comparison is valid precisely on the declared locus. -/
theorem targetRoundTrip
    (b : β)
    (hb : Admissible b) :
    Rβ (P.targetRoundTrip b) =
      Q.targetRoundTrip (Rβ b) := by
  unfold PairedTransform.targetRoundTrip
  simp only [Function.comp_apply]
  rw [h.forward]
  rw [h.backward_on b hb]

/-- If the target locus is universal, partial compatibility upgrades to the
ordinary global paired compatibility. -/
def toGlobal
    (hall : ∀ b, Admissible b) :
    PairedRealizationCompatibility
      Rα Rβ P Q where
  forward := h.forward
  backward := by
    intro b
    exact h.backward_on b (hall b)

end PairedRealizationCompatibilityOn
end CausalGeometry
