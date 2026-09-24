import CausalGeometry.Foundation.PairedTransform
import CausalGeometry.Realization.Basic

namespace CausalGeometry

universe u v w x

/-- Forward half of compatibility between a structural pair and two typed
realizations. It is deliberately independent of the backward half. -/
def ForwardPairedCompatibility
    {α : Type u} {β : Type v}
    {γ : Type w} {δ : Type x}
    (Rα : Realization α γ)
    (Rβ : Realization β δ)
    (P : PairedTransform α β)
    (Q : PairedTransform γ δ) : Prop :=
  ∀ a, Rβ (P.forward a) = Q.forward (Rα a)

/-- Backward/restriction half of compatibility. -/
def BackwardPairedCompatibility
    {α : Type u} {β : Type v}
    {γ : Type w} {δ : Type x}
    (Rα : Realization α γ)
    (Rβ : Realization β δ)
    (P : PairedTransform α β)
    (Q : PairedTransform γ δ) : Prop :=
  ∀ b, Rα (P.backward b) = Q.backward (Rβ b)

/-- A realization square preserving both structural directions. -/
structure PairedRealizationCompatibility
    {α : Type u} {β : Type v}
    {γ : Type w} {δ : Type x}
    (Rα : Realization α γ)
    (Rβ : Realization β δ)
    (P : PairedTransform α β)
    (Q : PairedTransform γ δ) : Prop where
  forward :
    ForwardPairedCompatibility Rα Rβ P Q
  backward :
    BackwardPairedCompatibility Rα Rβ P Q

namespace PairedRealizationCompatibility

variable
    {α : Type u} {β : Type v}
    {γ : Type w} {δ : Type x}
    {Rα : Realization α γ}
    {Rβ : Realization β δ}
    {P : PairedTransform α β}
    {Q : PairedTransform γ δ}

theorem sourceRoundTrip
    (h : PairedRealizationCompatibility Rα Rβ P Q)
    (a : α) :
    Rα (P.sourceRoundTrip a) =
      Q.sourceRoundTrip (Rα a) := by
  unfold PairedTransform.sourceRoundTrip
  simp only [Function.comp_apply]
  rw [h.backward, h.forward]

theorem targetRoundTrip
    (h : PairedRealizationCompatibility Rα Rβ P Q)
    (b : β) :
    Rβ (P.targetRoundTrip b) =
      Q.targetRoundTrip (Rβ b) := by
  unfold PairedTransform.targetRoundTrip
  simp only [Function.comp_apply]
  rw [h.forward, h.backward]

end PairedRealizationCompatibility
end CausalGeometry
