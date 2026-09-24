import CausalGeometry.Foundation.PairedTransform

namespace CausalGeometry

universe u v w

/-- An admitted domain for a structural pair. The carrier remains purely
structural; admission is an optional bridge layer. -/
structure TransportProfile (α : Type u) (β : Type v) where
  pair : PairedTransform α β
  sourceAdmissible : α → Prop
  targetAdmissible : β → Prop
  forward_preserves :
    ∀ a, sourceAdmissible a → targetAdmissible (pair.forward a)
  backward_preserves :
    ∀ b, targetAdmissible b → sourceAdmissible (pair.backward b)

namespace StructuralVariation

variable {α : Type u} {β : Type v} {V : Type w}

/-- Difference measured when an observable is transported in the Phi
direction. The source and target observables are deliberately separate. -/
def forwardDifference [AddGroup V]
    (P : PairedTransform α β)
    (Fsrc : α → V) (Ftgt : β → V) (a : α) : V :=
  Ftgt (P.forward a) - Fsrc a

/-- Difference measured when an observable is transported in the Psi
direction. -/
def backwardDifference [AddGroup V]
    (P : PairedTransform α β)
    (Fsrc : α → V) (Ftgt : β → V) (b : β) : V :=
  Fsrc (P.backward b) - Ftgt b

/-- Observable defect of the source round trip Psi(Phi(-)). This is not assumed
to vanish. -/
def sourceRoundTripDifference [AddGroup V]
    (P : PairedTransform α β)
    (F : α → V) (a : α) : V :=
  F (P.sourceRoundTrip a) - F a

/-- Observable defect of the target round trip Phi(Psi(-)). -/
def targetRoundTripDifference [AddGroup V]
    (P : PairedTransform α β)
    (F : β → V) (b : β) : V :=
  F (P.targetRoundTrip b) - F b

theorem sourceRoundTripDifference_eq_zero_of_fixed [AddGroup V]
    (P : PairedTransform α β) (F : α → V) {a : α}
    (h : P.SourceFixed a) :
    sourceRoundTripDifference P F a = 0 := by
  unfold sourceRoundTripDifference PairedTransform.SourceFixed at *
  rw [h]
  exact sub_self _

theorem targetRoundTripDifference_eq_zero_of_fixed [AddGroup V]
    (P : PairedTransform α β) (F : β → V) {b : β}
    (h : P.TargetFixed b) :
    targetRoundTripDifference P F b = 0 := by
  unfold targetRoundTripDifference PairedTransform.TargetFixed at *
  rw [h]
  exact sub_self _

@[simp] theorem identity_sourceRoundTripDifference [AddGroup V]
    (F : α → V) (a : α) :
    sourceRoundTripDifference (PairedTransform.identity α) F a = 0 := by
  simp [sourceRoundTripDifference]

end StructuralVariation
end CausalGeometry
