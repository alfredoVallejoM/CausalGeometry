namespace CausalGeometry

universe u v w

/-- The structural causal/restriction primitive.

A paired transform contains two oppositely directed transformations
  Phi : α -> β
  Psi : β -> α
and deliberately assumes no inverse, adjunction, dagger, duality or semantic
interpretation. Additional laws are separate bridge structures. -/
structure PairedTransform (α : Type u) (β : Type v) where
  forward : α → β
  backward : β → α

namespace PairedTransform

variable {α : Type u} {β : Type v}

/-- Mathematical alias for the forward structural transformation Phi. -/
def phi (P : PairedTransform α β) : α → β :=
  P.forward

/-- Mathematical alias for the backward structural transformation Psi. -/
def psi (P : PairedTransform α β) : β → α :=
  P.backward

def identity (α : Type u) : PairedTransform α α where
  forward := id
  backward := id

/-- Composition is covariant in Phi and contravariant in Psi. -/
def comp {γ : Type w}
    (P : PairedTransform α β)
    (Q : PairedTransform β γ) :
    PairedTransform α γ where
  forward := Q.forward ∘ P.forward
  backward := P.backward ∘ Q.backward

@[simp] theorem identity_forward (a : α) :
    (identity α).forward a = a := rfl

@[simp] theorem identity_backward (a : α) :
    (identity α).backward a = a := rfl

@[simp] theorem comp_forward {γ : Type w}
    (P : PairedTransform α β)
    (Q : PairedTransform β γ) (a : α) :
    (P.comp Q).forward a = Q.forward (P.forward a) := rfl

@[simp] theorem comp_backward {γ : Type w}
    (P : PairedTransform α β)
    (Q : PairedTransform β γ) (c : γ) :
    (P.comp Q).backward c = P.backward (Q.backward c) := rfl

/-- Round trip on the source. It is an observable structural operation, not
assumed to be the identity. -/
def sourceRoundTrip (P : PairedTransform α β) : α → α :=
  P.backward ∘ P.forward

/-- Round trip on the target. It is an observable structural operation, not
assumed to be the identity. -/
def targetRoundTrip (P : PairedTransform α β) : β → β :=
  P.forward ∘ P.backward

def SourceFixed (P : PairedTransform α β) (a : α) : Prop :=
  P.sourceRoundTrip a = a

def TargetFixed (P : PairedTransform α β) (b : β) : Prop :=
  P.targetRoundTrip b = b

@[simp] theorem identity_sourceRoundTrip (a : α) :
    (identity α).sourceRoundTrip a = a := rfl

@[simp] theorem identity_targetRoundTrip (a : α) :
    (identity α).targetRoundTrip a = a := rfl

end PairedTransform
end CausalGeometry
