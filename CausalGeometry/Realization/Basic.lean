import CausalGeometry.Number.Basic

namespace CausalGeometry

universe u v

/-- A deliberately small typed realization. Additional preservation laws are
theorems or specialized structures, never a bag of optional fields. -/
structure Realization (α : Type u) (β : Type v) where
  toFun : α → β

instance {α : Type u} {β : Type v} :
    CoeFun (Realization α β) (fun _ => α → β) :=
  ⟨Realization.toFun⟩

/-- Indistinguishability induced by a realization. -/
def Realization.Equivalent {α : Type u} {β : Type v}
    (R : Realization α β) (x y : α) : Prop :=
  R x = R y

theorem Realization.equivalent_refl {α : Type u} {β : Type v}
    (R : Realization α β) (x : α) :
    R.Equivalent x x := rfl

/-- Provenance class used by the ECIA derivation ledger. -/
inductive DerivationKind
  | kernel
  | realization
  | model
  | analytic
  | open
  deriving DecidableEq, Repr

end CausalGeometry
