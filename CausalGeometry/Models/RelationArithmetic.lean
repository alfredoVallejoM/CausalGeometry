import CausalGeometry.Number.Residual

namespace CausalGeometry

universe u

/-- Binary causal relations on one state space. -/
def CausalRelation (α : Type u) :=
  α → α → Prop

namespace CausalRelation

variable {α : Type u}

instance : LE (CausalRelation α) where
  le r s := ∀ ⦃a b⦄, r a b → s a b

instance : Preorder (CausalRelation α) where
  le_refl r := by
    intro a b h
    exact h
  le_trans r s t hrs hst := by
    intro a b h
    exact hst (hrs h)

instance : One (CausalRelation α) where
  one := Eq

instance : Mul (CausalRelation α) where
  mul r s := fun a c => ∃ b, r a b ∧ s b c

@[simp] theorem one_apply (a b : α) :
    (1 : CausalRelation α) a b ↔ a = b :=
  Iff.rfl

theorem mul_apply (r s : CausalRelation α) (a c : α) :
    (r * s) a c ↔ ∃ b, r a b ∧ s b c :=
  Iff.rfl

instance : Monoid (CausalRelation α) where
  mul_assoc r s t := by
    funext a c
    apply propext
    constructor
    · rintro ⟨b, ⟨d, had, hdb⟩, hbc⟩
      exact ⟨d, had, b, hdb, hbc⟩
    · rintro ⟨d, had, b, hdb, hbc⟩
      exact ⟨b, ⟨d, had, hdb⟩, hbc⟩
  one_mul r := by
    funext a c
    apply propext
    constructor
    · rintro ⟨b, hab, hbc⟩
      simpa using hab ▸ hbc
    · intro hac
      exact ⟨a, rfl, hac⟩
  mul_one r := by
    funext a c
    apply propext
    constructor
    · rintro ⟨b, hab, hbc⟩
      simpa using hbc ▸ hab
    · intro hac
      exact ⟨c, hac, rfl⟩

/-- Left residual of relational composition. -/
def leftResidual (r z : CausalRelation α) : CausalRelation α :=
  fun b c => ∀ a, r a b → z a c

/-- Right residual of relational composition. -/
def rightResidual (z r : CausalRelation α) : CausalRelation α :=
  fun a b => ∀ c, r b c → z a c

theorem leftAdjunction (r s z : CausalRelation α) :
    r * s ≤ z ↔ s ≤ leftResidual r z := by
  constructor
  · intro h b c hs a hra
    exact h ⟨b, hra, hs⟩
  · intro h a c hrs
    rcases hrs with ⟨b, hrb, hsc⟩
    exact h hsc a hrb

theorem rightAdjunction (r s z : CausalRelation α) :
    s * r ≤ z ↔ s ≤ rightResidual z r := by
  constructor
  · intro h a b hs c hrc
    exact h ⟨b, hs, hrc⟩
  · intro h a c hsr
    rcases hsr with ⟨b, hsb, hrc⟩
    exact h hsb c hrc

/-- Binary relations provide a canonical noncommutative residuated causal
arithmetic model. -/
def residuated : ResiduatedMultiplication (CausalRelation α) where
  leftResidual := leftResidual
  rightResidual := rightResidual
  leftAdjunction := leftAdjunction
  rightAdjunction := by
    intro r s z
    exact rightAdjunction r s z

end CausalRelation
end CausalGeometry
