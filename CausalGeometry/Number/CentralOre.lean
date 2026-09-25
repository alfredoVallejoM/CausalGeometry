import CausalGeometry.Number.OreLocalization

namespace CausalGeometry

universe u

namespace CausalLocalization

variable {α : Type u} [Monoid α]

/-- Denominator submonoid lies in the center of the ambient monoid.

The ambient monoid remains fully noncommutative; only denominators are
required to commute with arbitrary numerators. -/
def CentralDenominators
    (S : Submonoid α) : Prop :=
  ∀ s : S, ∀ a : α,
    Commute (s : α) a

namespace CentralDenominators

variable {S : Submonoid α}
variable (hS : CentralDenominators S)

/-- Central denominators supply canonical right Ore squares without requiring
the ambient monoid to commute. -/
def rightSquare
    (a : α) (s : S) :
    RightOreSquare S a s where
  numerator := a
  denominator := s
  cross := by
    exact (hS s a).eq.symm

/-- Central denominators also supply canonical left Ore squares. -/
def leftSquare
    (a : α) (s : S) :
    LeftOreSquare S a s where
  numerator := a
  denominator := s
  cross := by
    exact (hS s a).eq

theorem rightOre :
    RightOreCondition S := by
  intro a s
  exact ⟨hS.rightSquare a s⟩

theorem leftOre :
    LeftOreCondition S := by
  intro a s
  exact ⟨hS.leftSquare a s⟩

/-- In the central-denominator sector, right-fraction multiplication uses the
expected numerator and denominator products. -/
@[simp] theorem right_mulWith_canonical
    (x y : RightFraction S) :
    RightFraction.mulWith x y
        (hS.rightSquare
          y.numerator x.denominator) =
      { numerator :=
          x.numerator * y.numerator
        denominator :=
          y.denominator * x.denominator } := by
  rfl

/-- Left-fraction multiplication is equally explicit, while retaining its
left-handed denominator order. -/
@[simp] theorem left_mulWith_canonical
    (x y : LeftFraction S) :
    LeftFraction.mulWith x y
        (hS.leftSquare
          x.numerator y.denominator) =
      { denominator :=
          y.denominator * x.denominator
        numerator :=
          x.numerator * y.numerator } := by
  rfl

/-- Both Ore conditions are available simultaneously. -/
theorem bilateralOre :
    RightOreCondition S ∧
      LeftOreCondition S :=
  ⟨hS.rightOre, hS.leftOre⟩

end CentralDenominators

/-- The center submonoid is a canonical source of central denominators. -/
def centerSubmonoid (α : Type u) [Monoid α] :
    Submonoid α where
  carrier := {a | ∀ b : α, Commute a b}
  one_mem' := by
    intro b
    exact Commute.one_left b
  mul_mem' := by
    intro a b ha hb c
    exact (ha c).mul_left (hb c)

theorem centerSubmonoid_central :
    CentralDenominators
      (centerSubmonoid α) := by
  intro s a
  exact s.2 a

theorem centerSubmonoid_bilateralOre :
    RightOreCondition
        (centerSubmonoid α) ∧
      LeftOreCondition
        (centerSubmonoid α) :=
  (centerSubmonoid_central
    (α := α)).bilateralOre

end CausalLocalization
end CausalGeometry
