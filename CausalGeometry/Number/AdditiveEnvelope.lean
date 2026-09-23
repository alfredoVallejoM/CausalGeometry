import Mathlib.Data.Multiset.Basic

namespace CausalGeometry

universe u

/-- Free commutative additive envelope of causal generators.
It does not identify this addition with causal sequential composition. -/
abbrev AdditiveEnvelope (α : Type u) :=
  Multiset α

namespace AdditiveEnvelope

variable {α : Type u}

/-- Embed one causal generator into the additive envelope. -/
def atom (x : α) : AdditiveEnvelope α :=
  {x}

@[simp] theorem atom_ne_zero (x : α) :
    atom x ≠ 0 := by
  simp [atom]

/-- Additive natural shadow induced by a weight on generators. -/
def natShadow (weight : α → ℕ) (x : AdditiveEnvelope α) : ℕ :=
  (x.map weight).sum

@[simp] theorem natShadow_zero (weight : α → ℕ) :
    natShadow weight (0 : AdditiveEnvelope α) = 0 := by
  simp [natShadow]

@[simp] theorem natShadow_atom (weight : α → ℕ) (x : α) :
    natShadow weight (atom x) = weight x := by
  simp [natShadow, atom]

@[simp] theorem natShadow_add (weight : α → ℕ)
    (x y : AdditiveEnvelope α) :
    natShadow weight (x + y) =
      natShadow weight x + natShadow weight y := by
  simp [natShadow]

end AdditiveEnvelope
end CausalGeometry
