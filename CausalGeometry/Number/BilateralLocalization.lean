import CausalGeometry.Number.LeftFractionCalculus
import CausalGeometry.Number.RightFractionCalculus

namespace CausalGeometry

universe u

namespace CausalLocalization

variable {α : Type u} [Monoid α]
variable {S : Submonoid α}

/-- Explicit certificate that a chosen right and left localization calculus
describe the same two-sided localization.

Nothing in RightOreCondition or LeftOreCondition alone constructs this object.
The equivalence must preserve the source embedding and the selected
denominator inverses. -/
structure BilateralFractionComparison
    (R : RightFractionCalculus S)
    (L : LeftFractionCalculus S) where
  equivalence :
    R.QuotientType ≃* L.QuotientType

  source_compat :
    ∀ a : α,
      equivalence (R.sourceHom a) =
        L.sourceHom a

  denominator_compat :
    ∀ s : S,
      equivalence (R.denominatorInverse s) =
        L.denominatorInverse s

namespace BilateralFractionComparison

variable
    {R : RightFractionCalculus S}
    {L : LeftFractionCalculus S}
    (B : BilateralFractionComparison R L)

@[simp] theorem equivalence_source (a : α) :
    B.equivalence (R.sourceHom a) = L.sourceHom a :=
  B.source_compat a

@[simp] theorem equivalence_denominatorInverse (s : S) :
    B.equivalence (R.denominatorInverse s) =
      L.denominatorInverse s :=
  B.denominator_compat s

/-- Right normal forms transport to the corresponding left-localization
elements whenever a bilateral comparison has actually been certified. -/
theorem map_right_normalForm
    (x : RightFraction S) :
    B.equivalence (R.mk x) =
      L.sourceHom x.numerator *
        L.denominatorInverse x.denominator := by
  rw [R.mk_normalForm, map_mul,
    B.equivalence_source, B.equivalence_denominatorInverse]

/-- The inverse comparison also fixes the common source embedding. -/
@[simp] theorem inverse_source (a : α) :
    B.equivalence.symm (L.sourceHom a) =
      R.sourceHom a := by
  apply B.equivalence.injective
  simp

/-- And it fixes selected denominator inverses. -/
@[simp] theorem inverse_denominatorInverse (s : S) :
    B.equivalence.symm (L.denominatorInverse s) =
      R.denominatorInverse s := by
  apply B.equivalence.injective
  simp

/-- In a genuinely commutative/two-sided sector, left normal forms can be
compared with right normal forms only through this explicit certificate. -/
theorem map_left_normalForm
    (x : LeftFraction S) :
    B.equivalence.symm (L.mk x) =
      R.denominatorInverse x.denominator *
        R.sourceHom x.numerator := by
  rw [L.mk_normalForm, map_mul,
    B.inverse_denominatorInverse, B.inverse_source]

end BilateralFractionComparison
end CausalLocalization
end CausalGeometry
