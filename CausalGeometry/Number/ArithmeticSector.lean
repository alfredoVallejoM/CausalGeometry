import CausalGeometry.Number.NatShadow
import CausalGeometry.Number.Residual

namespace CausalGeometry

universe u

/-- Minimal arithmetic sector: an ordered causal multiplication with residuals
and a multiplicative natural shadow.  Factorization, valuations and
completions are derived layers and are not fields of this structure. -/
structure CausalArithmeticSector
    (α : Type u) [PartialOrder α] [Monoid α] where
  residual : ResiduatedMultiplication α
  shadow : NatShadow α

namespace CausalArithmeticSector

open CausalDivisibility

variable {α : Type u} [PartialOrder α] [Monoid α]
variable (S : CausalArithmeticSector α)

def leftRestriction (x : α) : ExtensionRestriction α α :=
  S.residual.leftExtensionRestriction x

def rightRestriction (x : α) : ExtensionRestriction α α :=
  S.residual.rightExtensionRestriction x

theorem leftDivides_sound {x z : α} (h : LeftDivides x z) :
    S.shadow x ∣ S.shadow z :=
  S.shadow.leftDivides_sound h

theorem rightDivides_sound {x z : α} (h : RightDivides x z) :
    S.shadow x ∣ S.shadow z :=
  S.shadow.rightDivides_sound h

theorem exactLeftDivision_iff {x z : α} :
    S.residual.ExactLeftDivision x z ↔ LeftDivides x z :=
  S.residual.exactLeftDivision_iff_leftDivides x z

theorem exactRightDivision_iff {x z : α} :
    S.residual.ExactRightDivision z x ↔ RightDivides x z :=
  S.residual.exactRightDivision_iff_rightDivides z x

end CausalArithmeticSector
end CausalGeometry
