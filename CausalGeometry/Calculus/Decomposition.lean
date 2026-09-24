namespace CausalGeometry

universe u v

/-- Three independently typed contributions to the causal differential.

The decomposition mirrors D = d_v + d_h + d_mu. No square-zero law is bundled:
flatness, curvature and complex conditions remain separate theorems with their
own hypotheses. -/
structure CausalDifferentialSplit
    (Ω₀ : Type u) (Ω₁ : Type v) [Add Ω₁] where
  vertical : Ω₀ → Ω₁
  horizontal : Ω₀ → Ω₁
  restriction : Ω₀ → Ω₁

namespace CausalDifferentialSplit

variable {Ω₀ : Type u} {Ω₁ : Type v} [Add Ω₁]

def total (D : CausalDifferentialSplit Ω₀ Ω₁) (x : Ω₀) : Ω₁ :=
  D.vertical x + D.horizontal x + D.restriction x

@[simp] theorem total_apply
    (D : CausalDifferentialSplit Ω₀ Ω₁) (x : Ω₀) :
    D.total x =
      D.vertical x + D.horizontal x + D.restriction x :=
  rfl

end CausalDifferentialSplit

/-- Square-zero is an explicit property of a differential on one carrier, not
part of the definition of a causal differential split. -/
def CausalSquareZero {Ω : Type u} [Zero Ω]
    (D : Ω → Ω) : Prop :=
  ∀ x, D (D x) = 0

end CausalGeometry
