import Mathlib.LinearAlgebra.Basic

namespace CausalGeometry

universe u v w

/-- Observation of an object/function through a probe. -/
def pullback {X : Type u} {Y : Type v} {R : Type w}
    (φ : Y → X) (A : X → R) : Y → R :=
  A ∘ φ

@[simp] theorem pullback_id {X : Type u} {R : Type w} (A : X → R) :
    pullback id A = A := by
  rfl

theorem pullback_comp {X : Type u} {Y : Type v} {Z : Type w}
    {R : Type*} (φ : Y → X) (ψ : Z → Y) (A : X → R) :
    pullback (φ ∘ ψ) A = pullback ψ (pullback φ A) := by
  rfl

/-- Affine-linear probe used by the Wilderber restriction realization. -/
structure AffineProbe (K : Type u) (V : Type v) (W : Type w)
    [Semiring K] [AddCommMonoid V] [Module K V]
    [AddCommMonoid W] [Module K W] where
  base : V
  linear : W →ₗ[K] V

namespace AffineProbe

variable {K : Type u} {V : Type v} {W : Type w}
variable [Semiring K] [AddCommMonoid V] [Module K V]
variable [AddCommMonoid W] [Module K W]

/-- Underlying affine map \(w ↦ p + Lw\). -/
def eval (P : AffineProbe K V W) : W → V :=
  fun w => P.base + P.linear w

/-- Restriction of an observable/law to an affine probe. -/
def restrict {R : Type*} (P : AffineProbe K V W) (F : V → R) : W → R :=
  pullback P.eval F

@[simp] theorem restrict_apply {R : Type*} (P : AffineProbe K V W)
    (F : V → R) (w : W) :
    P.restrict F w = F (P.base + P.linear w) := rfl

end AffineProbe
end CausalGeometry
