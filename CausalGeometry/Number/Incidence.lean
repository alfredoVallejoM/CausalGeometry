import CausalGeometry.Number.Divisibility
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

namespace CausalGeometry

universe u v

namespace CausalIncidence

open CausalDivisibility

/-- An antisymmetric presentation of left causal divisibility.

The raw causal divisibility relation is generally only a preorder because
mutually divisible objects can differ by units/equivalences. This structure
records a chosen partial-order presentation on which incidence algebra and
Mobius inversion are mathematically well-defined. -/
structure LeftDivisorPresentation
    (α : Type u) (δ : Type v)
    [Monoid α] [PartialOrder δ] where
  realize : δ → α
  realize_injective : Function.Injective realize
  le_iff_leftDivides :
    ∀ a b, a ≤ b ↔ LeftDivides (realize a) (realize b)

namespace LeftDivisorPresentation

variable {α : Type u} {δ : Type v}
variable [Monoid α] [PartialOrder δ]
variable (P : LeftDivisorPresentation α δ)

/-- Incidence zeta on the causal divisor presentation. -/
def zeta [DecidableLE δ] :
    IncidenceAlgebra ℤ δ :=
  IncidenceAlgebra.zeta ℤ

/-- Mobius element of the incidence algebra of causal divisibility. -/
def mobius [LocallyFiniteOrder δ] [DecidableEq δ] :
    IncidenceAlgebra ℤ δ :=
  IncidenceAlgebra.mu ℤ

@[simp] theorem mobius_self
    [LocallyFiniteOrder δ] [DecidableEq δ] (a : δ) :
    P.mobius a a = 1 := by
  simp [mobius]

theorem mobius_eq_zero_of_not_leftDivides
    [LocallyFiniteOrder δ] [DecidableEq δ]
    {a b : δ}
    (h : ¬ LeftDivides (P.realize a) (P.realize b)) :
    P.mobius a b = 0 := by
  apply IncidenceAlgebra.apply_eq_zero_of_not_le
  intro hab
  exact h ((P.le_iff_leftDivides a b).mp hab)

theorem mobius_mul_zeta
    [LocallyFiniteOrder δ] [DecidableEq δ] [DecidableLE δ] :
    P.mobius * P.zeta = 1 := by
  simpa [mobius, zeta] using
    (IncidenceAlgebra.mu_mul_zeta ℤ δ)

theorem zeta_mul_mobius
    [LocallyFiniteOrder δ] [DecidableEq δ] [DecidableLE δ] :
    P.zeta * P.mobius = 1 := by
  simpa [mobius, zeta] using
    (IncidenceAlgebra.zeta_mul_mu (𝕜 := ℤ) (α := δ))

/-- Mobius inversion on a divisor presentation with a least divisor.

If g accumulates f over all divisors below x, then f is recovered by the
incidence Mobius function. -/
theorem moebius_inversion
    [LocallyFiniteOrder δ] [DecidableEq δ] [OrderBot δ]
    (f g : δ → ℤ)
    (h : ∀ x, g x = ∑ y ∈ Finset.Iic x, f y)
    (x : δ) :
    f x =
      ∑ y ∈ Finset.Iic x, P.mobius y x * g y := by
  simpa [mobius] using
    (IncidenceAlgebra.moebius_inversion_bot f g h x)

/-- Incidence convolution is multiplication in the incidence algebra. -/
def convolution
    [LocallyFiniteOrder δ]
    (F G : IncidenceAlgebra ℤ δ) :
    IncidenceAlgebra ℤ δ :=
  F * G

@[simp] theorem convolution_apply
    [LocallyFiniteOrder δ]
    (F G : IncidenceAlgebra ℤ δ) (a b : δ) :
    P.convolution F G a b =
      ∑ x ∈ Finset.Icc a b, F a x * G x b := by
  rfl

end LeftDivisorPresentation

/-- Antisymmetric presentation of right causal divisibility.  It is separate
from the left presentation in genuinely noncommutative arithmetic. -/
structure RightDivisorPresentation
    (α : Type u) (δ : Type v)
    [Monoid α] [PartialOrder δ] where
  realize : δ → α
  realize_injective : Function.Injective realize
  le_iff_rightDivides :
    ∀ a b, a ≤ b ↔ RightDivides (realize a) (realize b)

namespace RightDivisorPresentation

variable {α : Type u} {δ : Type v}
variable [Monoid α] [PartialOrder δ]
variable (P : RightDivisorPresentation α δ)

def zeta [DecidableLE δ] :
    IncidenceAlgebra ℤ δ :=
  IncidenceAlgebra.zeta ℤ

def mobius [LocallyFiniteOrder δ] [DecidableEq δ] :
    IncidenceAlgebra ℤ δ :=
  IncidenceAlgebra.mu ℤ

@[simp] theorem mobius_self
    [LocallyFiniteOrder δ] [DecidableEq δ] (a : δ) :
    P.mobius a a = 1 := by
  simp [mobius]

theorem mobius_eq_zero_of_not_rightDivides
    [LocallyFiniteOrder δ] [DecidableEq δ]
    {a b : δ}
    (h : ¬ RightDivides (P.realize a) (P.realize b)) :
    P.mobius a b = 0 := by
  apply IncidenceAlgebra.apply_eq_zero_of_not_le
  intro hab
  exact h ((P.le_iff_rightDivides a b).mp hab)

theorem mobius_mul_zeta
    [LocallyFiniteOrder δ] [DecidableEq δ] [DecidableLE δ] :
    P.mobius * P.zeta = 1 := by
  simpa [mobius, zeta] using
    (IncidenceAlgebra.mu_mul_zeta ℤ δ)

theorem zeta_mul_mobius
    [LocallyFiniteOrder δ] [DecidableEq δ] [DecidableLE δ] :
    P.zeta * P.mobius = 1 := by
  simpa [mobius, zeta] using
    (IncidenceAlgebra.zeta_mul_mu (𝕜 := ℤ) (α := δ))

theorem moebius_inversion
    [LocallyFiniteOrder δ] [DecidableEq δ] [OrderBot δ]
    (f g : δ → ℤ)
    (h : ∀ x, g x = ∑ y ∈ Finset.Iic x, f y)
    (x : δ) :
    f x =
      ∑ y ∈ Finset.Iic x, P.mobius y x * g y := by
  simpa [mobius] using
    (IncidenceAlgebra.moebius_inversion_bot f g h x)

end RightDivisorPresentation

/-- Mobius factorizes across independent causal divisor channels represented by
a Cartesian product of locally finite divisor posets. -/
theorem mobius_product_channels
    {δ ε : Type*}
    [PartialOrder δ] [PartialOrder ε]
    [LocallyFiniteOrder δ] [LocallyFiniteOrder ε]
    [DecidableEq δ] [DecidableEq ε]
    [DecidableLE δ] [DecidableLE ε]
    (a₁ a₂ : δ) (b₁ b₂ : ε) :
    IncidenceAlgebra.mu ℤ (a₁, b₁) (a₂, b₂) =
      IncidenceAlgebra.mu ℤ a₁ a₂ *
        IncidenceAlgebra.mu ℤ b₁ b₂ := by
  rw [← IncidenceAlgebra.mu_prod_mu
    (𝕜 := ℤ) (α := δ) (β := ε)]
  rfl

/-- Euler characteristic, hence total Mobius content, multiplies across
independent bounded causal channels. -/
theorem eulerChar_product_channels
    {δ ε : Type*}
    [PartialOrder δ] [PartialOrder ε]
    [LocallyFiniteOrder δ] [LocallyFiniteOrder ε]
    [DecidableEq δ] [DecidableEq ε]
    [DecidableLE δ] [DecidableLE ε]
    [BoundedOrder δ] [BoundedOrder ε] :
    IncidenceAlgebra.eulerChar ℤ (δ × ε) =
      IncidenceAlgebra.eulerChar ℤ δ *
        IncidenceAlgebra.eulerChar ℤ ε := by
  exact IncidenceAlgebra.eulerChar_prod
    (𝕜 := ℤ) (α := δ) (β := ε)

end CausalIncidence
end CausalGeometry
