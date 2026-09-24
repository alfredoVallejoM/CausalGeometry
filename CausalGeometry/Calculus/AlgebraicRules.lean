import CausalGeometry.Calculus.Difference
import Mathlib.LinearAlgebra.Basic
import Mathlib.Tactic

namespace CausalGeometry

universe u v w x
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

theorem causalDifference_add
    {A : Type w} [AddCommGroup A]
    (F G : Configuration S → A)
    (C : Configuration S)
    (e : Event) (h : S.Enabled C e) :
    causalDifference (fun X => F X + G X) C e h =
      causalDifference F C e h + causalDifference G C e h := by
  unfold causalDifference
  abel

theorem causalDifference_sub
    {A : Type w} [AddCommGroup A]
    (F G : Configuration S → A)
    (C : Configuration S)
    (e : Event) (h : S.Enabled C e) :
    causalDifference (fun X => F X - G X) C e h =
      causalDifference F C e h - causalDifference G C e h := by
  unfold causalDifference
  abel

/-- Noncommutative finite product rule with chronological endpoint placement.
The first factor is evaluated at the new configuration in the first term and
the second factor at the old configuration in the second term. -/
theorem causalDifference_mul
    {R : Type w} [Ring R]
    (F G : Configuration S → R)
    (C : Configuration S)
    (e : Event) (h : S.Enabled C e) :
    causalDifference (fun X => F X * G X) C e h =
      F (S.extend C e h) * causalDifference G C e h
        + causalDifference F C e h * G C := by
  unfold causalDifference
  noncomm_ring

/-- Linear realizations commute with first causal difference. -/
theorem causalDifference_linearMap
    {K : Type w} {V : Type x} {W : Type*}
    [Semiring K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (L : V →ₗ[K] W)
    (F : Configuration S → V)
    (C : Configuration S)
    (e : Event) (h : S.Enabled C e) :
    causalDifference (fun X => L (F X)) C e h =
      L (causalDifference F C e h) := by
  simp [causalDifference, map_sub]

end CausalGeometry
