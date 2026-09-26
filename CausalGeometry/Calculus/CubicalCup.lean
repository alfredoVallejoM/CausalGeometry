import CausalGeometry.Calculus.CubicalCochain
import CausalGeometry.Calculus.CubicalFrontBack
import CausalGeometry.Calculus.CubicalLowDegree
import CausalGeometry.Calculus.AlgebraicRules
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalCubicalCochain

variable {K : Type w} [Field K]

/-- One ordered Alexander--Whitney causal cubical product value.

For a (p+q)-cube Q:
* the first cochain observes the lower front p-face;
* the second cochain observes the upper back q-face.

The two observations therefore retain chronological information rather than
multiplying unrelated degreewise values at one base point. -/
def orderedCupValue
    (p q : ℕ)
    (α : CausalCubicalCochain S K p)
    (β : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q)) :
    K :=
  α (Q.frontFace p q) *
    β (Q.backFace p q)

/-- Bilinear ordered front/back product on raw causal cubical cochains.

This is one Alexander--Whitney/Serre summand.  The full cubical cup product
must sum its coordinate permutations over all (p,q)-shuffles. -/
def orderedCup
    (p q : ℕ) :
    CausalCubicalCochain S K p →ₗ[K]
      CausalCubicalCochain S K q →ₗ[K]
        CausalCubicalCochain S K (p + q) where
  toFun := fun α =>
    { toFun := fun β Q =>
        orderedCupValue p q α β Q
      map_add' := by
        intro β γ
        funext Q
        simp [orderedCupValue, mul_add]
      map_smul' := by
        intro a β
        funext Q
        simp [orderedCupValue, mul_assoc] }
  map_add' := by
    intro α γ
    apply LinearMap.ext
    intro β
    funext Q
    simp [orderedCupValue, add_mul]
  map_smul' := by
    intro a α
    apply LinearMap.ext
    intro β
    funext Q
    simp [orderedCupValue, mul_assoc, mul_comm,
      mul_left_comm]

@[simp] theorem orderedCup_apply
    (p q : ℕ)
    (α : CausalCubicalCochain S K p)
    (β : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q)) :
    orderedCup p q α β Q =
      α (Q.frontFace p q) *
        β (Q.backFace p q) :=
  rfl

/-- Constant multiplicative unit as a degree-zero cochain. -/
def oneZero :
    CausalCubicalCochain S K 0 :=
  fun _ => 1

@[simp] theorem orderedCup_zero_zero_apply
    (α β : CausalCubicalCochain S K 0)
    (Q : CausalEventCube S 0) :
    orderedCup 0 0 α β Q =
      α Q * β Q := by
  rfl

/-- For configuration observables, degree-zero cup is ordinary pointwise
multiplication. -/
theorem orderedCup_configuration_observables
    (F G : Configuration S → K) :
    orderedCup 0 0
        (ofConfigurationObservable F)
        (ofConfigurationObservable G)
      =
    ofConfigurationObservable
      (fun C => F C * G C) := by
  funext Q
  rw [← CausalEventCube.zeroCube_base_eq Q]
  rfl

/-- First ordered-product/causal-difference compatibility.

On a one-event cube the differential of the degree-zero cup is exactly the
finite difference of the pointwise product. -/
theorem differential_zero_orderedCup_configuration
    (F G : Configuration S → K)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    differential (S := S) (K := K) 0
        (orderedCup 0 0
          (ofConfigurationObservable F)
          (ofConfigurationObservable G))
        (CausalEventCube.oneCube C e h)
      =
    causalDifference
      (fun X => F X * G X)
      C e h := by
  rw [orderedCup_configuration_observables]
  exact
    differential_zero_recovers_causalDifference
      (fun X => F X * G X)
      C e h

/-- Chronological finite product rule recovered from the ordered cubical product.

This is a low-degree regression for the future all-degree graded Leibniz
theorem. -/
theorem differential_zero_orderedCup_product_rule
    (F G : Configuration S → K)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    differential (S := S) (K := K) 0
        (orderedCup 0 0
          (ofConfigurationObservable F)
          (ofConfigurationObservable G))
        (CausalEventCube.oneCube C e h)
      =
    F (S.extend C e h) *
        causalDifference G C e h
      +
    causalDifference F C e h *
        G C := by
  rw [differential_zero_orderedCup_configuration]
  exact causalDifference_mul F G C e h

/-- Ordered degree-zero Leibniz regression.

Because K is commutative, the same product difference can be split as
(dF)·G(new) + F(old)·(dG), which is the p=0 instance of the graded cup
Leibniz rule. -/
theorem differential_zero_orderedCup_leibniz
    (F G : Configuration S → K)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    differential (S := S) (K := K) 0
        (orderedCup 0 0
          (ofConfigurationObservable F)
          (ofConfigurationObservable G))
        (CausalEventCube.oneCube C e h)
      =
    causalDifference F C e h *
        G (S.extend C e h)
      +
    F C *
        causalDifference G C e h := by
  rw [differential_zero_orderedCup_configuration]
  unfold causalDifference
  ring

end CausalCubicalCochain
end CausalGeometry
