import CausalGeometry.Calculus.EventCube
import CausalGeometry.Calculus.Difference
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

open EventSystem
open scoped BigOperators

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

/-- Raw scalar causal cubical cochains in arbitrary degree.

Alternation/orientation constraints are deliberately not baked into this raw
carrier.  The cubical coboundary itself carries the alternating face signs. -/
abbrev CausalCubicalCochain
    (S : EventSystem Event Label)
    (K : Type w)
    (n : ℕ) :=
  CausalEventCube S n → K

namespace CausalCubicalCochain

variable {K : Type w} [Field K]

/-- Scalar sign of a cubical face. -/
def faceSign
    {n : ℕ}
    (i : Fin (n + 1)) : K :=
  (-1 : K) ^ i.val

/-- One signed cubical face contribution: upper face minus lower face. -/
def faceContribution
    {n : ℕ}
    (ω : CausalCubicalCochain S K n)
    (Q : CausalEventCube S (n + 1))
    (i : Fin (n + 1)) : K :=
  faceSign i *
    (ω (Q.upperFace i) -
      ω (Q.lowerFace i))

/-- Arbitrary-degree causal cubical coboundary.

This is the standard alternating sum of upper-minus-lower faces.  The theorem
d^2=0 is intentionally separate and will be obtained from the cubical face
identities; it is not inserted as a field here. -/
def differential
    (n : ℕ) :
    CausalCubicalCochain S K n →ₗ[K]
      CausalCubicalCochain S K (n + 1) where
  toFun := fun ω Q =>
    ∑ i : Fin (n + 1),
      faceContribution ω Q i
  map_add' := by
    intro ω η
    funext Q
    simp only [Pi.add_apply, faceContribution]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  map_smul' := by
    intro a ω
    funext Q
    simp only [Pi.smul_apply, smul_eq_mul,
      faceContribution]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

@[simp] theorem differential_apply
    (n : ℕ)
    (ω : CausalCubicalCochain S K n)
    (Q : CausalEventCube S (n + 1)) :
    differential n ω Q =
      ∑ i : Fin (n + 1),
        faceContribution ω Q i :=
  rfl

@[simp] theorem differential_zero
    (n : ℕ) :
    differential (S := S) (K := K) n 0 = 0 := by
  exact map_zero (differential
    (S := S) (K := K) n)

/-- Embed an ordinary scalar observable on configurations as a degree-zero
cubical cochain by observing the cube base. -/
def ofConfigurationObservable
    (F : Configuration S → K) :
    CausalCubicalCochain S K 0 :=
  fun Q => F Q.base

@[simp] theorem ofConfigurationObservable_zeroCube
    (F : Configuration S → K)
    (C : Configuration S) :
    ofConfigurationObservable F
        (CausalEventCube.zeroCube C) =
      F C :=
  rfl


/-- Degree zero of the arbitrary cubical differential is exactly the original
finite causal difference on a one-event cube.  This is the compatibility
bridge between the old first-order calculus and the new graded carrier. -/
theorem differential_zero_recovers_causalDifference
    (F : Configuration S → K)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    differential (S := S) (K := K) 0
        (ofConfigurationObservable F)
        (CausalEventCube.oneCube C e h)
      =
    causalDifference F C e h := by
  simp [differential, faceContribution,
    faceSign, ofConfigurationObservable,
    CausalEventCube.oneCube,
    CausalEventCube.lowerFace,
    CausalEventCube.upperFace,
    CausalEventCube.base,
    CausalEventCube.frame,
    CausalCubeFrame.after,
    causalDifference]


/-- Degree-zero differential on an arbitrary one-cube, not only the canonical
oneCube constructor. -/
theorem differential_zero_on_cube
    (F : Configuration S → K)
    (Q : CausalEventCube S 1) :
    differential (S := S) (K := K) 0
        (ofConfigurationObservable F) Q
      =
    F (Q.frame.after (0 : Fin 1)) -
      F Q.base := by
  simp [differential, faceContribution,
    faceSign, ofConfigurationObservable,
    CausalEventCube.lowerFace,
    CausalEventCube.upperFace,
    CausalEventCube.base,
    CausalEventCube.frame,
    CausalCubeFrame.after]

/-- First nontrivial cubical square-zero theorem.

For scalar observables, d₁ d₀ vanishes on every causal two-cube.  The proof
uses the actual concurrency face identities, so this is a geometric theorem
rather than an assumed complex law. -/
theorem differential_one_differential_zero
    (F : Configuration S → K)
    (Q : CausalEventCube S 2) :
    differential (S := S) (K := K) 1
        (differential (S := S) (K := K) 0
          (ofConfigurationObservable F)) Q
      =
    0 := by
  rw [differential_apply]
  rw [Fin.sum_univ_two]
  simp only [faceContribution, faceSign]
  rw [
    differential_zero_on_cube F
      (Q.upperFace (0 : Fin 2)),
    differential_zero_on_cube F
      (Q.lowerFace (0 : Fin 2)),
    differential_zero_on_cube F
      (Q.upperFace (1 : Fin 2)),
    differential_zero_on_cube F
      (Q.lowerFace (1 : Fin 2))
  ]
  rw [
    CausalEventCube.twoCube_upperUpper_endpoint Q,
    CausalEventCube.twoCube_lowerZero_after_eq_upperOne Q,
    CausalEventCube.twoCube_lowerOne_after_eq_upperZero Q
  ]
  norm_num [faceSign]
  ring

end CausalCubicalCochain
end CausalGeometry
