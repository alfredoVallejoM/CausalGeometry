import CausalGeometry.Calculus.CubicalShuffleCup
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalCubicalCochain

/-- There is exactly one (0,0)-shuffle. -/
instance cubicalShuffleZeroZeroUnique :
    Unique (CubicalShuffle 0 0) where
  default :=
    identityShuffle 0 0
  uniq := by
    intro σ
    apply Subtype.ext
    apply Equiv.ext
    intro i
    exact Fin.elim0 i

@[simp] theorem inversionCount_zero_zero
    (σ : CubicalShuffle 0 0) :
    inversionCount σ.1 = 0 := by
  unfold inversionCount inversionPairs
  simp

variable {K : Type w} [Field K]

@[simp] theorem shuffleSign_zero_zero
    (σ : CubicalShuffle 0 0) :
    shuffleSign (K := K) σ = 1 := by
  simp [shuffleSign]

/-- In degree 0+0 the full shuffle sum has one term and is exactly the ordered
front/back product. -/
theorem serreCup_zero_zero
    (α β : CausalCubicalCochain S K 0) :
    serreCup 0 0 α β =
      orderedCup 0 0 α β := by
  funext Q
  simp [serreCup, shuffleCupTerm]

/-- Therefore configuration observables multiply pointwise under the full
Serre cup. -/
theorem serreCup_configuration_observables
    (F G : Configuration S → K) :
    serreCup 0 0
        (ofConfigurationObservable F)
        (ofConfigurationObservable G)
      =
    ofConfigurationObservable
      (fun C => F C * G C) := by
  rw [serreCup_zero_zero]
  exact orderedCup_configuration_observables F G

/-- Full-cup low-degree differential regression. -/
theorem differential_zero_serreCup_configuration
    (F G : Configuration S → K)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    differential (S := S) (K := K) 0
        (serreCup 0 0
          (ofConfigurationObservable F)
          (ofConfigurationObservable G))
        (CausalEventCube.oneCube C e h)
      =
    causalDifference
      (fun X => F X * G X)
      C e h := by
  rw [serreCup_zero_zero]
  exact
    differential_zero_orderedCup_configuration
      F G C e h

/-- The Serre cup recovers the existing chronological finite product rule in
the first differential. -/
theorem differential_zero_serreCup_product_rule
    (F G : Configuration S → K)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    differential (S := S) (K := K) 0
        (serreCup 0 0
          (ofConfigurationObservable F)
          (ofConfigurationObservable G))
        (CausalEventCube.oneCube C e h)
      =
    F (S.extend C e h) *
        causalDifference G C e h
      +
    causalDifference F C e h *
        G C := by
  rw [serreCup_zero_zero]
  exact
    differential_zero_orderedCup_product_rule
      F G C e h

end CausalCubicalCochain
end CausalGeometry
