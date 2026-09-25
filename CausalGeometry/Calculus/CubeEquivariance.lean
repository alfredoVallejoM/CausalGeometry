import CausalGeometry.Foundation.EventSystemEquiv
import CausalGeometry.Calculus.CubeShift

namespace CausalGeometry

universe u₁ v₁ u₂ v₂ w

open EventSystem

variable
    {Event₁ : Type u₁} {Label₁ : Type v₁}
    {Event₂ : Type u₂} {Label₂ : Type v₂}
    {S₁ : EventSystem Event₁ Label₁}
    {S₂ : EventSystem Event₂ Label₂}

namespace EventSystemEquiv

variable (E : EventSystemEquiv S₁ S₂)

/-- Primitive causal-system equivalence transports every cube frame
index-by-index. -/
def mapCubeFrame
    {C : Configuration S₁}
    {ι : Type w}
    (Q : CausalCubeFrame S₁ C ι) :
    CausalCubeFrame S₂
      (E.mapConfiguration C) ι where
  event := fun i =>
    E.eventEquiv (Q.event i)

  enabled := by
    intro i
    exact
      (E.enabled_iff C (Q.event i)).2
        (Q.enabled i)

  injective := by
    intro i j h
    apply Q.injective
    exact E.eventEquiv.injective h

  independent := by
    intro i j hij
    have hQ := Q.independent hij
    refine ⟨?_, ?_, ?_⟩
    · intro hp
      exact hQ.1
        ((E.precedes_iff
          (Q.event i)
          (Q.event j)).1 hp)
    · intro hp
      exact hQ.2.1
        ((E.precedes_iff
          (Q.event j)
          (Q.event i)).1 hp)
    · intro hc
      exact hQ.2.2
        ((E.conflict_iff
          (Q.event i)
          (Q.event j)).1 hc)

/-- Mapping a cube direction agrees with the canonical direction in the mapped
cube. -/
theorem directionEquiv_cube
    {C : Configuration S₁}
    {ι : Type w}
    (Q : CausalCubeFrame S₁ C ι)
    (i : ι) :
    E.directionEquiv C (Q.direction i) =
      (E.mapCubeFrame Q).direction i := by
  apply EventDirection.ext
  rfl

/-- Mapping the configuration after one cube direction is the configuration
after the corresponding mapped direction. -/
theorem map_cube_after
    {C : Configuration S₁}
    {ι : Type w}
    (Q : CausalCubeFrame S₁ C ι)
    (i : ι) :
    E.mapConfiguration (Q.after i) =
      (E.mapCubeFrame Q).after i := by
  exact
    E.map_extend C
      (Q.event i) (Q.enabled i)

/-- Concurrency diamonds are proof objects over fixed base/events, hence
unique once their type is fixed. -/
theorem concurrencyDiamond_eq
    {Event : Type*} {Label : Type*}
    {S : EventSystem Event Label}
    {C : Configuration S}
    {e f : Event}
    (d₁ d₂ : ConcurrencyDiamond C e f) :
    d₁ = d₂ := by
  cases d₁
  cases d₂
  rfl

/-- A face diamond of a cube transports to the corresponding face diamond of
the mapped cube. -/
theorem map_cube_diamond
    {C : Configuration S₁}
    {ι : Type w}
    (Q : CausalCubeFrame S₁ C ι)
    (i j : ι)
    (hij : i ≠ j) :
    E.mapDiamond (Q.diamond hij) =
      (E.mapCubeFrame Q).diamond hij := by
  exact concurrencyDiamond_eq _ _

/-- A shifted face diamond also transports correctly.  The only dependent
step is identifying the two equivalent intermediate configurations. -/
theorem map_cube_diamondAfter_value
    {K : Type*}
    (ω : CausalTwoForm S₂ K)
    {C : Configuration S₁}
    {ι : Type w}
    (Q : CausalCubeFrame S₁ C ι)
    (i j k : ι)
    (hji : j ≠ i)
    (hki : k ≠ i)
    (hjk : j ≠ k) :
    ω.value
        (E.mapDiamond
          (Q.diamondAfter i j k
            hji hki hjk))
      =
    ω.value
      ((E.mapCubeFrame Q).diamondAfter
        i j k hji hki hjk) := by
  have hcfg :=
    E.map_cube_after Q i
  cases hcfg
  congr 1
  exact concurrencyDiamond_eq _ _

/-- Base face values transport identically. -/
theorem map_cube_diamond_value
    {K : Type*}
    (ω : CausalTwoForm S₂ K)
    {C : Configuration S₁}
    {ι : Type w}
    (Q : CausalCubeFrame S₁ C ι)
    (i j : ι)
    (hij : i ≠ j) :
    ω.value
        (E.mapDiamond
          (Q.diamond hij))
      =
    ω.value
      ((E.mapCubeFrame Q).diamond hij) := by
  rw [E.map_cube_diamond Q i j hij]

end EventSystemEquiv
end CausalGeometry
