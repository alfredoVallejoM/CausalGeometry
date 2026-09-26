import CausalGeometry.Foundation.EventSystemEquiv
import CausalGeometry.History.Path
import Mathlib.Tactic

namespace CausalGeometry

universe u₁ v₁ u₂ v₂

open EventSystem

variable
    {Event₁ : Type u₁} {Label₁ : Type v₁}
    {Event₂ : Type u₂} {Label₂ : Type v₂}
    {S₁ : EventSystem Event₁ Label₁}
    {S₂ : EventSystem Event₂ Label₂}

namespace CausalPath

/-- Change only the declared start configuration of a path along an equality. -/
def castStart
    {C C' D : Configuration S₁}
    (h : C = C')
    (p : CausalPath S₁ C D) :
    CausalPath S₁ C' D :=
  h ▸ p

/-- Change only the declared terminal configuration of a path along an equality. -/
def castEnd
    {C D D' : Configuration S₁}
    (h : D = D')
    (p : CausalPath S₁ C D) :
    CausalPath S₁ C D' :=
  h ▸ p

@[simp] theorem castStart_rfl
    {C D : Configuration S₁}
    (p : CausalPath S₁ C D) :
    p.castStart rfl = p :=
  rfl

@[simp] theorem castEnd_rfl
    {C D : Configuration S₁}
    (p : CausalPath S₁ C D) :
    p.castEnd rfl = p :=
  rfl

end CausalPath

namespace EventSystemEquiv

/-- Transport a complete derived causal path through a primitive event-system
equivalence.

The only non-definitional point is the recursive start of the tail: mapping an
extension is propositionally equal to extending the mapped configuration.
The existing map_extend theorem supplies exactly that cast. -/
def mapPath
    (E : EventSystemEquiv S₁ S₂) :
    {C D : Configuration S₁} →
      CausalPath S₁ C D →
        CausalPath S₂
          (E.mapConfiguration C)
          (E.mapConfiguration D)
  | C, _, .nil _ =>
      .nil (E.mapConfiguration C)
  | C, D, .step e h tail =>
      let h₂ :
          S₂.Enabled
            (E.mapConfiguration C)
            (E.eventEquiv e) :=
        (E.enabled_iff C e).2 h

      let mappedTail₀ :=
        E.mapPath tail

      let mappedTail :
          CausalPath S₂
            (S₂.extend
              (E.mapConfiguration C)
              (E.eventEquiv e)
              h₂)
            (E.mapConfiguration D) :=
        mappedTail₀.castStart
          (E.map_extend C e h)

      .step
        (E.eventEquiv e)
        h₂
        mappedTail

/-- Path length is presentation invariant. -/
theorem mapPath_length
    (E : EventSystemEquiv S₁ S₂)
    {C D : Configuration S₁}
    (p : CausalPath S₁ C D) :
    (E.mapPath p).length = p.length := by
  induction p with
  | nil =>
      rfl
  | step e h tail ih =>
      dsimp [mapPath]
      have hm := E.map_extend _ e h
      cases hm
      simp [CausalPath.length, ih,
        CausalPath.castStart]

/-- Identity event-system equivalence acts trivially on causal paths. -/
theorem refl_mapPath
    {C D : Configuration S₁}
    (p : CausalPath S₁ C D) :
    (EventSystemEquiv.refl S₁).mapPath p = p := by
  induction p with
  | nil =>
      rfl
  | step e h tail ih =>
      simp [mapPath, ih,
        EventSystemEquiv.refl_mapConfiguration,
        EventSystemEquiv.map_extend,
        CausalPath.castStart]

end EventSystemEquiv
end CausalGeometry
