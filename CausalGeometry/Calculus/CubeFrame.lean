import CausalGeometry.History.Trace

namespace CausalGeometry

universe u v w
open EventSystem

variable {Event : Type u} {Label : Type v}

/-- A finite- or infinite-indexed frame of pairwise concurrent primitive-event
directions available at one derived configuration.

This is the combinatorial carrier of a causal cube. Executions and faces are
derived from the event family rather than added to primitive ontology. -/
structure CausalCubeFrame
    (S : EventSystem Event Label)
    (C : Configuration S)
    (ι : Type w) where
  event : ι → Event
  enabled : ∀ i, S.Enabled C (event i)
  injective : Function.Injective event
  independent :
    ∀ {i j}, i ≠ j →
      ¬ S.precedes (event i) (event j) ∧
      ¬ S.precedes (event j) (event i) ∧
      ¬ S.conflict (event i) (event j)

namespace CausalCubeFrame

variable {S : EventSystem Event Label}
variable {C : Configuration S} {ι : Type w}

/-- Any two distinct directions in a cube frame determine a genuine
concurrency diamond. -/
def diamond
    (Q : CausalCubeFrame S C ι)
    {i j : ι} (hij : i ≠ j) :
    ConcurrencyDiamond C (Q.event i) (Q.event j) where
  concurrent := by
    have h := Q.independent hij
    exact ⟨Q.enabled i, Q.enabled j, h.1, h.2.1, h.2.2,
      Q.injective.ne hij⟩

/-- Delete one direction to obtain a codimension-one combinatorial face. -/
def face
    (Q : CausalCubeFrame S C ι)
    (i : ι) :
    CausalCubeFrame S C {j : ι // j ≠ i} where
  event := fun j => Q.event j.1
  enabled := fun j => Q.enabled j.1
  injective := by
    intro j k h
    apply Subtype.ext
    exact Q.injective h
  independent := by
    intro j k hjk
    have hval : j.1 ≠ k.1 := by
      intro h
      apply hjk
      exact Subtype.ext h
    exact Q.independent hval

/-- Restrict a cube frame along any injective reindexing. -/
def reindex
    {κ : Type*}
    (Q : CausalCubeFrame S C ι)
    (f : κ → ι)
    (hf : Function.Injective f) :
    CausalCubeFrame S C κ where
  event := Q.event ∘ f
  enabled := fun k => Q.enabled (f k)
  injective := Q.injective.comp hf
  independent := by
    intro i j hij
    apply Q.independent
    exact hf.ne hij

end CausalCubeFrame
end CausalGeometry
