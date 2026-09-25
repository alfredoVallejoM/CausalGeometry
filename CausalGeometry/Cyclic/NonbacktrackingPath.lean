import CausalGeometry.Cyclic.DirectedEdgeCovering

namespace CausalGeometry

universe u₁ u₂

namespace DirectedEdgeSystem

variable {V E : Type u₁}
variable (G : DirectedEdgeSystem V E)

/-- A non-backtracking path is measured by number of edge-to-edge
transitions. Length zero stays on the same oriented edge. -/
inductive NonbacktrackingPath :
    E → ℕ → E → Prop
  | refl (e : E) :
      NonbacktrackingPath e 0 e
  | step {e f g : E} {n : ℕ}
      (hef : G.Nonbacktracking e f)
      (hfg : NonbacktrackingPath f n g) :
      NonbacktrackingPath e (n + 1) g

namespace NonbacktrackingPath

theorem one
    {e f : E}
    (h : G.Nonbacktracking e f) :
    G.NonbacktrackingPath e 1 f := by
  simpa using
    NonbacktrackingPath.step h
      (NonbacktrackingPath.refl f)

theorem append
    {e f g : E}
    {m n : ℕ}
    (h₁ : G.NonbacktrackingPath e m f)
    (h₂ : G.NonbacktrackingPath f n g) :
    G.NonbacktrackingPath e (m + n) g := by
  induction h₁ with
  | refl e =>
      simpa using h₂
  | @step e h f k heh hh ih =>
      simpa [Nat.add_assoc] using
        NonbacktrackingPath.step heh ih

/-- Reversal turns a path around. -/
theorem reverse
    {e f : E}
    {n : ℕ}
    (h : G.NonbacktrackingPath e n f) :
    G.NonbacktrackingPath
      (G.reverse f) n (G.reverse e) := by
  induction h with
  | refl e =>
      exact NonbacktrackingPath.refl _
  | @step e f g n hef hfg ih =>
      have hrev :
          G.Nonbacktracking
            (G.reverse f) (G.reverse e) := by
        constructor
        · rw [G.target_reverse, G.source_reverse]
          exact hef.1.symm
        · intro hh
          apply hef.2
          have :=
            congrArg G.reverse hh
          simpa [G.reverse_involutive] using this
      have hstep :
          G.NonbacktrackingPath
            (G.reverse f) 1
            (G.reverse e) :=
        NonbacktrackingPath.one G hrev
      have happ :=
        NonbacktrackingPath.append G ih hstep
      simpa [Nat.add_comm] using happ

end NonbacktrackingPath
end DirectedEdgeSystem

namespace DirectedEdgeCovering

variable
    {V₁ E₁ : Type u₁}
    {V₂ E₂ : Type u₂}
    {G : DirectedEdgeSystem V₁ E₁}
    {H : DirectedEdgeSystem V₂ E₂}
    (C : DirectedEdgeCovering G H)

/-- Coverings transport every non-backtracking path. -/
theorem map_nonbacktrackingPath
    {e f : E₁}
    {n : ℕ}
    (h : G.NonbacktrackingPath e n f) :
    H.NonbacktrackingPath
      (C.edgeMap e) n (C.edgeMap f) := by
  induction h with
  | refl e =>
      exact DirectedEdgeSystem.NonbacktrackingPath.refl _
  | @step e f g n hef hfg ih =>
      exact
        DirectedEdgeSystem.NonbacktrackingPath.step
          (C.map_nonbacktracking hef) ih

/-- A lifted path closes in the quotient when its endpoint edge is identified
with its starting edge. The source path itself need not be closed. -/
def ClosesInQuotient
    (e : E₁) (n : ℕ) (f : E₁) : Prop :=
  G.NonbacktrackingPath e n f ∧
    C.edgeMap f = C.edgeMap e

/-- Every lifted quotient-closing segment becomes an actual closed
non-backtracking path downstairs. -/
theorem map_closedPath
    {e f : E₁}
    {n : ℕ}
    (h : C.ClosesInQuotient e n f) :
    H.NonbacktrackingPath
      (C.edgeMap e) n (C.edgeMap e) := by
  have hp := C.map_nonbacktrackingPath h.1
  simpa [h.2] using hp

/-- A genuine global identification witness: the source segment is open but
its image is a closed quotient path. -/
structure QuotientCycleLift where
  startEdge : E₁
  endEdge : E₁
  length : ℕ

  positive : 0 < length

  path :
    G.NonbacktrackingPath
      startEdge length endEdge

  closes :
    C.edgeMap endEdge =
      C.edgeMap startEdge

  /-- Excludes cycles already present in the universal source. -/
  globallySeparated :
    endEdge ≠ startEdge

namespace QuotientCycleLift

theorem mapped_closedPath
    (L : C.QuotientCycleLift) :
    H.NonbacktrackingPath
      (C.edgeMap L.startEdge)
      L.length
      (C.edgeMap L.startEdge) := by
  exact C.map_closedPath ⟨L.path, L.closes⟩

end QuotientCycleLift
end DirectedEdgeCovering
end CausalGeometry
