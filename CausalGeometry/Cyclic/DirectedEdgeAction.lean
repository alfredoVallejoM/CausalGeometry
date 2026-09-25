import CausalGeometry.Cyclic.NonbacktrackingPath
import Mathlib.GroupTheory.GroupAction.Basic

namespace CausalGeometry

universe u g

/-- Group action by automorphisms of a directed-edge system. -/
structure DirectedEdgeGroupAction
    (Γ : Type g) [Group Γ]
    {V E : Type u}
    [MulAction Γ V] [MulAction Γ E]
    (G : DirectedEdgeSystem V E) : Prop where

  source_smul :
    ∀ γ e,
      G.source (γ • e) =
        γ • G.source e

  target_smul :
    ∀ γ e,
      G.target (γ • e) =
        γ • G.target e

  reverse_smul :
    ∀ γ e,
      G.reverse (γ • e) =
        γ • G.reverse e

namespace DirectedEdgeGroupAction

variable
    {Γ : Type g} [Group Γ]
    {V E : Type u}
    [MulAction Γ V] [MulAction Γ E]
    {G : DirectedEdgeSystem V E}
    (A : DirectedEdgeGroupAction Γ G)

/-- The action preserves non-backtracking adjacency exactly. -/
theorem nonbacktracking_smul_iff
    (γ : Γ) (e f : E) :
    G.Nonbacktracking (γ • e) (γ • f) ↔
      G.Nonbacktracking e f := by
  constructor
  · intro h
    constructor
    · have hinc :=
        congrArg (γ⁻¹ • ·) h.1
      simpa [A.source_smul, A.target_smul] using hinc
    · intro hrev
      apply h.2
      rw [hrev, A.reverse_smul]
  · intro h
    constructor
    · rw [A.target_smul, A.source_smul,
        h.1]
    · intro hrev
      apply h.2
      have hh :=
        congrArg (γ⁻¹ • ·) hrev
      simpa [A.reverse_smul] using hh

/-- The action transports all finite non-backtracking paths. -/
theorem path_smul
    (γ : Γ)
    {e f : E} {n : ℕ}
    (h : G.NonbacktrackingPath e n f) :
    G.NonbacktrackingPath
      (γ • e) n (γ • f) := by
  induction h with
  | refl e =>
      exact DirectedEdgeSystem.NonbacktrackingPath.refl _
  | @step e f z n hef hfz ih =>
      exact
        DirectedEdgeSystem.NonbacktrackingPath.step
          ((A.nonbacktracking_smul_iff γ e f).mpr hef)
          ih

end DirectedEdgeGroupAction

/-- A quotient covering whose fibers are exactly group orbits.

This is the formal Γ\T boundary: local geometry is supplied by the covering;
global identifications are certified by orbit equivalence. -/
structure OrbitDirectedEdgeCovering
    (Γ : Type g) [Group Γ]
    {V E : Type u}
    [MulAction Γ V] [MulAction Γ E]
    (G : DirectedEdgeSystem V E)
    {VQ EQ : Type*}
    (H : DirectedEdgeSystem VQ EQ) where

  action :
    DirectedEdgeGroupAction Γ G

  covering :
    DirectedEdgeCovering G H

  vertex_orbit_iff :
    ∀ x y,
      covering.vertexMap x =
          covering.vertexMap y ↔
        ∃ γ : Γ, γ • x = y

  edge_orbit_iff :
    ∀ e f,
      covering.edgeMap e =
          covering.edgeMap f ↔
        ∃ γ : Γ, γ • e = f

namespace OrbitDirectedEdgeCovering

variable
    {Γ : Type g} [Group Γ]
    {V E : Type u}
    [MulAction Γ V] [MulAction Γ E]
    {G : DirectedEdgeSystem V E}
    {VQ EQ : Type*}
    {H : DirectedEdgeSystem VQ EQ}
    (Q : OrbitDirectedEdgeCovering Γ G H)

/-- A quotient-closing lifted segment determines a deck transformation that
moves its starting oriented edge to its endpoint. -/
theorem exists_deck_of_closes
    {e f : E}
    {n : ℕ}
    (h :
      Q.covering.ClosesInQuotient e n f) :
    ∃ γ : Γ, γ • e = f := by
  exact
    (Q.edge_orbit_iff e f).mp h.2.symm

/-- If the lifted endpoints are distinct, the deck transformation can be
chosen nontrivial. -/
theorem exists_nontrivial_deck_of_cycleLift
    (L : Q.covering.QuotientCycleLift) :
    ∃ γ : Γ,
      γ ≠ 1 ∧
      γ • L.startEdge =
        L.endEdge := by
  rcases
      (Q.edge_orbit_iff
        L.startEdge L.endEdge).mp
        L.closes.symm with
    ⟨γ, hγ⟩
  refine ⟨γ, ?_, hγ⟩
  intro h1
  apply L.globallySeparated
  simpa [h1] using hγ.symm

/-- Typed witness combining a quotient cycle lift with one nontrivial deck
transformation responsible for its closure. -/
structure DeckCycleWitness where
  lift : Q.covering.QuotientCycleLift
  deck : Γ
  deck_ne_one : deck ≠ 1
  moves_start :
    deck • lift.startEdge =
      lift.endEdge

/-- Every globally separated quotient-cycle lift admits a deck witness. -/
noncomputable def deckCycleWitness
    (L : Q.covering.QuotientCycleLift) :
    Q.DeckCycleWitness := by
  classical
  let h :=
    Q.exists_nontrivial_deck_of_cycleLift L
  exact
    { lift := L
      deck := Classical.choose h
      deck_ne_one :=
        (Classical.choose_spec h).1
      moves_start :=
        (Classical.choose_spec h).2 }

end OrbitDirectedEdgeCovering
end CausalGeometry
