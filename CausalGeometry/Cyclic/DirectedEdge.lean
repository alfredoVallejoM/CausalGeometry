import CausalGeometry.Cyclic.Hashimoto

namespace CausalGeometry

universe u

/-- Directed-edge system without any global finiteness assumption.

This is the correct source notion for universal trees and their finite
quotients. -/
structure DirectedEdgeSystem
    (Vertex Edge : Type u) where
  source : Edge → Vertex
  target : Edge → Vertex
  reverse : Edge → Edge

  reverse_involutive :
    Function.Involutive reverse

  source_reverse :
    ∀ e, source (reverse e) = target e

  target_reverse :
    ∀ e, target (reverse e) = source e

  reverse_ne :
    ∀ e, reverse e ≠ e

namespace DirectedEdgeSystem

variable {Vertex Edge : Type u}
variable (G : DirectedEdgeSystem Vertex Edge)

/-- Non-backtracking adjacency in an arbitrary directed-edge system. -/
def Nonbacktracking (e f : Edge) : Prop :=
  G.target e = G.source f ∧
    f ≠ G.reverse e

/-- Oriented edges leaving one vertex. -/
def Outgoing (v : Vertex) :=
  {e : Edge // G.source e = v}

/-- Oriented edges entering one vertex. -/
def Incoming (v : Vertex) :=
  {e : Edge // G.target e = v}

/-- Non-backtracking successors of one oriented edge. -/
def Successor (e : Edge) :=
  {f : Edge // G.Nonbacktracking e f}

/-- Reversal converts outgoing edges at v to incoming edges at v. -/
def reverseOutgoingEquivIncoming (v : Vertex) :
    G.Outgoing v ≃ G.Incoming v where
  toFun := fun e =>
    ⟨G.reverse e.1, by
      rw [G.target_reverse, e.2]⟩
  invFun := fun e =>
    ⟨G.reverse e.1, by
      rw [G.source_reverse, e.2]⟩
  left_inv := by
    intro e
    apply Subtype.ext
    exact G.reverse_involutive e.1
  right_inv := by
    intro e
    apply Subtype.ext
    exact G.reverse_involutive e.1

/-- The immediate reverse of e is an outgoing edge at target(e). -/
def reverseAsOutgoing (e : Edge) :
    G.Outgoing (G.target e) :=
  ⟨G.reverse e, G.source_reverse e⟩

/-- Successors are precisely outgoing edges at target(e), except the immediate
reverse edge. -/
def successorEquivOutgoingNeReverse
    (e : Edge) :
    G.Successor e ≃
      {f : G.Outgoing (G.target e) //
        f ≠ G.reverseAsOutgoing e} where
  toFun := fun f => by
    refine ⟨⟨f.1, f.2.1.symm⟩, ?_⟩
    intro h
    apply f.2.2
    exact congrArg Subtype.val h
  invFun := fun f => by
    refine ⟨f.1.1, ?_⟩
    constructor
    · exact f.1.2.symm
    · intro h
      apply f.2
      apply Subtype.ext
      exact h
  left_inv := by
    intro f
    apply Subtype.ext
    rfl
  right_inv := by
    intro f
    apply Subtype.ext
    rfl

end DirectedEdgeSystem

namespace FiniteDirectedEdgeSystem

variable
    {Vertex Edge : Type u}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]

/-- Forget global finiteness while preserving all directed-edge structure. -/
def toDirected
    (G : FiniteDirectedEdgeSystem Vertex Edge) :
    DirectedEdgeSystem Vertex Edge where
  source := G.source
  target := G.target
  reverse := G.reverse
  reverse_involutive := G.reverse_involutive
  source_reverse := G.source_reverse
  target_reverse := G.target_reverse
  reverse_ne := G.reverse_ne

@[simp] theorem toDirected_nonbacktracking
    (G : FiniteDirectedEdgeSystem Vertex Edge)
    (e f : Edge) :
    G.toDirected.Nonbacktracking e f ↔
      G.Nonbacktracking e f :=
  Iff.rfl

end FiniteDirectedEdgeSystem
end CausalGeometry
