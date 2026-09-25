import CausalGeometry.Completion.BruhatTitsUniversalDegree
import CausalGeometry.Cyclic.HashimotoSparsity
import CausalGeometry.Cyclic.NonbacktrackingPath

namespace CausalGeometry

universe u v

namespace BruhatTitsFiniteQuotient

variable
    {A : ℕ → Type u}
    [∀ n, CommRing (A n)]
    [∀ n, IsLocalRing (A n)]
    [∀ n, Fintype (A n)]
    {T : PrimePowerLocalRingTower A}
    (B : BruhatTitsBranchingContract T)

/-- Finite locally-bijective quotient of the universal Bruhat--Tits tree.

Global identifications are allowed and are exactly where nontrivial cycles may
appear. -/
abbrev Quotient :=
  FiniteDirectedEdgeQuotient.{u, v}
    B.directedEdgeSystem

variable (Q : Quotient (B := B))

noncomputable local instance :
    Fintype Q.QuotVertex :=
  Q.vertexFintype

noncomputable local instance :
    DecidableEq Q.QuotVertex :=
  Q.vertexDecEq

noncomputable local instance :
    Fintype Q.QuotEdge :=
  Q.edgeFintype

noncomputable local instance :
    DecidableEq Q.QuotEdge :=
  Q.edgeDecEq

/-- Every quotient vertex inherits the q+1 outgoing star of any lift. -/
theorem outgoing_natCard
    (v : Q.QuotVertex) :
    Nat.card
        (Q.finiteSystem.Outgoing v) =
      T.q + 1 := by
  rcases Q.covering.vertex_surjective v with
    ⟨x, hx⟩
  calc
    Nat.card
        (Q.finiteSystem.Outgoing v)
        =
      Nat.card
        (Q.finiteSystem.toDirected.Outgoing
          (Q.covering.vertexMap x)) := by
            rw [hx]
    _ =
      Nat.card
        (B.directedEdgeSystem.Outgoing x) := by
          exact
            (Nat.card_congr
              (Q.covering.outgoingEquiv x)).symm
    _ = T.q + 1 :=
      B.outgoing_natCard x

/-- Every oriented quotient edge has exactly q non-backtracking continuations. -/
theorem successor_natCard
    (e : Q.QuotEdge) :
    Nat.card
        (Q.finiteSystem.Successor e) =
      T.q := by
  rw [Q.finiteSystem.successor_natCard e,
    B.outgoing_natCard Q
      (Q.finiteSystem.target e)]
  omega

/-- Exact quotient Hashimoto state count. -/
theorem edge_natCard :
    Nat.card Q.QuotEdge =
      Nat.card Q.QuotVertex *
        (T.q + 1) := by
  exact
    Q.finiteSystem.edge_natCard_of_regular
      (T.q + 1)
      (B.outgoing_natCard Q)

/-- Exact sparse NNZ law for every finite Bruhat--Tits quotient. -/
theorem hashimoto_nnz_natCard :
    Nat.card
        Q.finiteSystem.HashimotoNonzero =
      Nat.card Q.QuotVertex *
        (T.q + 1) * T.q := by
  exact
    (Q.finiteSystem.qRegular_state_and_nnz
      T.q (B.outgoing_natCard Q)).2

/-- The finite quotient's stable transfer signature. -/
noncomputable def transferSignature :
    FiniteTransferSignature :=
  FiniteTransferSignature.ofHashimoto
    Q.finiteSystem

/-- Lifted quotient-cycle witness specialized to the universal Bruhat--Tits
tree. -/
abbrev CycleLift :=
  Q.covering.QuotientCycleLift

/-- Every lifted quotient cycle becomes a closed non-backtracking path in the
finite quotient graph. -/
theorem cycleLift_maps_closed
    (L : CycleLift (B := B) Q) :
    Q.finiteSystem.toDirected.NonbacktrackingPath
      (Q.covering.edgeMap L.startEdge)
      L.length
      (Q.covering.edgeMap L.startEdge) :=
  L.mapped_closedPath

/-- The universal source and finite quotient are locally indistinguishable:
all local branching data is inherited, while cycles can only arise from the
global noninjectivity allowed by the covering. -/
theorem local_branching_preserved
    (x : BruhatTitsUniversalGraph.Vertex
      (B := B)) :
    Nat.card
        (B.directedEdgeSystem.Outgoing x) =
      Nat.card
        (Q.finiteSystem.toDirected.Outgoing
          (Q.covering.vertexMap x)) := by
  exact Nat.card_congr
    (Q.covering.outgoingEquiv x)

end BruhatTitsFiniteQuotient
end CausalGeometry
