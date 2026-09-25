import CausalGeometry.Completion.BruhatTitsQuotient
import CausalGeometry.Cyclic.DirectedEdgeAction

namespace CausalGeometry

universe u v g

/-- Arithmetic realization of a finite Bruhat--Tits quotient as Γ\T.

The finite quotient itself already certifies local covering geometry. This
structure adds a group action on the universal tree and proves that quotient
fibers are exactly Γ-orbits. -/
structure BruhatTitsArithmeticQuotient
    (Γ : Type g) [Group Γ]
    {A : ℕ → Type u}
    [∀ n, CommRing (A n)]
    [∀ n, IsLocalRing (A n)]
    [∀ n, Fintype (A n)]
    {T : PrimePowerLocalRingTower A}
    (B : BruhatTitsBranchingContract T)
    [MulAction Γ
      (BruhatTitsUniversalGraph.Vertex
        (B := B))]
    [MulAction Γ
      (BruhatTitsUniversalGraph.OrientedEdge
        (B := B))] where

  quotient :
    BruhatTitsFiniteQuotient.Quotient
      (B := B)

  action :
    DirectedEdgeGroupAction Γ
      B.directedEdgeSystem

  vertex_orbit_iff :
    ∀ x y,
      quotient.covering.vertexMap x =
          quotient.covering.vertexMap y ↔
        ∃ γ : Γ, γ • x = y

  edge_orbit_iff :
    ∀ e f,
      quotient.covering.edgeMap e =
          quotient.covering.edgeMap f ↔
        ∃ γ : Γ, γ • e = f

namespace BruhatTitsArithmeticQuotient

variable
    {Γ : Type g} [Group Γ]
    {A : ℕ → Type u}
    [∀ n, CommRing (A n)]
    [∀ n, IsLocalRing (A n)]
    [∀ n, Fintype (A n)]
    {T : PrimePowerLocalRingTower A}
    {B : BruhatTitsBranchingContract T}
    [MulAction Γ
      (BruhatTitsUniversalGraph.Vertex
        (B := B))]
    [MulAction Γ
      (BruhatTitsUniversalGraph.OrientedEdge
        (B := B))]
    (Q : BruhatTitsArithmeticQuotient.{u, v, g}
      Γ B)

noncomputable local instance :
    Fintype Q.quotient.QuotVertex :=
  Q.quotient.vertexFintype

noncomputable local instance :
    DecidableEq Q.quotient.QuotVertex :=
  Q.quotient.vertexDecEq

noncomputable local instance :
    Fintype Q.quotient.QuotEdge :=
  Q.quotient.edgeFintype

noncomputable local instance :
    DecidableEq Q.quotient.QuotEdge :=
  Q.quotient.edgeDecEq

/-- Assemble the generic orbit-covering interface. -/
def orbitCovering :
    OrbitDirectedEdgeCovering
      Γ B.directedEdgeSystem
      Q.quotient.finiteSystem.toDirected where
  action := Q.action
  covering := Q.quotient.covering
  vertex_orbit_iff := Q.vertex_orbit_iff
  edge_orbit_iff := Q.edge_orbit_iff

/-- Stable Hashimoto signature of Γ\T. -/
noncomputable def transferSignature :
    FiniteTransferSignature :=
  FiniteTransferSignature.ofHashimoto
    Q.quotient.finiteSystem

/-- Exact state count inherited from q+1 regularity. -/
theorem edge_natCard :
    Nat.card Q.quotient.QuotEdge =
      Nat.card Q.quotient.QuotVertex *
        (T.q + 1) :=
  BruhatTitsFiniteQuotient.edge_natCard
    B Q.quotient

/-- Exact sparse Hashimoto size for Γ\T. -/
theorem hashimoto_nnz_natCard :
    Nat.card
        Q.quotient.finiteSystem.HashimotoNonzero =
      Nat.card Q.quotient.QuotVertex *
        (T.q + 1) * T.q :=
  BruhatTitsFiniteQuotient.hashimoto_nnz_natCard
    B Q.quotient

/-- A quotient-cycle lift determines a nontrivial Γ-element moving the lifted
start edge to the lifted endpoint. -/
theorem exists_nontrivial_deck
    (L :
      Q.quotient.covering.QuotientCycleLift) :
    ∃ γ : Γ,
      γ ≠ 1 ∧
      γ • L.startEdge =
        L.endEdge :=
  Q.orbitCovering
    |>.exists_nontrivial_deck_of_cycleLift L

/-- Canonical chosen deck witness for a lifted quotient cycle. -/
noncomputable def deckCycleWitness
    (L :
      Q.quotient.covering.QuotientCycleLift) :
    Q.orbitCovering.DeckCycleWitness :=
  Q.orbitCovering.deckCycleWitness L

/-- Conjugacy class associated to a chosen deck-cycle witness. -/
def deckConjClass
    (W : Q.orbitCovering.DeckCycleWitness) :
    ConjClasses Γ :=
  Q.orbitCovering.deckConjClass W

/-- Translating the lift conjugates the deck element and therefore leaves its
conjugacy class unchanged. -/
theorem deckConjClass_lift_invariant
    (δ : Γ)
    (W : Q.orbitCovering.DeckCycleWitness) :
    Q.deckConjClass
        (Q.orbitCovering.conjugateDeckCycleWitness
          δ W) =
      Q.deckConjClass W :=
  Q.orbitCovering.deckConjClass_conjugate
    δ W

end BruhatTitsArithmeticQuotient
end CausalGeometry
