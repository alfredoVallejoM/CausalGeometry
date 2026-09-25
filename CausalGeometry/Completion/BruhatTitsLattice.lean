import CausalGeometry.Completion.BruhatTitsUniversalDegree
import CausalGeometry.Completion.LatticeGraph
import CausalGeometry.Cyclic.DirectedEdgeEquiv

namespace CausalGeometry

universe u v₁ v₂

/-- Exact lattice realization boundary for the universal Bruhat--Tits tree.

The source tree is already derived from the projective residue tower. The
target graph is independently built from homothety classes of actual O-lattices
in K^2 with q-index adjacency. A realization is therefore an isomorphism of
directed-edge systems, not a renaming of vertices. -/
structure BruhatTitsLatticeComparison
    {A : ℕ → Type u}
    [∀ n, CommRing (A n)]
    [∀ n, IsLocalRing (A n)]
    [∀ n, Fintype (A n)]
    {T : PrimePowerLocalRingTower A}
    (B : BruhatTitsBranchingContract T)
    (O : Type v₁) (K : Type v₂)
    [CommRing O] [Field K] [Algebra O K] where

  graphEquiv :
    DirectedEdgeEquiv
      B.directedEdgeSystem
      (RankTwoLattice.latticeDirectedEdgeSystem
        (O := O) (K := K) T.q)

namespace BruhatTitsLatticeComparison

variable
    {A : ℕ → Type u}
    [∀ n, CommRing (A n)]
    [∀ n, IsLocalRing (A n)]
    [∀ n, Fintype (A n)]
    {T : PrimePowerLocalRingTower A}
    {B : BruhatTitsBranchingContract T}
    {O : Type v₁} {K : Type v₂}
    [CommRing O] [Field K] [Algebra O K]
    (C : BruhatTitsLatticeComparison B O K)

/-- Homothety class corresponding to the distinguished tree root. -/
def rootClass :
    RankTwoLattice.HomothetyClass
      (O := O) (K := K) :=
  C.graphEquiv.vertexEquiv
    (.root :
      BruhatTitsUniversalGraph.Vertex
        (B := B))

/-- Homothety class corresponding to one projective sphere point. -/
def sphereClass
    (n : ℕ)
    (x : LocalProjectivePair.Line (A n)) :
    RankTwoLattice.HomothetyClass
      (O := O) (K := K) :=
  C.graphEquiv.vertexEquiv
    (.sphere n x :
      BruhatTitsUniversalGraph.Vertex
        (B := B))

/-- The projective/lattice vertex representation is injective at every fixed
depth because the global vertex comparison is an equivalence. -/
theorem sphereClass_injective
    (n : ℕ) :
    Function.Injective
      (C.sphereClass n) := by
  intro x y h
  have hvertex :
      (BruhatTitsUniversalGraph.Vertex
        (B := B)) := .sphere n x
  have hvertex' :
      (BruhatTitsUniversalGraph.Vertex
        (B := B)) := .sphere n y
  have hv :
      hvertex = hvertex' :=
    C.graphEquiv.vertexEquiv.injective h
  cases hv
  rfl

/-- Level-zero projective vertices are q-adjacent to the root lattice class. -/
theorem levelZero_adjacent_root
    (x : LocalProjectivePair.Line (A 0)) :
    RankTwoLattice.ClassAdjacent
        (O := O) (K := K) T.q
        (C.sphereClass 0 x)
        C.rootClass := by
  let e :=
    BruhatTitsUniversalGraph.parentEdge
      B 0 x
  let e' := C.graphEquiv.edgeEquiv e
  have hs :=
    C.graphEquiv.source_compat e
  have ht :=
    C.graphEquiv.target_compat e
  have hadj := e'.2.2
  change
    RankTwoLattice.ClassAdjacent T.q
      (C.graphEquiv.vertexEquiv
        (.sphere 0 x))
      (C.graphEquiv.vertexEquiv
        (.root :
          BruhatTitsUniversalGraph.Vertex
            (B := B)))
  rw [hs, ht]
  exact hadj

/-- Every deeper projective point is q-adjacent to its projective reduction
one level closer to the root. -/
theorem sphere_adjacent_parent
    (n : ℕ)
    (x :
      LocalProjectivePair.Line
        (A (n + 1))) :
    RankTwoLattice.ClassAdjacent
        (O := O) (K := K) T.q
        (C.sphereClass (n + 1) x)
        (C.sphereClass n
          (LocalProjectivePair.map
            (T.drop n) x)) := by
  let e :=
    BruhatTitsUniversalGraph.parentEdge
      B (n + 1) x
  let e' := C.graphEquiv.edgeEquiv e
  have hs :=
    C.graphEquiv.source_compat e
  have ht :=
    C.graphEquiv.target_compat e
  have hadj := e'.2.2
  change
    RankTwoLattice.ClassAdjacent T.q
      (C.graphEquiv.vertexEquiv
        (.sphere (n + 1) x))
      (C.graphEquiv.vertexEquiv
        (.sphere n
          (LocalProjectivePair.map
            (T.drop n) x)))
  rw [hs, ht]
  exact hadj

/-- Lattice outgoing stars inherit q+1 regularity from the independently
proved projective Bruhat--Tits tree. -/
theorem lattice_outgoing_natCard
    (v :
      BruhatTitsUniversalGraph.Vertex
        (B := B)) :
    Nat.card
        ((RankTwoLattice.latticeDirectedEdgeSystem
          (O := O) (K := K) T.q).Outgoing
          (C.graphEquiv.vertexEquiv v)) =
      T.q + 1 := by
  rw [← Nat.card_congr
    (C.graphEquiv.outgoingEquiv v)]
  exact B.outgoing_natCard v

/-- Non-backtracking successor multiplicities are also transported exactly by
the graph isomorphism. -/
theorem successor_natCard_eq
    (e :
      BruhatTitsUniversalGraph.OrientedEdge
        (B := B)) :
    Nat.card
        (B.directedEdgeSystem.Successor e) =
      Nat.card
        ((RankTwoLattice.latticeDirectedEdgeSystem
          (O := O) (K := K) T.q).Successor
          (C.graphEquiv.edgeEquiv e)) := by
  exact Nat.card_congr
    (C.graphEquiv.successorEquiv e)

end BruhatTitsLatticeComparison
end CausalGeometry
