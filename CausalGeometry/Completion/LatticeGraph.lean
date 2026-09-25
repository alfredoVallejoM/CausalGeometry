import CausalGeometry.Completion.RankTwoLattice
import CausalGeometry.Cyclic.DirectedEdge
import Mathlib.LinearAlgebra.Quotient.Defs

namespace CausalGeometry

universe u v

namespace RankTwoLattice

variable
    {O : Type u} {K : Type v}
    [CommRing O] [Field K] [Algebra O K]

/-- One oriented lattice refinement of residual index q.

The smaller lattice M lies inside L and the finite additive/module quotient
L/M has exactly q elements. Finiteness is encoded by Nat.card rather than
assumed globally for arbitrary lattice quotients. -/
structure IndexStep
    (q : ℕ)
    (L M : RankTwoLattice O K) : Prop where
  le :
    M.carrier ≤ L.carrier

  quotient_card :
    Nat.card
        (L.carrier ⧸
          M.carrier.submoduleOf L.carrier) =
      q

namespace IndexStep

variable {q : ℕ}
variable {L M : RankTwoLattice O K}

theorem ne_of_card_gt_one
    (h : IndexStep q L M)
    (hq : 1 < q) :
    L ≠ M := by
  intro hLM
  subst M
  have htop :
      L.carrier.submoduleOf L.carrier =
        ⊤ := by
    exact
      (Submodule.submoduleOf_eq_top).2 le_rfl
  rw [htop] at h
  have hcard :
      Nat.card
          (L.carrier ⧸
            (⊤ : Submodule O L.carrier)) =
        1 := by
    simp
  omega

end IndexStep

/-- Two homothety classes are q-adjacent if they admit representatives joined
by one q-index refinement in either orientation.

The use of representatives makes the relation intrinsically a relation on
homothety classes; no unproved statement that index is invariant under an
arbitrary independent rescaling of the two representatives is needed. -/
def ClassAdjacent
    (q : ℕ)
    (x y : HomothetyClass (O := O) (K := K)) : Prop :=
  ∃ L M : RankTwoLattice O K,
    classOf L = x ∧
      classOf M = y ∧
      (IndexStep q L M ∨
        IndexStep q M L)

theorem classAdjacent_symm
    {q : ℕ}
    {x y : HomothetyClass (O := O) (K := K)}
    (h : ClassAdjacent q x y) :
    ClassAdjacent q y x := by
  rcases h with
    ⟨L, M, hx, hy, hLM | hML⟩
  · exact
      ⟨M, L, hy, hx, Or.inr hLM⟩
  · exact
      ⟨M, L, hy, hx, Or.inl hML⟩

/-- Oriented edges of the q-index lattice graph.

Self-edges are excluded explicitly; in true DVR models q>1 also makes this
follow from the index condition once suitable representatives are chosen. -/
abbrev OrientedClassEdge
    (q : ℕ) :=
  {p :
      HomothetyClass (O := O) (K := K) ×
        HomothetyClass (O := O) (K := K) //
    p.1 ≠ p.2 ∧
      ClassAdjacent q p.1 p.2}

namespace OrientedClassEdge

variable {q : ℕ}

def source
    (e : OrientedClassEdge
      (O := O) (K := K) q) :
    HomothetyClass (O := O) (K := K) :=
  e.1.1

def target
    (e : OrientedClassEdge
      (O := O) (K := K) q) :
    HomothetyClass (O := O) (K := K) :=
  e.1.2

def reverse
    (e : OrientedClassEdge
      (O := O) (K := K) q) :
    OrientedClassEdge (O := O) (K := K) q :=
  ⟨(e.1.2, e.1.1),
    ⟨e.2.1.symm,
      classAdjacent_symm e.2.2⟩⟩

@[simp] theorem reverse_reverse
    (e : OrientedClassEdge
      (O := O) (K := K) q) :
    reverse (reverse e) = e := by
  apply Subtype.ext
  rcases e with ⟨⟨x, y⟩, h⟩
  rfl

@[simp] theorem source_reverse
    (e : OrientedClassEdge
      (O := O) (K := K) q) :
    source (reverse e) =
      target e :=
  rfl

@[simp] theorem target_reverse
    (e : OrientedClassEdge
      (O := O) (K := K) q) :
    target (reverse e) =
      source e :=
  rfl

theorem reverse_ne
    (e : OrientedClassEdge
      (O := O) (K := K) q) :
    reverse e ≠ e := by
  intro h
  have hs :=
    congrArg source h
  change e.1.2 = e.1.1 at hs
  exact e.2.1 hs.symm

end OrientedClassEdge

/-- Directed-edge system carried by homothety classes and q-index lattice
refinements. -/
def latticeDirectedEdgeSystem
    (q : ℕ) :
    DirectedEdgeSystem
      (HomothetyClass (O := O) (K := K))
      (OrientedClassEdge (O := O) (K := K) q) where
  source :=
    OrientedClassEdge.source
  target :=
    OrientedClassEdge.target
  reverse :=
    OrientedClassEdge.reverse
  reverse_involutive :=
    OrientedClassEdge.reverse_reverse
  source_reverse :=
    OrientedClassEdge.source_reverse
  target_reverse :=
    OrientedClassEdge.target_reverse
  reverse_ne :=
    OrientedClassEdge.reverse_ne

end RankTwoLattice
end CausalGeometry
