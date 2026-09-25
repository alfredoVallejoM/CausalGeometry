import CausalGeometry.Cyclic.DirectedEdge
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

namespace CausalGeometry

universe u

namespace FiniteDirectedEdgeSystem

variable
    {Vertex Edge : Type u}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    (G : FiniteDirectedEdgeSystem Vertex Edge)

abbrev Directed :=
  G.toDirected

/-- Non-backtracking successors of one finite oriented edge. -/
abbrev Successor (e : Edge) :=
  G.Directed.Successor e

/-- Outgoing star at one finite vertex. -/
abbrev Outgoing (v : Vertex) :=
  G.Directed.Outgoing v

/-- Successor count is degree(target)-1 because immediate reversal is the
unique forbidden outgoing edge. -/
theorem successor_natCard
    (e : Edge) :
    Nat.card (G.Successor e) =
      Nat.card (G.Outgoing (G.target e)) - 1 := by
  rw [Nat.card_congr
    (G.Directed.successorEquivOutgoingNeReverse e)]
  classical
  let r :=
    G.Directed.reverseAsOutgoing e
  have hcompl :=
    Fintype.card_subtype_compl
      (fun f : G.Outgoing (G.target e) =>
        f = r)
  simpa [r, Nat.card_eq_fintype_card] using hcompl

/-- In a d-regular directed-edge presentation, each Hashimoto row contains
exactly d-1 admissible transitions. -/
theorem successor_natCard_of_outgoing
    (d : ℕ)
    (hdegree :
      ∀ v : Vertex,
        Nat.card (G.Outgoing v) = d)
    (e : Edge) :
    Nat.card (G.Successor e) =
      d - 1 := by
  rw [G.successor_natCard e,
    hdegree (G.target e)]

/-- Typed set of all non-backtracking matrix positions. -/
abbrev NonbacktrackingTransition :=
  {p : Edge × Edge //
    G.Nonbacktracking p.1 p.2}

/-- Non-backtracking transitions decompose fiberwise by their first edge. -/
def transitionEquivSigma :
    G.NonbacktrackingTransition ≃
      (Σ e : Edge, G.Successor e) where
  toFun := fun p =>
    ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
  invFun := fun p =>
    ⟨(p.1, p.2.1), p.2.2⟩
  left_inv := by
    intro p
    rfl
  right_inv := by
    intro p
    rfl

/-- Exact structural NNZ count before materializing the Hashimoto matrix. -/
theorem transition_natCard :
    Nat.card G.NonbacktrackingTransition =
      ∑ e : Edge,
        Nat.card (G.Successor e) := by
  rw [Nat.card_congr G.transitionEquivSigma,
    Nat.card_sigma]

/-- Matrix positions with a genuinely nonzero integer Hashimoto weight. -/
abbrev HashimotoNonzero :=
  {p : Edge × Edge //
    G.hashimotoWeight
      (R := ℤ) p.1 p.2 ≠ 0}

@[simp] theorem hashimotoWeight_ne_zero_iff
    (e f : Edge) :
    G.hashimotoWeight (R := ℤ) e f ≠ 0 ↔
      G.Nonbacktracking e f := by
  by_cases h : G.Nonbacktracking e f
  · simp [FiniteDirectedEdgeSystem.hashimotoWeight, h]
  · simp [FiniteDirectedEdgeSystem.hashimotoWeight, h]

/-- Nonzero matrix positions are definitionally the non-backtracking
transition relation. -/
def hashimotoNonzeroEquivTransition :
    G.HashimotoNonzero ≃
      G.NonbacktrackingTransition where
  toFun := fun p =>
    ⟨p.1,
      (G.hashimotoWeight_ne_zero_iff
        p.1.1 p.1.2).mp p.2⟩
  invFun := fun p =>
    ⟨p.1,
      (G.hashimotoWeight_ne_zero_iff
        p.1.1 p.1.2).mpr p.2⟩
  left_inv := by
    intro p
    rfl
  right_inv := by
    intro p
    rfl

/-- Exact NNZ formula in terms of successor counts. -/
theorem hashimotoNonzero_natCard :
    Nat.card G.HashimotoNonzero =
      ∑ e : Edge,
        Nat.card (G.Successor e) := by
  rw [Nat.card_congr
    G.hashimotoNonzeroEquivTransition]
  exact G.transition_natCard

/-- If every vertex has d outgoing oriented edges, Hashimoto has exactly
|E|*(d-1) nonzero entries. -/
theorem hashimotoNonzero_natCard_of_regular
    (d : ℕ)
    (hdegree :
      ∀ v : Vertex,
        Nat.card (G.Outgoing v) = d) :
    Nat.card G.HashimotoNonzero =
      Nat.card Edge * (d - 1) := by
  rw [G.hashimotoNonzero_natCard]
  have hs :
      ∀ e : Edge,
        Nat.card (G.Successor e) =
          d - 1 :=
    G.successor_natCard_of_outgoing d hdegree
  simp_rw [hs]
  simp [Nat.card_eq_fintype_card]

/-- q+1 regularity gives the sparse complexity law NNZ=q*|E|. -/
theorem hashimotoNonzero_natCard_of_qRegular
    (q : ℕ)
    (hdegree :
      ∀ v : Vertex,
        Nat.card (G.Outgoing v) = q + 1) :
    Nat.card G.HashimotoNonzero =
      Nat.card Edge * q := by
  simpa using
    G.hashimotoNonzero_natCard_of_regular
      (q + 1) hdegree

end FiniteDirectedEdgeSystem
end CausalGeometry
