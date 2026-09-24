import CausalGeometry.Completion.BruhatTitsFiniteGraph
import Mathlib.SetTheory.Cardinal.Finite

namespace CausalGeometry

universe u

namespace BruhatTitsFiniteGraph

variable
    {A : ℕ → Type u}
    [∀ n, CommRing (A n)]
    [∀ n, IsLocalRing (A n)]
    [∀ n, Fintype (A n)]
    {T : PrimePowerLocalRingTower A}
    (B : BruhatTitsBranchingContract T)

/-- Exact number of vertices in the rooted truncation through projective level N. -/
theorem vertex_natCard (N : ℕ) :
    Nat.card (Vertex (B := B) N) =
      1 +
        ∑ n : Fin (N + 1),
          (T.q + 1) * T.q ^ n.1 := by
  change
    Nat.card
      (Sum Unit
        (Σ n : Fin (N + 1),
          LocalProjectivePair.Line (A n.1))) =
      _
  rw [Nat.card_sum, Nat.card_unique, Nat.card_sigma]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact B.projective_card n.1

/-- Exact number of undirected parent-child links in the rooted truncation. -/
theorem link_natCard (N : ℕ) :
    Nat.card (Link (B := B) N) =
      (T.q + 1) +
        ∑ n : Fin N,
          (T.q + 1) * T.q ^ (n.1 + 1) := by
  change
    Nat.card
      (Sum
        (LocalProjectivePair.Line (A 0))
        (Σ n : Fin N,
          LocalProjectivePair.Line (A (n.1 + 1)))) =
      _
  rw [Nat.card_sum, Nat.card_sigma]
  rw [B.projective_card_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact B.projective_card (n.1 + 1)

/-- Every undirected tree link contributes exactly two oriented Hashimoto
states. -/
theorem orientedEdge_natCard (N : ℕ) :
    Nat.card (OrientedEdge (B := B) N) =
      2 * Nat.card (Link (B := B) N) := by
  change
    Nat.card (Link (B := B) N × Bool) =
      _
  rw [Nat.card_prod]
  simp [Nat.mul_comm]

/-- Expanded exact formula for the size of the Hashimoto state space. -/
theorem orientedEdge_natCard_expanded (N : ℕ) :
    Nat.card (OrientedEdge (B := B) N) =
      2 *
        ((T.q + 1) +
          ∑ n : Fin N,
            (T.q + 1) * T.q ^ (n.1 + 1)) := by
  rw [B.orientedEdge_natCard N, B.link_natCard N]

end BruhatTitsFiniteGraph
end CausalGeometry
