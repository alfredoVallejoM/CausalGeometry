import CausalGeometry.Cyclic.FiniteTransfer
import Mathlib.LinearAlgebra.Matrix.Trace

namespace CausalGeometry

universe u v

/-- Finite directed-edge system with a fixed-point-free edge reversal.

This is the minimal source needed for a Hashimoto/non-backtracking operator.
Vertices and oriented edges are explicit finite types; no graph library object
is smuggled into the causal kernel. -/
structure FiniteDirectedEdgeSystem
    (Vertex Edge : Type u)
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge] where
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

namespace FiniteDirectedEdgeSystem

variable
    {Vertex Edge : Type u}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    (G : FiniteDirectedEdgeSystem Vertex Edge)

/-- Two oriented edges may follow each other when endpoints match and the
second edge is not the immediate reverse of the first. -/
def Nonbacktracking (e f : Edge) : Prop :=
  G.target e = G.source f ∧ f ≠ G.reverse e

instance nonbacktrackingDecidable (e f : Edge) :
    Decidable (G.Nonbacktracking e f) :=
  inferInstance

/-- Hashimoto transition weight over any commutative ring. -/
def hashimotoWeight
    {R : Type v} [CommRing R]
    (e f : Edge) : R :=
  if G.Nonbacktracking e f then 1 else 0

@[simp] theorem hashimotoWeight_eq_one
    {R : Type v} [CommRing R]
    {e f : Edge}
    (h : G.Nonbacktracking e f) :
    G.hashimotoWeight (R := R) e f = 1 := by
  simp [hashimotoWeight, h]

@[simp] theorem hashimotoWeight_eq_zero
    {R : Type v} [CommRing R]
    {e f : Edge}
    (h : ¬ G.Nonbacktracking e f) :
    G.hashimotoWeight (R := R) e f = 0 := by
  simp [hashimotoWeight, h]

/-- Finite transfer realization of the non-backtracking edge dynamics. -/
def hashimotoTransfer
    (R : Type v) [CommRing R] :
    FiniteTransferSystem R where
  State := Edge
  finite := inferInstance
  decEq := inferInstance
  weight := G.hashimotoWeight

@[simp] theorem hashimoto_matrix_apply
    {R : Type v} [CommRing R]
    (e f : Edge) :
    (G.hashimotoTransfer R).matrix e f =
      G.hashimotoWeight e f := rfl

/-- Weighted number of length-n edge transitions from e to f.

Length zero is the identity matrix.  The recursion appends one final
non-backtracking transition. -/
def walkCount
    {R : Type v} [CommRing R] :
    ℕ → Edge → Edge → R
  | 0, e, f => if e = f then 1 else 0
  | n + 1, e, f =>
      ∑ g : Edge,
        G.walkCount (R := R) n e g *
          G.hashimotoWeight g f

@[simp] theorem walkCount_zero
    {R : Type v} [CommRing R]
    (e f : Edge) :
    G.walkCount (R := R) 0 e f =
      if e = f then 1 else 0 := rfl

@[simp] theorem walkCount_succ
    {R : Type v} [CommRing R]
    (n : ℕ) (e f : Edge) :
    G.walkCount (R := R) (n + 1) e f =
      ∑ g : Edge,
        G.walkCount (R := R) n e g *
          G.hashimotoWeight g f := rfl

/-- Powers of the Hashimoto matrix are exactly the recursive
non-backtracking transition counts. -/
theorem hashimoto_pow_apply_eq_walkCount
    {R : Type v} [CommRing R]
    (n : ℕ) (e f : Edge) :
    ((G.hashimotoTransfer R).matrix ^ n) e f =
      G.walkCount (R := R) n e f := by
  induction n with
  | zero =>
      simp [walkCount]
  | succ n ih =>
      rw [pow_succ, Matrix.mul_apply]
      simp only [hashimoto_matrix_apply, ih]
      rfl

/-- Weighted count of closed non-backtracking edge walks of transition length n. -/
def closedWalkCount
    {R : Type v} [CommRing R]
    (n : ℕ) : R :=
  ∑ e : Edge, G.walkCount (R := R) n e e

/-- Hashimoto trace equals the weighted count of closed non-backtracking walks. -/
theorem tracePower_eq_closedWalkCount
    {R : Type v} [CommRing R]
    (n : ℕ) :
    (G.hashimotoTransfer R).tracePower n =
      G.closedWalkCount (R := R) n := by
  unfold FiniteTransferSystem.tracePower
  simp only [Matrix.trace, Matrix.diag_apply]
  apply Finset.sum_congr rfl
  intro e he
  exact G.hashimoto_pow_apply_eq_walkCount n e e

/-- Immediate reversal is rejected by construction. -/
theorem not_nonbacktracking_reverse (e : Edge) :
    ¬ G.Nonbacktracking e (G.reverse e) := by
  intro h
  exact h.2 rfl

/-- Reversal itself is involutive and therefore supplies the opposite
orientation without identifying an edge with its reverse. -/
@[simp] theorem reverse_reverse (e : Edge) :
    G.reverse (G.reverse e) = e :=
  G.reverse_involutive e

end FiniteDirectedEdgeSystem
end CausalGeometry
