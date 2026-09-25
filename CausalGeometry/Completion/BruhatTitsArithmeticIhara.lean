import CausalGeometry.Completion.BruhatTitsArithmeticQuotient
import CausalGeometry.Cyclic.PrimitiveConjugacySpectrum
import CausalGeometry.Cyclic.TransferDeterminant

namespace CausalGeometry

universe u v g w

/-- Full arithmetic Ihara realization over a finite quotient Γ\T.

Every identification is explicit:
1. arithmetic quotient fibers are Γ-orbits;
2. primitive Hashimoto counts are identified with primitive conjugacy classes
   by translation length;
3. the determinant object is identified with the primitive-count object.
-/
structure BruhatTitsArithmeticIharaRealization
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

  arithmeticQuotient :
    BruhatTitsArithmeticQuotient.{u, v, g}
      Γ B

  primitiveComparison :
    HashimotoPrimitiveComparison
      arithmeticQuotient.quotient.finiteSystem

  conjugacyComparison :
    PrimitiveTraceConjugacyComparison
      (Γ := Γ)
      primitiveComparison.counts

  IharaObject : Type w

  fromDeterminant :
    ℤ[X] → IharaObject

  fromPrimitiveCounts :
    (ℕ → ℤ) → IharaObject

  determinant_primitive_agree :
    fromDeterminant
        arithmeticQuotient.quotient.finiteSystem.hashimotoDeterminantPolynomial =
      fromPrimitiveCounts
        primitiveComparison.counts.primitive

namespace BruhatTitsArithmeticIharaRealization

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
    (I : BruhatTitsArithmeticIharaRealization.{u, v, g, w}
      Γ B)

noncomputable local instance :
    Fintype
      I.arithmeticQuotient.quotient.QuotVertex :=
  I.arithmeticQuotient.quotient.vertexFintype

noncomputable local instance :
    DecidableEq
      I.arithmeticQuotient.quotient.QuotVertex :=
  I.arithmeticQuotient.quotient.vertexDecEq

noncomputable local instance :
    Fintype
      I.arithmeticQuotient.quotient.QuotEdge :=
  I.arithmeticQuotient.quotient.edgeFintype

noncomputable local instance :
    DecidableEq
      I.arithmeticQuotient.quotient.QuotEdge :=
  I.arithmeticQuotient.quotient.edgeDecEq

/-- Primitive exact-period multiplicity is the number of primitive conjugacy
classes at that translation length. -/
theorem primitive_eq_conjugacy_natCard
    (n : ℕ) :
    I.primitiveComparison.counts.primitive n =
      (Nat.card
        (I.conjugacyComparison.spectrum.Level n) : ℤ) :=
  I.conjugacyComparison.primitive_eq_natCard n

/-- Hence all certified primitive multiplicities are nonnegative. -/
theorem primitive_nonnegative
    (n : ℕ) :
    0 ≤
      I.primitiveComparison.counts.primitive n :=
  I.conjugacyComparison.primitive_nonnegative n

/-- Hashimoto trace equals the divisor sum of arithmetic primitive
conjugacy-class multiplicities. -/
theorem trace_eq_conjugacy_divisor_sum
    (n : ℕ) (hn : 0 < n) :
    (I.arithmeticQuotient.quotient.finiteSystem.hashimotoTransfer ℤ).tracePower n =
      ∑ d ∈ n.divisors,
        (d : ℤ) *
          (Nat.card
            (I.conjugacyComparison.spectrum.Level d) : ℤ) := by
  rw [I.primitiveComparison.trace_eq_primitive_divisor_sum n hn]
  apply Finset.sum_congr rfl
  intro d hd
  rw [I.primitive_eq_conjugacy_natCard d]

/-- Möbius inversion recovers the weighted primitive conjugacy count directly
from Hashimoto traces. -/
theorem mobius_recover_conjugacy
    (n : ℕ) (hn : 0 < n) :
    ∑ x ∈ n.divisorsAntidiagonal,
      ArithmeticFunction.moebius x.1 *
        (I.arithmeticQuotient.quotient.finiteSystem.hashimotoTransfer ℤ).tracePower x.2 =
      (n : ℤ) *
        (Nat.card
          (I.conjugacyComparison.spectrum.Level n) : ℤ) := by
  rw [I.primitiveComparison.mobius_recover_from_hashimoto n hn]
  rw [I.primitive_eq_conjugacy_natCard n]

/-- Final certified equality between determinant and primitive arithmetic
objects. -/
theorem ihara_agreement :
    I.fromDeterminant
        I.arithmeticQuotient.quotient.finiteSystem.hashimotoDeterminantPolynomial =
      I.fromPrimitiveCounts
        I.primitiveComparison.counts.primitive :=
  I.determinant_primitive_agree

/-- Exact Hashimoto state count of Γ\T. -/
theorem hashimoto_state_natCard :
    Nat.card
        I.arithmeticQuotient.quotient.QuotEdge =
      Nat.card
          I.arithmeticQuotient.quotient.QuotVertex *
        (T.q + 1) :=
  I.arithmeticQuotient.edge_natCard

/-- Exact sparse NNZ count of Γ\T. -/
theorem hashimoto_nnz_natCard :
    Nat.card
        I.arithmeticQuotient.quotient.finiteSystem.HashimotoNonzero =
      Nat.card
          I.arithmeticQuotient.quotient.QuotVertex *
        (T.q + 1) * T.q :=
  I.arithmeticQuotient.hashimoto_nnz_natCard

/-- A chosen lifted cycle/deck witness. -/
abbrev DeckCycleWitness :=
  I.arithmeticQuotient.orbitCovering.DeckCycleWitness

/-- If a deck witness is primitive and its lifted length is certified to equal
the conjugacy translation length, it becomes an element of the exact spectrum
level counted by the primitive trace coefficient. -/
def primitiveSpectrumElement
    (W : I.DeckCycleWitness)
    (hprimitive :
      PrimitiveConjugacy.IsPrimitive W.deck)
    (hlength :
      I.conjugacyComparison.spectrum.translationLength
          (I.arithmeticQuotient.deckConjClass W) =
        W.lift.length) :
    I.conjugacyComparison.spectrum.Level
      W.lift.length := by
  refine
    ⟨I.arithmeticQuotient.deckConjClass W,
      ?_, hlength⟩
  unfold BruhatTitsArithmeticQuotient.deckConjClass
  exact
    (PrimitiveConjugacy.primitiveClass_mk_iff
      W.deck).2 hprimitive

/-- Changing the chosen lift leaves the counted conjugacy class unchanged. -/
theorem deck_class_lift_invariant
    (δ : Γ)
    (W : I.DeckCycleWitness) :
    I.arithmeticQuotient.deckConjClass
        (I.arithmeticQuotient.orbitCovering.conjugateDeckCycleWitness
          δ W) =
      I.arithmeticQuotient.deckConjClass W :=
  I.arithmeticQuotient.deckConjClass_lift_invariant
    δ W

end BruhatTitsArithmeticIharaRealization
end CausalGeometry
