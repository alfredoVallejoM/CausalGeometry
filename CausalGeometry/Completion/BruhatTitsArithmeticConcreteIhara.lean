import CausalGeometry.Completion.BruhatTitsArithmeticQuotient
import CausalGeometry.Completion.BruhatTitsConcreteIhara
import CausalGeometry.Cyclic.PrimitiveConjugacySpectrum

namespace CausalGeometry

universe u v g

/-- Concrete arithmetic Ihara realization of a finite quotient Γ\T.

The only arithmetic-specific input beyond the quotient is the identification
of primitive Hashimoto periods with primitive conjugacy classes and their
translation lengths. The determinant/Euler identity is inherited
automatically from finite matrix algebra. -/
structure BruhatTitsArithmeticConcreteIhara
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

namespace BruhatTitsArithmeticConcreteIhara

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
    (I : BruhatTitsArithmeticConcreteIhara.{u, v, g}
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

/-- Forget arithmetic conjugacy data and retain the concrete finite Ihara
quotient. -/
def toConcreteIhara :
    BruhatTitsConcreteIhara B where
  quotient :=
    I.arithmeticQuotient.quotient
  primitiveComparison :=
    I.primitiveComparison

/-- Exact determinant/Euler Ihara identity. -/
theorem ihara :
    I.arithmeticQuotient.quotient.finiteSystem
        .hashimotoDeterminantReciprocal
      =
    I.primitiveComparison
        .hashimotoEulerZetaSeries :=
  I.toConcreteIhara.ihara

/-- Primitive period multiplicity equals arithmetic primitive conjugacy
multiplicity. -/
theorem primitive_eq_conjugacy_natCard
    (n : ℕ) :
    I.primitiveComparison.counts.primitive n =
      (Nat.card
        (I.conjugacyComparison.spectrum.Level n) : ℤ) :=
  I.conjugacyComparison.primitive_eq_natCard n

theorem primitive_nonnegative
    (n : ℕ) :
    0 ≤
      I.primitiveComparison.counts.primitive n :=
  I.conjugacyComparison.primitive_nonnegative n

/-- Hashimoto trace expressed directly through primitive conjugacy classes. -/
theorem trace_eq_conjugacy_divisor_sum
    (n : ℕ) (hn : 0 < n) :
    (I.arithmeticQuotient.quotient.finiteSystem.hashimotoTransfer ℤ).tracePower n =
      ∑ d ∈ n.divisors,
        (d : ℤ) *
          (Nat.card
            (I.conjugacyComparison.spectrum.Level d) : ℤ) := by
  rw [
    I.primitiveComparison
      .trace_eq_primitive_divisor_sum n hn
  ]
  apply Finset.sum_congr rfl
  intro d hd
  rw [I.primitive_eq_conjugacy_natCard d]

/-- Möbius inversion recovers weighted primitive arithmetic conjugacy counts. -/
theorem mobius_recover_conjugacy
    (n : ℕ) (hn : 0 < n) :
    ∑ x ∈ n.divisorsAntidiagonal,
      ArithmeticFunction.moebius x.1 *
        (I.arithmeticQuotient.quotient.finiteSystem.hashimotoTransfer ℤ).tracePower x.2 =
      (n : ℤ) *
        (Nat.card
          (I.conjugacyComparison.spectrum.Level n) : ℤ) := by
  rw [
    I.primitiveComparison
      .mobius_recover_from_hashimoto n hn
  ]
  rw [I.primitive_eq_conjugacy_natCard n]

/-- Formal zeta differential equation in arithmetic quotient form. -/
theorem determinantZeta_derivative :
    PowerSeries.derivative
        I.arithmeticQuotient.quotient.finiteSystem
          .hashimotoDeterminantReciprocal
      =
    I.arithmeticQuotient.quotient.finiteSystem
        .hashimotoDeterminantReciprocal *
      I.primitiveComparison
        .hashimotoTraceSeries :=
  I.primitiveComparison
    .determinantReciprocal_derivative

/-- Exact quotient Hashimoto state count. -/
theorem hashimoto_state_natCard :
    Nat.card
        I.arithmeticQuotient.quotient.QuotEdge =
      Nat.card
          I.arithmeticQuotient.quotient.QuotVertex *
        (T.q + 1) :=
  I.arithmeticQuotient.edge_natCard

/-- Exact sparse NNZ count. -/
theorem hashimoto_nnz_natCard :
    Nat.card
        I.arithmeticQuotient.quotient.finiteSystem.HashimotoNonzero =
      Nat.card
          I.arithmeticQuotient.quotient.QuotVertex *
        (T.q + 1) * T.q :=
  I.arithmeticQuotient.hashimoto_nnz_natCard

/-- Chosen deck-cycle witness. -/
abbrev DeckCycleWitness :=
  I.arithmeticQuotient.orbitCovering.DeckCycleWitness

/-- A primitive deck witness with certified translation length becomes one
of the conjugacy classes counted by the exact primitive coefficient. -/
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

theorem deck_class_lift_invariant
    (δ : Γ)
    (W : I.DeckCycleWitness) :
    I.arithmeticQuotient.deckConjClass
        (I.arithmeticQuotient.orbitCovering.conjugateDeckCycleWitness
          δ W) =
      I.arithmeticQuotient.deckConjClass W :=
  I.arithmeticQuotient
    .deckConjClass_lift_invariant δ W

end BruhatTitsArithmeticConcreteIhara
end CausalGeometry
