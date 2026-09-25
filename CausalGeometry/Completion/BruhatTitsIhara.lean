import CausalGeometry.Completion.BruhatTitsQuotient
import CausalGeometry.Cyclic.TransferDeterminant

namespace CausalGeometry

universe u v w

/-- Certified finite Ihara realization obtained from a locally bijective
quotient of the universal Bruhat--Tits tree.

The quotient supplies global cycles, the Hashimoto comparison supplies trace
versus primitive periods, and the Ihara certificate supplies the final
determinant-versus-primitive object equality. -/
structure BruhatTitsIharaRealization
    {A : ℕ → Type u}
    [∀ n, CommRing (A n)]
    [∀ n, IsLocalRing (A n)]
    [∀ n, Fintype (A n)]
    {T : PrimePowerLocalRingTower A}
    (B : BruhatTitsBranchingContract T) where

  quotient :
    BruhatTitsFiniteQuotient.Quotient
      (B := B)

  primitiveComparison :
    HashimotoPrimitiveComparison
      quotient.finiteSystem

  IharaObject : Type w

  fromDeterminant :
    ℤ[X] → IharaObject

  fromPrimitiveCounts :
    (ℕ → ℤ) → IharaObject

  determinant_primitive_agree :
    fromDeterminant
        quotient.finiteSystem.hashimotoDeterminantPolynomial =
      fromPrimitiveCounts
        primitiveComparison.counts.primitive

namespace BruhatTitsIharaRealization

variable
    {A : ℕ → Type u}
    [∀ n, CommRing (A n)]
    [∀ n, IsLocalRing (A n)]
    [∀ n, Fintype (A n)]
    {T : PrimePowerLocalRingTower A}
    {B : BruhatTitsBranchingContract T}
    (I : BruhatTitsIharaRealization.{u, v, w} B)

noncomputable local instance :
    Fintype I.quotient.QuotVertex :=
  I.quotient.vertexFintype

noncomputable local instance :
    DecidableEq I.quotient.QuotVertex :=
  I.quotient.vertexDecEq

noncomputable local instance :
    Fintype I.quotient.QuotEdge :=
  I.quotient.edgeFintype

noncomputable local instance :
    DecidableEq I.quotient.QuotEdge :=
  I.quotient.edgeDecEq

/-- Stable finite transfer signature of the quotient. -/
noncomputable def transferSignature :
    FiniteTransferSignature :=
  FiniteTransferSignature.ofHashimoto
    I.quotient.finiteSystem

/-- Primitive signature kept separately from the transfer signature. -/
def primitiveSignature :
    PrimitiveSignature :=
  PrimitiveSignature.ofComparison
    I.primitiveComparison

/-- Hashimoto traces are divisor sums of exact primitive periods. -/
theorem trace_eq_primitive_divisor_sum
    (n : ℕ) (hn : 0 < n) :
    (I.quotient.finiteSystem.hashimotoTransfer ℤ).tracePower n =
      ∑ d ∈ n.divisors,
        (d : ℤ) *
          I.primitiveComparison.counts.primitive d :=
  I.primitiveComparison.trace_eq_primitive_divisor_sum
    n hn

/-- Möbius inversion recovers exact primitive-period content from the quotient
Hashimoto traces. -/
theorem mobius_recover_primitive
    (n : ℕ) (hn : 0 < n) :
    ∑ x ∈ n.divisorsAntidiagonal,
      ArithmeticFunction.moebius x.1 *
        (I.quotient.finiteSystem.hashimotoTransfer ℤ).tracePower x.2 =
      (n : ℤ) *
        I.primitiveComparison.counts.primitive n :=
  I.primitiveComparison.mobius_recover_from_hashimoto
    n hn

/-- The determinant side and primitive-count side agree in the certified Ihara
target. -/
theorem ihara_agreement :
    I.fromDeterminant
        I.quotient.finiteSystem.hashimotoDeterminantPolynomial =
      I.fromPrimitiveCounts
        I.primitiveComparison.counts.primitive :=
  I.determinant_primitive_agree

/-- Exact sparse size of the quotient Hashimoto operator. -/
theorem hashimoto_nnz_natCard :
    Nat.card
        I.quotient.finiteSystem.HashimotoNonzero =
      Nat.card I.quotient.QuotVertex *
        (T.q + 1) * T.q :=
  BruhatTitsFiniteQuotient.hashimoto_nnz_natCard
    B I.quotient

/-- Exact number of Hashimoto states. -/
theorem hashimoto_state_natCard :
    Nat.card I.quotient.QuotEdge =
      Nat.card I.quotient.QuotVertex *
        (T.q + 1) :=
  BruhatTitsFiniteQuotient.edge_natCard
    B I.quotient

/-- Lifted quotient-cycle evidence remains available for geometric
interpretation of closed non-backtracking cycles. -/
abbrev CycleLift :=
  BruhatTitsFiniteQuotient.CycleLift
    (B := B) I.quotient

theorem cycleLift_maps_closed
    (L : I.CycleLift) :
    I.quotient.finiteSystem.toDirected.NonbacktrackingPath
      (I.quotient.covering.edgeMap L.startEdge)
      L.length
      (I.quotient.covering.edgeMap L.startEdge) :=
  BruhatTitsFiniteQuotient.cycleLift_maps_closed
    B I.quotient L

end BruhatTitsIharaRealization
end CausalGeometry
