import CausalGeometry.Completion.BruhatTitsQuotient
import CausalGeometry.Cyclic.HashimotoIhara

namespace CausalGeometry

universe u v

/-- Concrete Ihara realization of a finite Bruhat--Tits quotient.

No arbitrary Ihara target remains. Once primitive Hashimoto counts are
certified, the determinant reciprocal/Euler-zeta identity is automatic. -/
structure BruhatTitsConcreteIhara
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

namespace BruhatTitsConcreteIhara

variable
    {A : ℕ → Type u}
    [∀ n, CommRing (A n)]
    [∀ n, IsLocalRing (A n)]
    [∀ n, Fintype (A n)]
    {T : PrimePowerLocalRingTower A}
    {B : BruhatTitsBranchingContract T}
    (I : BruhatTitsConcreteIhara.{u, v} B)

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

/-- Concrete determinant reciprocal of the finite quotient. -/
noncomputable def determinantZeta :
    PowerSeries ℚ :=
  I.quotient.finiteSystem
    .hashimotoDeterminantReciprocal

/-- Concrete Euler zeta reconstructed from primitive periods. -/
noncomputable def primitiveZeta :
    PowerSeries ℚ :=
  I.primitiveComparison
    .hashimotoEulerZetaSeries

/-- Finite Ihara identity is now automatic. -/
theorem ihara :
    I.determinantZeta =
      I.primitiveZeta :=
  I.primitiveComparison.ihara

/-- Hashimoto traces are the divisor sums of primitive periods. -/
theorem trace_eq_primitive_divisor_sum
    (n : ℕ) (hn : 0 < n) :
    (I.quotient.finiteSystem.hashimotoTransfer ℤ).tracePower n =
      ∑ d ∈ n.divisors,
        (d : ℤ) *
          I.primitiveComparison.counts.primitive d :=
  I.primitiveComparison
    .trace_eq_primitive_divisor_sum n hn

/-- Primitive periods are recovered from traces by Möbius inversion. -/
theorem mobius_recover_primitive
    (n : ℕ) (hn : 0 < n) :
    ∑ x ∈ n.divisorsAntidiagonal,
      ArithmeticFunction.moebius x.1 *
        (I.quotient.finiteSystem.hashimotoTransfer ℤ).tracePower x.2 =
      (n : ℤ) *
        I.primitiveComparison.counts.primitive n :=
  I.primitiveComparison
    .mobius_recover_from_hashimoto n hn

/-- Exact determinant reciprocal differential equation. -/
theorem determinantZeta_derivative :
    PowerSeries.derivative I.determinantZeta =
      I.determinantZeta *
        I.primitiveComparison.hashimotoTraceSeries := by
  exact
    I.primitiveComparison
      .determinantReciprocal_derivative

/-- Primitive Euler zeta satisfies the same equation independently. -/
theorem primitiveZeta_derivative :
    PowerSeries.derivative I.primitiveZeta =
      I.primitiveZeta *
        I.primitiveComparison.hashimotoTraceSeries :=
  I.primitiveComparison
    .derivative_hashimotoEulerZetaSeries

/-- Exact Hashimoto state count. -/
theorem hashimoto_state_natCard :
    Nat.card I.quotient.QuotEdge =
      Nat.card I.quotient.QuotVertex *
        (T.q + 1) :=
  BruhatTitsFiniteQuotient.edge_natCard
    B I.quotient

/-- Exact sparse NNZ count. -/
theorem hashimoto_nnz_natCard :
    Nat.card
        I.quotient.finiteSystem.HashimotoNonzero =
      Nat.card I.quotient.QuotVertex *
        (T.q + 1) * T.q :=
  BruhatTitsFiniteQuotient.hashimoto_nnz_natCard
    B I.quotient

/-- Stable decategorized transfer signature. -/
noncomputable def transferSignature :
    FiniteTransferSignature :=
  FiniteTransferSignature.ofHashimoto
    I.quotient.finiteSystem

/-- Primitive signature remains independently exposed. -/
def primitiveSignature :
    PrimitiveSignature :=
  PrimitiveSignature.ofComparison
    I.primitiveComparison

end BruhatTitsConcreteIhara
end CausalGeometry
