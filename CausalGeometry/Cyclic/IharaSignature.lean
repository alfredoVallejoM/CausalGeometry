import CausalGeometry.Cyclic.EulerZetaSeries
import CausalGeometry.Cyclic.TransferSignature
import CausalGeometry.Cyclic.ConcreteIhara

namespace CausalGeometry

/-- Presentation-independent finite Ihara signature.

It contains only stable decategorized data:
- the complete transfer signature (all traces and determinant polynomial);
- primitive exact-period multiplicities;
- the certified divisor decomposition connecting them.

No state basis, matrix presentation or graph labels are retained. -/
structure FiniteIharaSignature where
  transfer : FiniteTransferSignature
  primitive : PrimitiveSignature

  decomposition :
    ∀ n, 0 < n →
      ∑ d ∈ n.divisors,
        (d : ℤ) * primitive.primitive d =
      transfer.traceSequence n

namespace FiniteIharaSignature

/-- Recover the PrimitiveTraceCounts API from the stable signature. -/
def counts
    (S : FiniteIharaSignature) :
    PrimitiveTraceCounts where
  primitive := S.primitive.primitive
  closed := S.transfer.traceSequence
  decomposition := S.decomposition

/-- Formal Euler logarithm derived only from stable primitive/trace data. -/
def eulerLogSeries
    (S : FiniteIharaSignature) :
    PowerSeries ℚ :=
  S.counts.eulerLogSeries

/-- Formal Euler zeta derived from the signature. -/
def eulerZetaSeries
    (S : FiniteIharaSignature) :
    PowerSeries ℚ :=
  S.counts.eulerZetaSeries

/-- Determinant polynomial embedded into Q[[X]]. -/
def determinantPowerSeries
    (S : FiniteIharaSignature) :
    PowerSeries ℚ :=
  (((S.transfer.determinantPolynomial.map
      (Int.castRingHom ℚ)) : ℚ[X]) :
    PowerSeries ℚ)

/-- The determinant polynomial has constant term one exactly when its zero
coefficient says so. This property is kept explicit for arbitrary stable
signatures, even though Hashimoto signatures prove it automatically. -/
def DeterminantNormalized
    (S : FiniteIharaSignature) : Prop :=
  S.transfer.determinantPolynomial.coeff 0 = 1

/-- Formal reciprocal determinant reconstructed from a normalized signature. -/
def determinantReciprocal
    (S : FiniteIharaSignature)
    (h : S.DeterminantNormalized) :
    PowerSeries ℚ :=
  PowerSeries.invOfUnit
    S.determinantPowerSeries 1

@[simp] theorem determinantPowerSeries_constantCoeff
    (S : FiniteIharaSignature)
    (h : S.DeterminantNormalized) :
    PowerSeries.constantCoeff
        S.determinantPowerSeries =
      1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [determinantPowerSeries, h]

/-- Stable signatures can state the concrete Ihara identity without retaining a
matrix presentation. -/
def SatisfiesIhara
    (S : FiniteIharaSignature)
    (h : S.DeterminantNormalized) : Prop :=
  S.determinantReciprocal h =
    S.eulerZetaSeries

/-- Any concrete finite graph plus primitive comparison produces a stable
Ihara signature. -/
def ofHashimoto
    {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    {G : FiniteDirectedEdgeSystem Vertex Edge}
    (C : HashimotoPrimitiveComparison G) :
    FiniteIharaSignature where
  transfer :=
    FiniteTransferSignature.ofHashimoto G
  primitive :=
    PrimitiveSignature.ofComparison C
  decomposition := by
    intro n hn
    symm
    exact
      C.trace_eq_primitive_divisor_sum n hn

/-- Hashimoto signatures are normalized. -/
theorem ofHashimoto_normalized
    {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    {G : FiniteDirectedEdgeSystem Vertex Edge}
    (C : HashimotoPrimitiveComparison G) :
    (ofHashimoto C).DeterminantNormalized := by
  change
    G.hashimotoDeterminantPolynomial.coeff 0 = 1
  exact
    (G.hashimotoTransfer ℤ)
      .determinantPolynomial_coeff_zero

/-- The stable signature produced by any finite Hashimoto realization
satisfies the concrete Ihara identity. -/
theorem ofHashimoto_satisfiesIhara
    {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    {G : FiniteDirectedEdgeSystem Vertex Edge}
    (C : HashimotoPrimitiveComparison G) :
    (ofHashimoto C).SatisfiesIhara
      (ofHashimoto_normalized C) := by
  change
    PowerSeries.invOfUnit
      G.hashimotoDeterminantPowerSeries 1 =
      C.hashimotoEulerZetaSeries
  exact C.ihara

/-- Equality of transfer and primitive signatures determines equality of the
entire stable Ihara signature. -/
theorem ext
    {S T : FiniteIharaSignature}
    (htransfer : S.transfer = T.transfer)
    (hprimitive : S.primitive = T.primitive) :
    S = T := by
  cases S
  cases T
  simp_all

/-- Every derived Euler logarithm is invariant under equality of stable
signatures. -/
theorem eulerLogSeries_eq_of_eq
    {S T : FiniteIharaSignature}
    (h : S = T) :
    S.eulerLogSeries = T.eulerLogSeries := by
  rw [h]

theorem eulerZetaSeries_eq_of_eq
    {S T : FiniteIharaSignature}
    (h : S = T) :
    S.eulerZetaSeries = T.eulerZetaSeries := by
  rw [h]

end FiniteIharaSignature
end CausalGeometry
