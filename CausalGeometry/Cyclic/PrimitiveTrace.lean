import CausalGeometry.Cyclic.Hashimoto
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace CausalGeometry

open scoped ArithmeticFunction.Moebius

/-- Certified primitive/multiple trace decomposition.

primitive n is the number (or signed/weighted count) of primitive cyclic
classes of exact period n. closed n is the rooted closed-walk trace count.

The defining law closed(n) = sum_{d|n} d * primitive(d) is the exact
combinatorial content required before Mobius inversion can be used. -/
structure PrimitiveTraceCounts where
  primitive : ℕ → ℤ
  closed : ℕ → ℤ

  decomposition :
    ∀ n, 0 < n →
      ∑ d ∈ n.divisors,
        (d : ℤ) * primitive d =
      closed n

namespace PrimitiveTraceCounts

variable (P : PrimitiveTraceCounts)

/-- Weighted primitive sequence A(n)=n P(n). -/
def weightedPrimitive (n : ℕ) : ℤ :=
  (n : ℤ) * P.primitive n

theorem divisor_sum_weightedPrimitive
    (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, P.weightedPrimitive d =
      P.closed n := by
  simpa [weightedPrimitive] using P.decomposition n hn

/-- Mobius inversion recovers the weighted primitive count from the closed
trace sequence. -/
theorem mobius_recover_weightedPrimitive
    (n : ℕ) (hn : 0 < n) :
    ∑ x ∈ n.divisorsAntidiagonal,
      ArithmeticFunction.moebius x.1 •
        P.closed x.2 =
      P.weightedPrimitive n := by
  have h :=
    (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq
      (R := ℤ)).1
      (fun m hm => P.divisor_sum_weightedPrimitive m hm)
  exact h n hn

/-- Same recovery written as integer multiplication. -/
theorem mobius_recover_weightedPrimitive_mul
    (n : ℕ) (hn : 0 < n) :
    ∑ x ∈ n.divisorsAntidiagonal,
      ArithmeticFunction.moebius x.1 *
        P.closed x.2 =
      (n : ℤ) * P.primitive n := by
  simpa [weightedPrimitive, smul_eq_mul] using
    P.mobius_recover_weightedPrimitive n hn

end PrimitiveTraceCounts

/-- Comparison between a concrete Hashimoto operator and a certified
primitive-cycle decomposition. -/
structure HashimotoPrimitiveComparison
    {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    (G : FiniteDirectedEdgeSystem Vertex Edge) where
  counts : PrimitiveTraceCounts

  trace_matches :
    ∀ n,
      (G.hashimotoTransfer ℤ).tracePower n =
        counts.closed n

namespace HashimotoPrimitiveComparison

variable
    {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    {G : FiniteDirectedEdgeSystem Vertex Edge}
    (C : HashimotoPrimitiveComparison G)

/-- Hashimoto traces decompose into primitive periods once the comparison
certificate is supplied. -/
theorem trace_eq_primitive_divisor_sum
    (n : ℕ) (hn : 0 < n) :
    (G.hashimotoTransfer ℤ).tracePower n =
      ∑ d ∈ n.divisors,
        (d : ℤ) * C.counts.primitive d := by
  rw [C.trace_matches n]
  exact (C.counts.decomposition n hn).symm

/-- Primitive-period content can be recovered directly from Hashimoto traces
by Mobius inversion. -/
theorem mobius_recover_from_hashimoto
    (n : ℕ) (hn : 0 < n) :
    ∑ x ∈ n.divisorsAntidiagonal,
      ArithmeticFunction.moebius x.1 *
        (G.hashimotoTransfer ℤ).tracePower x.2 =
      (n : ℤ) * C.counts.primitive n := by
  have h := C.counts.mobius_recover_weightedPrimitive_mul n hn
  simpa only [← C.trace_matches] using h

/-- The same statement can be read purely as a closed-walk count theorem. -/
theorem mobius_recover_from_closedWalkCount
    (n : ℕ) (hn : 0 < n) :
    ∑ x ∈ n.divisorsAntidiagonal,
      ArithmeticFunction.moebius x.1 *
        G.closedWalkCount (R := ℤ) x.2 =
      (n : ℤ) * C.counts.primitive n := by
  simpa only [← G.tracePower_eq_closedWalkCount] using
    C.mobius_recover_from_hashimoto n hn

end HashimotoPrimitiveComparison
end CausalGeometry
