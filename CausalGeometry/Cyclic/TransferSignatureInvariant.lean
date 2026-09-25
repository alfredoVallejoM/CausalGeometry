import CausalGeometry.Cyclic.TransferReindex
import CausalGeometry.Cyclic.TransferSignature

namespace CausalGeometry

universe u u'

namespace FiniteTransferSignature

/-- Stable signature attached to any integer-valued finite transfer system. -/
def ofTransfer
    (T : FiniteTransferSystem.{u, 0} ℤ) :
    FiniteTransferSignature where
  traceSequence := T.traceSequence
  determinantPolynomial := T.determinantPolynomial

@[simp] theorem ofTransfer_trace
    (T : FiniteTransferSystem.{u, 0} ℤ)
    (n : ℕ) :
    (ofTransfer T).traceSequence n =
      T.tracePower n := rfl

@[simp] theorem ofTransfer_determinant
    (T : FiniteTransferSystem.{u, 0} ℤ) :
    (ofTransfer T).determinantPolynomial =
      T.determinantPolynomial := rfl

/-- Reindexing the state type leaves the complete signature unchanged. -/
theorem ofTransfer_reindex
    (T : FiniteTransferSystem.{u, 0} ℤ)
    {S : Type u'}
    [Fintype S] [DecidableEq S]
    (e : T.State ≃ S) :
    ofTransfer (T.reindex e) =
      ofTransfer T := by
  apply FiniteTransferSignature.ext
  · funext n
    exact T.reindex_tracePower e n
  · exact T.reindex_determinantPolynomial e

/-- Hashimoto signature is just the generic transfer signature of its
non-backtracking transition system. -/
theorem ofHashimoto_eq_ofTransfer
    {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    (G : FiniteDirectedEdgeSystem Vertex Edge) :
    ofHashimoto G =
      ofTransfer (G.hashimotoTransfer ℤ) := by
  rfl

end FiniteTransferSignature

/-- Equality of transfer signatures is the exact presentation-independent
comparison surface used by downstream realizations. -/
structure FiniteTransferSignatureComparison
    (T₁ : FiniteTransferSystem.{u, 0} ℤ)
    (T₂ : FiniteTransferSystem.{u', 0} ℤ) : Prop where
  trace :
    ∀ n, T₁.tracePower n = T₂.tracePower n
  determinant :
    T₁.determinantPolynomial =
      T₂.determinantPolynomial

namespace FiniteTransferSignatureComparison

theorem signature_eq
    {T₁ : FiniteTransferSystem.{u, 0} ℤ}
    {T₂ : FiniteTransferSystem.{u', 0} ℤ}
    (C : FiniteTransferSignatureComparison T₁ T₂) :
    FiniteTransferSignature.ofTransfer T₁ =
      FiniteTransferSignature.ofTransfer T₂ := by
  apply FiniteTransferSignature.ext
  · funext n
    exact C.trace n
  · exact C.determinant

/-- A state equivalence automatically supplies a signature comparison. -/
def ofReindex
    (T : FiniteTransferSystem.{u, 0} ℤ)
    {S : Type u'}
    [Fintype S] [DecidableEq S]
    (e : T.State ≃ S) :
    FiniteTransferSignatureComparison
      T (T.reindex e) where
  trace n := (T.reindex_tracePower e n).symm
  determinant :=
    (T.reindex_determinantPolynomial e).symm

end FiniteTransferSignatureComparison
end CausalGeometry
