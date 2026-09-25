import CausalGeometry.Cyclic.IharaSignature
import CausalGeometry.Realization.ECIATransferContract

namespace CausalGeometry

universe u v

namespace ECIARealization

variable {A : Type u}
variable {sourceAdmissible : CausalNumber A → Prop}
variable {T : ECIAStructuralTarget.{u, v} A}

/-- ECIA preserves a complete stable Ihara signature when it separately
preserves the transfer and primitive signatures.

No new zeta-preservation field is required: all zeta data are derived. -/
structure PreservesFiniteIharaSignature
    (R : ECIARealization A sourceAdmissible T)
    (source : CausalNumber A → FiniteIharaSignature)
    (target : T.Target → FiniteIharaSignature) : Prop where
  transfer :
    R.PreservesFiniteTransferSignature
      (fun X => (source X).transfer)
      (fun Y => (target Y).transfer)

  primitive :
    R.PreservesPrimitiveSignature
      (fun X => (source X).primitive)
      (fun Y => (target Y).primitive)

namespace PreservesFiniteIharaSignature

variable
    {R : ECIARealization A sourceAdmissible T}
    {source : CausalNumber A → FiniteIharaSignature}
    {target : T.Target → FiniteIharaSignature}
    (h :
      R.PreservesFiniteIharaSignature
        source target)

/-- Transfer signature equality at one realized causal number. -/
theorem transfer_eq
    (X : CausalNumber A) :
    (target (R.realize X)).transfer =
      (source X).transfer := by
  apply FiniteTransferSignature.ext
  · funext n
    exact h.transfer.trace X n
  · exact h.transfer.determinant X

/-- Primitive signature equality at one realized causal number. -/
theorem primitive_eq
    (X : CausalNumber A) :
    (target (R.realize X)).primitive =
      (source X).primitive := by
  apply PrimitiveSignature.ext
  funext n
  exact h.primitive.primitive X n

/-- The complete stable Ihara signature is preserved. -/
theorem signature_eq
    (X : CausalNumber A) :
    target (R.realize X) =
      source X := by
  exact
    FiniteIharaSignature.ext
      (h.transfer_eq X)
      (h.primitive_eq X)

/-- Euler logarithm preservation is derived, not assumed. -/
theorem eulerLogSeries_eq
    (X : CausalNumber A) :
    (target (R.realize X)).eulerLogSeries =
      (source X).eulerLogSeries := by
  rw [h.signature_eq X]

/-- Euler zeta preservation is derived. -/
theorem eulerZetaSeries_eq
    (X : CausalNumber A) :
    (target (R.realize X)).eulerZetaSeries =
      (source X).eulerZetaSeries := by
  rw [h.signature_eq X]

/-- Determinant power-series preservation is also derived from the stable
signature equality. -/
theorem determinantPowerSeries_eq
    (X : CausalNumber A) :
    (target (R.realize X)).determinantPowerSeries =
      (source X).determinantPowerSeries := by
  rw [h.signature_eq X]

/-- Normalization of the determinant transfers automatically. -/
theorem target_normalized
    (X : CausalNumber A)
    (hsrc :
      (source X).DeterminantNormalized) :
    (target (R.realize X)).DeterminantNormalized := by
  rw [h.signature_eq X]
  exact hsrc

/-- The concrete reciprocal determinant is preserved with transported
normalization proof. -/
theorem determinantReciprocal_eq
    (X : CausalNumber A)
    (hsrc :
      (source X).DeterminantNormalized) :
    (target (R.realize X)).determinantReciprocal
        (h.target_normalized X hsrc)
      =
    (source X).determinantReciprocal hsrc := by
  have hs := h.signature_eq X
  cases hs
  rfl

/-- If the source finite realization satisfies the concrete Ihara identity,
then the ECIA image satisfies exactly the same identity. -/
theorem target_satisfiesIhara
    (X : CausalNumber A)
    (hsrcNorm :
      (source X).DeterminantNormalized)
    (hsrcIhara :
      (source X).SatisfiesIhara hsrcNorm) :
    (target (R.realize X)).SatisfiesIhara
      (h.target_normalized X hsrcNorm) := by
  have hs := h.signature_eq X
  cases hs
  exact hsrcIhara

/-- In particular, every Hashimoto-produced source signature transports its
proved Ihara identity through ECIA as soon as the stable signatures are
preserved. -/
theorem target_satisfiesIhara_of_sourceHashimoto
    {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    {G : FiniteDirectedEdgeSystem Vertex Edge}
    (C : HashimotoPrimitiveComparison G)
    (X : CausalNumber A)
    (hsource :
      source X =
        FiniteIharaSignature.ofHashimoto C) :
    (target (R.realize X)).SatisfiesIhara
      (by
        rw [h.signature_eq X, hsource]
        exact
          FiniteIharaSignature.ofHashimoto_normalized C) := by
  rw [h.signature_eq X, hsource]
  exact
    FiniteIharaSignature.ofHashimoto_satisfiesIhara C

end PreservesFiniteIharaSignature
end ECIARealization
end CausalGeometry
