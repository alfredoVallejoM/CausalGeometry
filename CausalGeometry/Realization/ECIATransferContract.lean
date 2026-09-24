import CausalGeometry.Cyclic.TransferSignature
import CausalGeometry.Realization.ECIAContract

namespace CausalGeometry

universe u v

namespace ECIARealization

variable {A : Type u}
variable {sourceAdmissible : CausalNumber A → Prop}
variable {T : ECIAStructuralTarget.{u, v} A}

/-- Preservation of the stable finite transfer signature.

This does not require ECIA to expose the source matrix or its state basis.
Only the trace sequence and determinant polynomial are compared. -/
structure PreservesFiniteTransferSignature
    (R : ECIARealization A sourceAdmissible T)
    (source : CausalNumber A → FiniteTransferSignature)
    (target : T.Target → FiniteTransferSignature) : Prop where
  trace :
    ∀ X n,
      (target (R.realize X)).traceSequence n =
        (source X).traceSequence n
  determinant :
    ∀ X,
      (target (R.realize X)).determinantPolynomial =
        (source X).determinantPolynomial

/-- Primitive-cycle preservation remains an independent obligation. -/
structure PreservesPrimitiveSignature
    (R : ECIARealization A sourceAdmissible T)
    (source : CausalNumber A → PrimitiveSignature)
    (target : T.Target → PrimitiveSignature) : Prop where
  primitive :
    ∀ X n,
      (target (R.realize X)).primitive n =
        (source X).primitive n

namespace PreservesFiniteTransferSignature

variable
    {R : ECIARealization A sourceAdmissible T}
    {source : CausalNumber A → FiniteTransferSignature}
    {target : T.Target → FiniteTransferSignature}

theorem determinant_eval
    (h : R.PreservesFiniteTransferSignature source target)
    (X : CausalNumber A)
    (u : ℤ) :
    ((target (R.realize X)).determinantPolynomial).eval u =
      ((source X).determinantPolynomial).eval u := by
  rw [h.determinant X]

end PreservesFiniteTransferSignature
end ECIARealization
end CausalGeometry
