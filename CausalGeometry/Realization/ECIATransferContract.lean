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

/-- Admissibility-scoped preservation of a stable finite transfer signature.

The source signature is carried only by admitted causal numbers. -/
structure PreservesFiniteTransferSignatureOnAdmissible
    (R : ECIARealization A sourceAdmissible T)
    (source :
      {X : CausalNumber A // sourceAdmissible X} →
        FiniteTransferSignature)
    (target : T.Target → FiniteTransferSignature) : Prop where
  trace :
    ∀ X n,
      (target (R.realize X.1)).traceSequence n =
        (source X).traceSequence n
  determinant :
    ∀ X,
      (target (R.realize X.1)).determinantPolynomial =
        (source X).determinantPolynomial

/-- Admissibility-scoped primitive-signature preservation. -/
structure PreservesPrimitiveSignatureOnAdmissible
    (R : ECIARealization A sourceAdmissible T)
    (source :
      {X : CausalNumber A // sourceAdmissible X} →
        PrimitiveSignature)
    (target : T.Target → PrimitiveSignature) : Prop where
  primitive :
    ∀ X n,
      (target (R.realize X.1)).primitive n =
        (source X).primitive n

/-- Any global transfer comparison restricts to an admitted source domain. -/
def PreservesFiniteTransferSignature.toOnAdmissible
    {R : ECIARealization A sourceAdmissible T}
    {source : CausalNumber A → FiniteTransferSignature}
    {target : T.Target → FiniteTransferSignature}
    (h :
      R.PreservesFiniteTransferSignature
        source target) :
    R.PreservesFiniteTransferSignatureOnAdmissible
      (fun X => source X.1)
      target where
  trace := fun X n => h.trace X.1 n
  determinant := fun X => h.determinant X.1

/-- Any global primitive comparison restricts likewise. -/
def PreservesPrimitiveSignature.toOnAdmissible
    {R : ECIARealization A sourceAdmissible T}
    {source : CausalNumber A → PrimitiveSignature}
    {target : T.Target → PrimitiveSignature}
    (h :
      R.PreservesPrimitiveSignature
        source target) :
    R.PreservesPrimitiveSignatureOnAdmissible
      (fun X => source X.1)
      target where
  primitive := fun X n => h.primitive X.1 n

namespace PreservesFiniteTransferSignatureOnAdmissible

variable
    {R : ECIARealization A sourceAdmissible T}
    {source :
      {X : CausalNumber A // sourceAdmissible X} →
        FiniteTransferSignature}
    {target : T.Target → FiniteTransferSignature}

theorem determinant_eval
    (h :
      R.PreservesFiniteTransferSignatureOnAdmissible
        source target)
    (X : {X : CausalNumber A // sourceAdmissible X})
    (u : ℤ) :
    ((target (R.realize X.1)).determinantPolynomial).eval u =
      ((source X).determinantPolynomial).eval u := by
  rw [h.determinant X]

end PreservesFiniteTransferSignatureOnAdmissible

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
