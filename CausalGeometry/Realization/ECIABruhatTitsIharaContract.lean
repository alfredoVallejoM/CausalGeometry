import CausalGeometry.Completion.BruhatTitsIharaProfile
import CausalGeometry.Realization.ECIAIharaContract

namespace CausalGeometry

universe u v

namespace ECIARealization

variable {A : Type u}
variable {sourceAdmissible : CausalNumber A → Prop}
variable {T : ECIAStructuralTarget.{u, v} A}

/-- ECIA preservation contract for the complete stable local/Ihara provenance.

Only independent data are required:
- residue prime p;
- residue degree f;
- residue cardinal q;
- quotient vertex count;
- the stable finite Ihara signature.

Hashimoto state count, sparse NNZ, determinant reciprocal and Euler zeta are
all derived from those data and the profile laws. -/
structure PreservesBruhatTitsIharaProfile
    (R : ECIARealization A sourceAdmissible T)
    (source : CausalNumber A → BruhatTitsIharaProfile)
    (target : T.Target → BruhatTitsIharaProfile) : Prop where

  prime :
    ∀ X,
      (target (R.realize X)).p =
        (source X).p

  residueDegree :
    ∀ X,
      (target (R.realize X)).f =
        (source X).f

  residueCardinal :
    ∀ X,
      (target (R.realize X)).q =
        (source X).q

  vertexCount :
    ∀ X,
      (target (R.realize X)).vertexCount =
        (source X).vertexCount

  ihara :
    R.PreservesFiniteIharaSignature
      (fun X => (source X).ihara)
      (fun Y => (target Y).ihara)

namespace PreservesBruhatTitsIharaProfile

variable
    {R : ECIARealization A sourceAdmissible T}
    {source : CausalNumber A → BruhatTitsIharaProfile}
    {target : T.Target → BruhatTitsIharaProfile}
    (h :
      R.PreservesBruhatTitsIharaProfile
        source target)

/-- The entire stable profile is preserved from the independent fields. -/
theorem profile_eq
    (X : CausalNumber A) :
    target (R.realize X) =
      source X := by
  apply BruhatTitsIharaProfile.ext
  · exact h.prime X
  · exact h.residueDegree X
  · exact h.residueCardinal X
  · exact h.vertexCount X
  · exact h.ihara.signature_eq X

/-- Hashimoto state count is derived from local degree and quotient size. -/
theorem edgeCount_eq
    (X : CausalNumber A) :
    (target (R.realize X)).edgeCount =
      (source X).edgeCount := by
  rw [h.profile_eq X]

/-- Sparse NNZ count is derived as well. -/
theorem nnzCount_eq
    (X : CausalNumber A) :
    (target (R.realize X)).nnzCount =
      (source X).nnzCount := by
  rw [h.profile_eq X]

/-- The complete finite Ihara signature is preserved. -/
theorem ihara_eq
    (X : CausalNumber A) :
    (target (R.realize X)).ihara =
      (source X).ihara := by
  rw [h.profile_eq X]

/-- Determinant zeta preservation is derived. -/
theorem determinantZeta_eq
    (X : CausalNumber A) :
    (target (R.realize X)).determinantZeta =
      (source X).determinantZeta := by
  rw [h.profile_eq X]

/-- Primitive Euler zeta preservation is derived independently of matrix
presentation. -/
theorem primitiveZeta_eq
    (X : CausalNumber A) :
    (target (R.realize X)).primitiveZeta =
      (source X).primitiveZeta := by
  rw [h.profile_eq X]

/-- Trace sequence preservation follows from the embedded Ihara signature. -/
theorem traceSequence_eq
    (X : CausalNumber A) :
    (target (R.realize X)).ihara
          .transfer.traceSequence =
      (source X).ihara
          .transfer.traceSequence := by
  rw [h.profile_eq X]

/-- Primitive exact-period multiplicities are preserved. -/
theorem primitiveSignature_eq
    (X : CausalNumber A) :
    (target (R.realize X)).ihara
          .primitive =
      (source X).ihara
          .primitive := by
  rw [h.profile_eq X]

/-- Local arithmetic scaling law q=p^f is transported automatically because
the whole profile agrees. -/
theorem residuePrimePowerLaw_eq
    (X : CausalNumber A) :
    (target (R.realize X)).q =
      (target (R.realize X)).p ^
        (target (R.realize X)).f := by
  exact (target (R.realize X)).q_eq

/-- Sparse complexity law survives realization without a separate proof field. -/
theorem target_sparse_law
    (X : CausalNumber A) :
    (target (R.realize X)).nnzCount =
      (target (R.realize X)).vertexCount *
        ((target (R.realize X)).q + 1) *
        (target (R.realize X)).q :=
  (target (R.realize X)).nnzCount_law

/-- The target profile inherits the already proved concrete Ihara identity. -/
theorem target_ihara
    (X : CausalNumber A) :
    (target (R.realize X)).determinantZeta =
      (target (R.realize X)).primitiveZeta :=
  (target (R.realize X))
    .determinantZeta_eq_primitiveZeta

end PreservesBruhatTitsIharaProfile

/-- Arithmetic provenance preservation needs no new primitive-count field:
once the underlying local/Ihara profile is preserved, actual primitive class
counts are forced by their identification with the stable primitive signature. -/
def PreservesArithmeticBruhatTitsIharaProfile
    (R : ECIARealization A sourceAdmissible T)
    (source :
      CausalNumber A →
        ArithmeticBruhatTitsIharaProfile)
    (target :
      T.Target →
        ArithmeticBruhatTitsIharaProfile) : Prop :=
  R.PreservesBruhatTitsIharaProfile
    (fun X =>
      (source X).toBruhatTitsIharaProfile)
    (fun Y =>
      (target Y).toBruhatTitsIharaProfile)

namespace PreservesArithmeticBruhatTitsIharaProfile

variable
    {R : ECIARealization A sourceAdmissible T}
    {source :
      CausalNumber A →
        ArithmeticBruhatTitsIharaProfile}
    {target :
      T.Target →
        ArithmeticBruhatTitsIharaProfile}
    (h :
      R.PreservesArithmeticBruhatTitsIharaProfile
        source target)

/-- Actual primitive conjugacy-class counts are forced to agree. -/
theorem primitiveClassCount_eq
    (X : CausalNumber A)
    (n : ℕ) :
    (target (R.realize X)).primitiveClassCount n =
      (source X).primitiveClassCount n := by
  apply Nat.cast_injective (R := ℤ)
  rw [
    ← (target (R.realize X))
      .primitive_eq_classCount n,
    ← (source X)
      .primitive_eq_classCount n
  ]
  have hs :=
    h.primitiveSignature_eq X
  exact congrArg
    (fun P : PrimitiveSignature =>
      P.primitive n) hs

/-- Arithmetic primitive multiplicities remain nonnegative downstream. -/
theorem target_primitive_nonnegative
    (X : CausalNumber A)
    (n : ℕ) :
    0 ≤
      (target (R.realize X))
        .toBruhatTitsIharaProfile
        .ihara.primitive.primitive n :=
  (target (R.realize X))
    .primitive_nonnegative n

/-- The full local/Ihara profile preservation API remains available. -/
theorem underlying_profile_eq
    (X : CausalNumber A) :
    (target (R.realize X))
        .toBruhatTitsIharaProfile =
      (source X)
        .toBruhatTitsIharaProfile :=
  h.profile_eq X

end PreservesArithmeticBruhatTitsIharaProfile
end ECIARealization
end CausalGeometry
