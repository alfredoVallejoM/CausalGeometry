import CausalGeometry.Calculus.GradedCohomologyTransport
import CausalGeometry.Calculus.GradedHodge
import CausalGeometry.Realization.ECIAContract
import Mathlib.Tactic

namespace CausalGeometry

universe u v w x y z

namespace ECIARealization

variable {A : Type u}
variable {sourceAdmissible : CausalNumber A → Prop}
variable {T : ECIAStructuralTarget.{u, v} A}

/-- ECIA preservation of a supplied arbitrary-degree causal cochain theory.

The source cochain family is explicit because the concrete event-cell
realization beyond degree two is itself a theorem/construction layer. -/
structure PreservesGradedCausalCohomology
    (R : ECIARealization A sourceAdmissible T)
    (K : Type w)
    [Field K]
    (SourceCochain :
      CausalNumber A → ℕ → Type x)
    [∀ X n, AddCommGroup (SourceCochain X n)]
    [∀ X n, Module K (SourceCochain X n)]
    (sourceComplex :
      ∀ X : CausalNumber A,
        GradedCausalCochainComplex K
          (SourceCochain X))
    (TargetH0 :
      T.Target → Type y)
    (TargetHSucc :
      T.Target → ℕ → Type z)
    [∀ Y, AddCommGroup (TargetH0 Y)]
    [∀ Y, Module K (TargetH0 Y)]
    [∀ Y n, AddCommGroup (TargetHSucc Y n)]
    [∀ Y n, Module K (TargetHSucc Y n)] : Prop where

  h0Equiv :
    ∀ X : CausalNumber A,
      (sourceComplex X).H0 ≃ₗ[K]
        TargetH0 (R.realize X)

  hSuccEquiv :
    ∀ (X : CausalNumber A) (n : ℕ),
      (sourceComplex X).HSucc n ≃ₗ[K]
        TargetHSucc (R.realize X) n

namespace PreservesGradedCausalCohomology

variable
    {R : ECIARealization A sourceAdmissible T}
    {K : Type w}
    [Field K]
    {SourceCochain :
      CausalNumber A → ℕ → Type x}
    [∀ X n, AddCommGroup (SourceCochain X n)]
    [∀ X n, Module K (SourceCochain X n)]
    {sourceComplex :
      ∀ X : CausalNumber A,
        GradedCausalCochainComplex K
          (SourceCochain X)}
    {TargetH0 : T.Target → Type y}
    {TargetHSucc : T.Target → ℕ → Type z}
    [∀ Y, AddCommGroup (TargetH0 Y)]
    [∀ Y, Module K (TargetH0 Y)]
    [∀ Y n, AddCommGroup (TargetHSucc Y n)]
    [∀ Y n, Module K (TargetHSucc Y n)]
    (h :
      R.PreservesGradedCausalCohomology
        K SourceCochain sourceComplex
        TargetH0 TargetHSucc)

theorem hSucc_subsingleton_iff
    (X : CausalNumber A)
    (n : ℕ) :
    Subsingleton ((sourceComplex X).HSucc n) ↔
      Subsingleton
        (TargetHSucc (R.realize X) n) :=
  h.hSuccEquiv X n
    |>.toEquiv.subsingleton_congr

end PreservesGradedCausalCohomology

/-- ECIA preservation of arbitrary positive-degree causal harmonic data.

This is stronger than preserving only the abstract cohomology group: it records
a target harmonic carrier and a linear equivalence from the source harmonic
space in every positive degree. -/
structure PreservesGradedCausalHodge
    (R : ECIARealization A sourceAdmissible T)
    (K : Type w)
    [Field K]
    (SourceCochain :
      CausalNumber A → ℕ → Type x)
    [∀ X n, AddCommGroup (SourceCochain X n)]
    [∀ X n, Module K (SourceCochain X n)]
    (sourceComplex :
      ∀ X : CausalNumber A,
        GradedCausalCochainComplex K
          (SourceCochain X))
    (sourceHodge :
      ∀ X : CausalNumber A,
        GradedCausalHodgeData
          (sourceComplex X))
    (sourceRepresentation :
      ∀ (X : CausalNumber A) (n : ℕ),
        GradedCausalHodgeRepresentationSucc
          (sourceHodge X) n)
    (TargetHarmonicSucc :
      T.Target → ℕ → Type z)
    [∀ Y n, AddCommGroup
      (TargetHarmonicSucc Y n)]
    [∀ Y n, Module K
      (TargetHarmonicSucc Y n)] : Prop where

  harmonicEquiv :
    ∀ (X : CausalNumber A) (n : ℕ),
      (sourceHodge X).HarmonicSucc n ≃ₗ[K]
        TargetHarmonicSucc (R.realize X) n

namespace PreservesGradedCausalHodge

variable
    {R : ECIARealization A sourceAdmissible T}
    {K : Type w}
    [Field K]
    {SourceCochain :
      CausalNumber A → ℕ → Type x}
    [∀ X n, AddCommGroup (SourceCochain X n)]
    [∀ X n, Module K (SourceCochain X n)]
    {sourceComplex :
      ∀ X : CausalNumber A,
        GradedCausalCochainComplex K
          (SourceCochain X)}
    {sourceHodge :
      ∀ X : CausalNumber A,
        GradedCausalHodgeData
          (sourceComplex X)}
    {sourceRepresentation :
      ∀ (X : CausalNumber A) (n : ℕ),
        GradedCausalHodgeRepresentationSucc
          (sourceHodge X) n}
    {TargetHarmonicSucc :
      T.Target → ℕ → Type z}
    [∀ Y n, AddCommGroup
      (TargetHarmonicSucc Y n)]
    [∀ Y n, Module K
      (TargetHarmonicSucc Y n)]
    (h :
      R.PreservesGradedCausalHodge
        K SourceCochain sourceComplex
        sourceHodge sourceRepresentation
        TargetHarmonicSucc)

/-- Once source Hodge representation is proved, ECIA harmonic preservation
yields a direct equivalence from source causal cohomology to target harmonic
states in every positive degree. -/
noncomputable def hSuccEquivTargetHarmonic
    (X : CausalNumber A)
    (n : ℕ) :
    (sourceComplex X).HSucc n ≃ₗ[K]
      TargetHarmonicSucc (R.realize X) n :=
  (sourceRepresentation X n)
    .harmonicEquivHSucc.symm.trans
      (h.harmonicEquiv X n)

end PreservesGradedCausalHodge
end ECIARealization
end CausalGeometry
