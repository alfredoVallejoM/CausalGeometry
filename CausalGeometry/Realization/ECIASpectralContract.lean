import CausalGeometry.Calculus.GradedHodge
import CausalGeometry.Realization.ECIAGradedContract
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic

namespace CausalGeometry

universe u v w x y

namespace ECIARealization

variable {A : Type u}
variable {sourceAdmissible : CausalNumber A → Prop}
variable {T : ECIAStructuralTarget.{u, v} A}

/-- Strong ECIA contract for preserving the actual graded causal Hodge
Laplacian.

This is intentionally stronger than merely giving an equivalence of harmonic
spaces.  The downstream target must expose a target cochain carrier, a target
Laplacian, and an equivalence of cochains that intertwines source and target
operators.  Harmonic and spectral preservation are then derived theorems. -/
structure PreservesGradedCausalLaplacian
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
    (TargetCochain :
      T.Target → ℕ → Type y)
    [∀ Y n, AddCommGroup (TargetCochain Y n)]
    [∀ Y n, Module K (TargetCochain Y n)] : Prop where

  targetLaplacianSucc :
    ∀ (Y : T.Target) (n : ℕ),
      TargetCochain Y (n + 1) →ₗ[K]
        TargetCochain Y (n + 1)

  cochainEquivSucc :
    ∀ (X : CausalNumber A) (n : ℕ),
      SourceCochain X (n + 1) ≃ₗ[K]
        TargetCochain (R.realize X) (n + 1)

  intertwines :
    ∀ (X : CausalNumber A) (n : ℕ),
      (targetLaplacianSucc
          (R.realize X) n).comp
        (cochainEquivSucc X n).toLinearMap
      =
      (cochainEquivSucc X n).toLinearMap.comp
        ((sourceHodge X).laplacianSucc n)

namespace PreservesGradedCausalLaplacian

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
    {TargetCochain :
      T.Target → ℕ → Type y}
    [∀ Y n, AddCommGroup (TargetCochain Y n)]
    [∀ Y n, Module K (TargetCochain Y n)]
    (h :
      R.PreservesGradedCausalLaplacian
        K SourceCochain sourceComplex
        sourceHodge TargetCochain)

/-- Target harmonic subspace defined from the target Laplacian itself. -/
abbrev TargetHarmonicSucc
    (Y : T.Target)
    (n : ℕ) :
    Submodule K
      (TargetCochain Y (n + 1)) :=
  (h.targetLaplacianSucc Y n).ker

/-- The strong Laplacian contract derives harmonic preservation. -/
def harmonicEquiv
    (X : CausalNumber A)
    (n : ℕ) :
    (sourceHodge X).HarmonicSucc n ≃ₗ[K]
      h.TargetHarmonicSucc
        (R.realize X) n where

  toFun := fun z =>
    ⟨h.cochainEquivSucc X n z, by
      have hi :=
        LinearMap.congr_fun
          (h.intertwines X n)
          (z : SourceCochain X (n + 1))
      change
        h.targetLaplacianSucc
            (R.realize X) n
            (h.cochainEquivSucc X n z)
          =
        0
      rw [hi]
      rw [z.2]
      simp⟩

  invFun := fun z =>
    ⟨(h.cochainEquivSucc X n).symm z, by
      have hi :=
        LinearMap.congr_fun
          (h.intertwines X n)
          ((h.cochainEquivSucc X n).symm z)
      have hz :
          h.targetLaplacianSucc
              (R.realize X) n z
            =
          0 :=
        z.2
      change
        (sourceHodge X).laplacianSucc n
            ((h.cochainEquivSucc X n).symm z)
          =
        0
      apply
        (h.cochainEquivSucc X n).injective
      rw [← hi]
      simpa using hz⟩

  left_inv := by
    intro z
    apply Subtype.ext
    simp

  right_inv := by
    intro z
    apply Subtype.ext
    simp

  map_add' := by
    intro x y
    apply Subtype.ext
    simp

  map_smul' := by
    intro a x
    apply Subtype.ext
    simp

/-- Target eigenspace of the actual target Laplacian. -/
abbrev TargetEigenspace
    (Y : T.Target)
    (n : ℕ)
    (μ : K) :
    Submodule K
      (TargetCochain Y (n + 1)) :=
  Module.End.eigenspace
    (h.targetLaplacianSucc Y n) μ

/-- The strong Laplacian contract preserves every named eigenspace, not only
the zero/harmonic one. -/
def eigenspaceEquiv
    (X : CausalNumber A)
    (n : ℕ)
    (μ : K) :
    Module.End.eigenspace
        ((sourceHodge X).laplacianSucc n)
        μ
      ≃ₗ[K]
    h.TargetEigenspace
      (R.realize X) n μ where

  toFun := fun z =>
    ⟨h.cochainEquivSucc X n z, by
      apply Module.End.mem_eigenspace_iff.mpr
      have hz :
          (sourceHodge X).laplacianSucc n z
            =
          μ • (z :
            SourceCochain X (n + 1)) :=
        Module.End.mem_eigenspace_iff.mp z.2
      have hi :=
        LinearMap.congr_fun
          (h.intertwines X n)
          (z : SourceCochain X (n + 1))
      rw [hi, hz]
      simp⟩

  invFun := fun z =>
    ⟨(h.cochainEquivSucc X n).symm z, by
      apply Module.End.mem_eigenspace_iff.mpr
      have hz :
          h.targetLaplacianSucc
              (R.realize X) n z
            =
          μ •
            (z :
              TargetCochain
                (R.realize X) (n + 1)) :=
        Module.End.mem_eigenspace_iff.mp z.2
      have hi :=
        LinearMap.congr_fun
          (h.intertwines X n)
          ((h.cochainEquivSucc X n).symm z)
      apply
        (h.cochainEquivSucc X n).injective
      rw [← hi]
      rw [hz]
      simp⟩

  left_inv := by
    intro z
    apply Subtype.ext
    simp

  right_inv := by
    intro z
    apply Subtype.ext
    simp

  map_add' := by
    intro x y
    apply Subtype.ext
    simp

  map_smul' := by
    intro a x
    apply Subtype.ext
    simp

/-- Finite eigenspace multiplicities are therefore preserved exactly. -/
theorem eigenspace_finrank_eq
    [∀ X n,
      FiniteDimensional K
        (SourceCochain X n)]
    [∀ Y n,
      FiniteDimensional K
        (TargetCochain Y n)]
    (X : CausalNumber A)
    (n : ℕ)
    (μ : K) :
    Module.finrank K
        (Module.End.eigenspace
          ((sourceHodge X).laplacianSucc n)
          μ)
      =
    Module.finrank K
        (h.TargetEigenspace
          (R.realize X) n μ) :=
  LinearEquiv.finrank_eq
    (h.eigenspaceEquiv X n μ)

/-- The zero eigenspace comparison specializes to harmonic preservation. -/
theorem zeroEigenspace_finrank_eq_harmonic
    [∀ X n,
      FiniteDimensional K
        (SourceCochain X n)]
    [∀ Y n,
      FiniteDimensional K
        (TargetCochain Y n)]
    (X : CausalNumber A)
    (n : ℕ) :
    Module.finrank K
        ((sourceHodge X).HarmonicSucc n)
      =
    Module.finrank K
        (h.TargetHarmonicSucc
          (R.realize X) n) := by
  exact
    LinearEquiv.finrank_eq
      (h.harmonicEquiv X n)

end PreservesGradedCausalLaplacian
end ECIARealization
end CausalGeometry
