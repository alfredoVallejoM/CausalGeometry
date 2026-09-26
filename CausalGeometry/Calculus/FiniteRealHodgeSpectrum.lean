import CausalGeometry.Calculus.FiniteRealHodgeDecomposition
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Tactic

namespace CausalGeometry

noncomputable section

universe v

open InnerProductSpace

namespace finiteRealHodgeData

variable
    {C : ℕ → Type v}
    [∀ n, NormedAddCommGroup (C n)]
    [∀ n, InnerProductSpace ℝ (C n)]
    [∀ n, FiniteDimensional ℝ (C n)]
    (G : GradedCausalCochainComplex ℝ C)

/-- The finite-real positive-degree Hodge Laplacian is a positive
endomorphism.  This is derived from the two Gram summands d d^* and d^* d. -/
theorem laplacianSucc_isPositive
    (n : ℕ) :
    ((H G).laplacianSucc n).IsPositive := by
  change
    ((G.d n).comp (G.d n).adjoint +
      (G.d (n + 1)).adjoint.comp
        (G.d (n + 1))).IsPositive
  exact
    (LinearMap.isPositive_self_comp_adjoint
      (G.d n)).add
      (LinearMap.isPositive_adjoint_comp_self
        (G.d (n + 1)))

/-- In particular the causal Hodge Laplacian is symmetric/self-adjoint in the
finite-dimensional real sector. -/
theorem laplacianSucc_isSymmetric
    (n : ℕ) :
    ((H G).laplacianSucc n).IsSymmetric :=
  (laplacianSucc_isPositive G n).isSymmetric

/-- Spectral rank of degree n+1. -/
abbrev spectralRank
    (n : ℕ) : ℕ :=
  Module.finrank ℝ (C (n + 1))

/-- Ordered eigenvalues of the positive causal Hodge Laplacian. -/
noncomputable def laplacianEigenvalues
    (n : ℕ) :
    Fin (G.spectralRank n) → ℝ :=
  (laplacianSucc_isSymmetric G n)
    .eigenvalues rfl

/-- Orthonormal eigenbasis of the positive causal Hodge Laplacian. -/
noncomputable def laplacianEigenvectorBasis
    (n : ℕ) :
    OrthonormalBasis
      (Fin (G.spectralRank n))
      ℝ
      (C (n + 1)) :=
  (laplacianSucc_isSymmetric G n)
    .eigenvectorBasis rfl

/-- Every vector of the canonical spectral basis is an eigenvector. -/
theorem laplacian_apply_eigenvectorBasis
    (n : ℕ)
    (i : Fin (G.spectralRank n)) :
    (H G).laplacianSucc n
        (G.laplacianEigenvectorBasis n i)
      =
    G.laplacianEigenvalues n i •
      G.laplacianEigenvectorBasis n i := by
  exact
    (laplacianSucc_isSymmetric G n)
      .apply_eigenvectorBasis rfl i

/-- The positive Hodge spectrum is nonnegative. -/
theorem laplacianEigenvalues_nonneg
    (n : ℕ)
    (i : Fin (G.spectralRank n)) :
    0 ≤ G.laplacianEigenvalues n i := by
  exact
    (laplacianSucc_isPositive G n)
      .nonneg_eigenvalues rfl i

/-- The zero eigenspace of the Hodge Laplacian is exactly the causal harmonic
subspace. -/
theorem zeroEigenspace_eq_harmonic
    (n : ℕ) :
    Module.End.eigenspace
        ((H G).laplacianSucc n)
        0
      =
    (H G).HarmonicSucc n := by
  rw [Module.End.eigenspace_zero]
  rfl

/-- Spectral diagonalization formula in the orthonormal eigenbasis. -/
theorem laplacian_repr
    (n : ℕ)
    (x : C (n + 1))
    (i : Fin (G.spectralRank n)) :
    (G.laplacianEigenvectorBasis n).repr
        ((H G).laplacianSucc n x) i
      =
    G.laplacianEigenvalues n i *
      (G.laplacianEigenvectorBasis n).repr x i := by
  exact
    (laplacianSucc_isSymmetric G n)
      .eigenvectorBasis_apply_self_apply
        rfl x i

/-- Zero-eigenvalue multiplicity is the dimension of causal harmonic
cochains. -/
theorem zeroEigenvalueMultiplicity
    (n : ℕ) :
    Finset.card
        {i : Fin (G.spectralRank n) |
          G.laplacianEigenvalues n i = 0}
      =
    Module.finrank ℝ
      ((H G).HarmonicSucc n) := by
  have h :=
    (laplacianSucc_isSymmetric G n)
      .card_filter_eigenvalues_eq
        (n := G.spectralRank n)
        rfl 0
  rw [zeroEigenspace_eq_harmonic G n] at h
  exact h

end finiteRealHodgeData
end

end CausalGeometry
