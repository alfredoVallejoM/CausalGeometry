import CausalGeometry.Calculus.FiniteRealHodgeSpectrum
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic

namespace CausalGeometry

noncomputable section

universe v

namespace finiteRealHodgeData

variable
    {C : ℕ → Type v}
    [∀ n, NormedAddCommGroup (C n)]
    [∀ n, InnerProductSpace ℝ (C n)]
    [∀ n, FiniteDimensional ℝ (C n)]
    (G : GradedCausalCochainComplex ℝ C)

/-- Ordinary algebraic basis underlying the orthonormal Hodge eigenbasis. -/
abbrev spectralBasis
    (n : ℕ) :
    Basis (Fin (G.spectralRank n))
      ℝ (C (n + 1)) :=
  (G.laplacianEigenvectorBasis n).toBasis

/-- Reciprocal spectral weight, with the harmonic zero mode sent to zero. -/
def greenWeight
    (n : ℕ)
    (i : Fin (G.spectralRank n)) :
    ℝ :=
  if G.laplacianEigenvalues n i = 0 then
    0
  else
    (G.laplacianEigenvalues n i)⁻¹

/-- Spectral Green operator: inverse Laplacian on the positive spectrum and
zero on the harmonic zero eigenspace. -/
noncomputable def greenSucc
    (n : ℕ) :
    C (n + 1) →ₗ[ℝ] C (n + 1) :=
  (G.spectralBasis n).constr ℝ
    (fun i =>
      G.greenWeight n i •
        G.spectralBasis n i)

/-- Spectral projector onto the zero eigenspace/harmonic sector. -/
noncomputable def harmonicProjectionSucc
    (n : ℕ) :
    C (n + 1) →ₗ[ℝ] C (n + 1) :=
  (G.spectralBasis n).constr ℝ
    (fun i =>
      if G.laplacianEigenvalues n i = 0 then
        G.spectralBasis n i
      else
        0)

@[simp] theorem greenSucc_basis
    (n : ℕ)
    (i : Fin (G.spectralRank n)) :
    G.greenSucc n
        (G.spectralBasis n i)
      =
    G.greenWeight n i •
      G.spectralBasis n i := by
  exact
    (G.spectralBasis n).constr_basis
      ℝ
      (fun j =>
        G.greenWeight n j •
          G.spectralBasis n j)
      i

@[simp] theorem harmonicProjectionSucc_basis
    (n : ℕ)
    (i : Fin (G.spectralRank n)) :
    G.harmonicProjectionSucc n
        (G.spectralBasis n i)
      =
    if G.laplacianEigenvalues n i = 0 then
      G.spectralBasis n i
    else
      0 := by
  exact
    (G.spectralBasis n).constr_basis
      ℝ
      (fun j =>
        if G.laplacianEigenvalues n j = 0 then
          G.spectralBasis n j
        else
          0)
      i

/-- Green equation on one spectral basis vector. -/
theorem laplacian_green_basis
    (n : ℕ)
    (i : Fin (G.spectralRank n)) :
    (H G).laplacianSucc n
        (G.greenSucc n
          (G.spectralBasis n i))
      =
    (LinearMap.id -
      G.harmonicProjectionSucc n)
        (G.spectralBasis n i) := by

  rw [greenSucc_basis]
  rw [map_smul]
  change
    G.greenWeight n i •
        ((H G).laplacianSucc n
          (G.laplacianEigenvectorBasis n i))
      =
    _

  rw [laplacian_apply_eigenvectorBasis]

  by_cases h :
      G.laplacianEigenvalues n i = 0

  · simp [greenWeight,
      harmonicProjectionSucc_basis,
      h]

  · simp [greenWeight,
      harmonicProjectionSucc_basis,
      h, smul_smul]

/-- The reverse Green equation on one spectral basis vector. -/
theorem green_laplacian_basis
    (n : ℕ)
    (i : Fin (G.spectralRank n)) :
    G.greenSucc n
        ((H G).laplacianSucc n
          (G.spectralBasis n i))
      =
    (LinearMap.id -
      G.harmonicProjectionSucc n)
        (G.spectralBasis n i) := by

  change
    G.greenSucc n
        ((H G).laplacianSucc n
          (G.laplacianEigenvectorBasis n i))
      =
    _

  rw [laplacian_apply_eigenvectorBasis]
  rw [map_smul]
  rw [greenSucc_basis]

  by_cases h :
      G.laplacianEigenvalues n i = 0

  · simp [greenWeight,
      harmonicProjectionSucc_basis,
      h]

  · simp [greenWeight,
      harmonicProjectionSucc_basis,
      h, smul_smul]

/-- Global Green identity Delta G = I - P_harm. -/
theorem laplacian_comp_green
    (n : ℕ) :
    ((H G).laplacianSucc n).comp
        (G.greenSucc n)
      =
    LinearMap.id -
      G.harmonicProjectionSucc n := by
  apply (G.spectralBasis n).ext
  intro i
  exact
    laplacian_green_basis G n i

/-- Global reverse Green identity G Delta = I - P_harm. -/
theorem green_comp_laplacian
    (n : ℕ) :
    (G.greenSucc n).comp
        ((H G).laplacianSucc n)
      =
    LinearMap.id -
      G.harmonicProjectionSucc n := by
  apply (G.spectralBasis n).ext
  intro i
  exact
    green_laplacian_basis G n i

/-- Harmonic spectral projection is killed by the Laplacian. -/
theorem laplacian_comp_harmonicProjection
    (n : ℕ) :
    ((H G).laplacianSucc n).comp
        (G.harmonicProjectionSucc n)
      =
    0 := by
  apply (G.spectralBasis n).ext
  intro i
  rw [LinearMap.comp_apply]
  rw [harmonicProjectionSucc_basis]
  by_cases h :
      G.laplacianEigenvalues n i = 0
  · rw [if_pos h]
    change
      (H G).laplacianSucc n
          (G.laplacianEigenvectorBasis n i)
        =
      0
    rw [laplacian_apply_eigenvectorBasis]
    rw [h]
    simp
  · rw [if_neg h]
    simp

/-- Green kills the harmonic spectral projection. -/
theorem green_comp_harmonicProjection
    (n : ℕ) :
    (G.greenSucc n).comp
        (G.harmonicProjectionSucc n)
      =
    0 := by
  apply (G.spectralBasis n).ext
  intro i
  rw [LinearMap.comp_apply]
  rw [harmonicProjectionSucc_basis]
  by_cases h :
      G.laplacianEigenvalues n i = 0
  · rw [if_pos h]
    rw [greenSucc_basis]
    simp [greenWeight, h]
  · rw [if_neg h]
    simp

/-- The harmonic projector is idempotent. -/
theorem harmonicProjectionSucc_idempotent
    (n : ℕ) :
    (G.harmonicProjectionSucc n).comp
        (G.harmonicProjectionSucc n)
      =
    G.harmonicProjectionSucc n := by
  apply (G.spectralBasis n).ext
  intro i
  rw [LinearMap.comp_apply]
  rw [harmonicProjectionSucc_basis]
  by_cases h :
      G.laplacianEigenvalues n i = 0
  · rw [if_pos h]
    rw [harmonicProjectionSucc_basis]
    rw [if_pos h]
  · rw [if_neg h]
    simp

/-- The range of the spectral harmonic projector is contained in the actual
causal harmonic subspace. -/
theorem harmonicProjectionSucc_mem_harmonic
    (n : ℕ)
    (x : C (n + 1)) :
    G.harmonicProjectionSucc n x ∈
      (H G).HarmonicSucc n := by
  change
    (H G).laplacianSucc n
        (G.harmonicProjectionSucc n x)
      =
    0
  have h :=
    LinearMap.congr_fun
      (laplacian_comp_harmonicProjection
        G n)
      x
  simpa using h

/-- Every harmonic cochain is fixed by the spectral harmonic projector. -/
theorem harmonicProjectionSucc_eq_self_of_harmonic
    (n : ℕ)
    {x : C (n + 1)}
    (hx :
      x ∈ (H G).HarmonicSucc n) :
    G.harmonicProjectionSucc n x = x := by

  have h :=
    LinearMap.congr_fun
      (green_comp_laplacian
        G n)
      x

  change
    G.greenSucc n
        ((H G).laplacianSucc n x)
      =
    x -
      G.harmonicProjectionSucc n x at h

  rw [hx] at h
  simp at h

  exact h.symm

/-- Green vanishes on genuine harmonic cochains. -/
theorem greenSucc_eq_zero_of_harmonic
    (n : ℕ)
    {x : C (n + 1)}
    (hx :
      x ∈ (H G).HarmonicSucc n) :
    G.greenSucc n x = 0 := by
  rw [←
    harmonicProjectionSucc_eq_self_of_harmonic
      G n hx]
  have h :=
    LinearMap.congr_fun
      (green_comp_harmonicProjection
        G n)
      x
  simpa using h

end finiteRealHodgeData
end

end CausalGeometry
