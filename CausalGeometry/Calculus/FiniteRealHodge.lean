import CausalGeometry.Calculus.GradedHodge
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic

namespace CausalGeometry

noncomputable section

universe v

open InnerProductSpace

/-- Canonical real finite-dimensional Hodge datum on a graded causal complex.

The codifferential is not chosen independently: it is the actual adjoint of
the causal differential for the supplied real inner products. -/
def finiteRealHodgeData
    {C : ℕ → Type v}
    [∀ n, NormedAddCommGroup (C n)]
    [∀ n, InnerProductSpace ℝ (C n)]
    [∀ n, FiniteDimensional ℝ (C n)]
    (G : GradedCausalCochainComplex ℝ C) :
    GradedCausalHodgeData G where

  codiff := fun n =>
    (G.d n).adjoint

  pairing := fun n =>
    innerₗ (C n)

  adjoint := by
    intro n x y
    exact
      (LinearMap.adjoint_inner_right
        (G.d n) x y).symm

namespace finiteRealHodgeData

variable
    {C : ℕ → Type v}
    [∀ n, NormedAddCommGroup (C n)]
    [∀ n, InnerProductSpace ℝ (C n)]
    [∀ n, FiniteDimensional ℝ (C n)]
    (G : GradedCausalCochainComplex ℝ C)

abbrev H :
    GradedCausalHodgeData G :=
  finiteRealHodgeData G

/-- Positive-degree causal Hodge Laplacian in the canonical finite real
realization. -/
theorem laplacianSucc_apply
    (n : ℕ)
    (x : C (n + 1)) :
    (H G).laplacianSucc n x =
      G.d n ((G.d n).adjoint x) +
        (G.d (n + 1)).adjoint
          (G.d (n + 1) x) :=
  rfl

/-- Hodge energy identity.

The Laplacian energy is exactly the sum of the squared incoming-codifferential
and outgoing-differential norms. -/
theorem inner_laplacianSucc_eq_energy
    (n : ℕ)
    (x : C (n + 1)) :
    inner ℝ x ((H G).laplacianSucc n x)
      =
    ‖(G.d n).adjoint x‖ ^ 2 +
      ‖G.d (n + 1) x‖ ^ 2 := by
  rw [laplacianSucc_apply]
  rw [inner_add_right]
  rw [← LinearMap.adjoint_inner_left
    (G.d n) ((G.d n).adjoint x) x]
  rw [LinearMap.adjoint_inner_right
    (G.d (n + 1)) x
      (G.d (n + 1) x)]
  rw [real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]

/-- In finite-dimensional positive real Hodge theory, harmonicity is no longer
an independent decomposition hypothesis: Delta x = 0 iff x is simultaneously
closed and coclosed. -/
theorem harmonicSucc_iff_closed_and_coclosed
    (n : ℕ)
    (x : C (n + 1)) :
    x ∈ (H G).HarmonicSucc n
      ↔
    G.d (n + 1) x = 0 ∧
      (G.d n).adjoint x = 0 := by
  constructor

  · intro hx

    have hlap :
        (H G).laplacianSucc n x = 0 :=
      hx

    have henergy :=
      inner_laplacianSucc_eq_energy
        G n x

    rw [hlap, inner_zero_right] at henergy

    have hcodNorm :
        ‖(G.d n).adjoint x‖ = 0 := by
      have hnonneg :
          0 ≤ ‖G.d (n + 1) x‖ ^ 2 :=
        sq_nonneg _
      have hsq :
          ‖(G.d n).adjoint x‖ ^ 2 = 0 := by
        nlinarith
      exact sq_eq_zero_iff.mp hsq

    have hdNorm :
        ‖G.d (n + 1) x‖ = 0 := by
      have hnonneg :
          0 ≤ ‖(G.d n).adjoint x‖ ^ 2 :=
        sq_nonneg _
      have hsq :
          ‖G.d (n + 1) x‖ ^ 2 = 0 := by
        nlinarith
      exact sq_eq_zero_iff.mp hsq

    exact
      ⟨norm_eq_zero.mp hdNorm,
        norm_eq_zero.mp hcodNorm⟩

  · rintro ⟨hd, hcod⟩

    change
      (H G).laplacianSucc n x = 0

    rw [laplacianSucc_apply]
    rw [hd, hcod]
    simp

/-- The orthogonal complement of exact cochains is precisely the kernel of the
incoming codifferential. -/
theorem exactSucc_orthogonal_eq_coclosed
    (n : ℕ) :
    (G.ExactSucc n)ᗮ =
      (G.d n).adjoint.ker := by
  change
    (G.d n).rangeᗮ =
      (G.d n).adjoint.ker
  exact
    LinearMap.orthogonal_range
      (G.d n)

/-- Harmonic cochains are exactly closed cochains orthogonal to the exact
subspace. -/
theorem harmonicSucc_eq_closed_inf_exactOrthogonal
    (n : ℕ) :
    (H G).HarmonicSucc n =
      G.Closed (n + 1) ⊓
        (G.ExactSucc n)ᗮ := by
  ext x
  constructor

  · intro hx
    rcases
        (harmonicSucc_iff_closed_and_coclosed
          G n x).1 hx with
      ⟨hclosed, hcoclosed⟩
    refine ⟨hclosed, ?_⟩
    rw [exactSucc_orthogonal_eq_coclosed
      G n]
    exact hcoclosed

  · rintro ⟨hclosed, horth⟩
    apply
      (harmonicSucc_iff_closed_and_coclosed
        G n x).2
    refine ⟨hclosed, ?_⟩
    rw [← exactSucc_orthogonal_eq_coclosed
      G n]
    exact horth

/-- Every exact subspace admits an orthogonal projection in the
finite-dimensional real sector. -/
noncomputable local instance exactHasOrthogonalProjection
    (n : ℕ) :
    (G.ExactSucc n).HasOrthogonalProjection := by
  letI :
      FiniteDimensional ℝ
        (G.ExactSucc n) :=
    Submodule.finiteDimensional_of_le
      (show G.ExactSucc n ≤ ⊤ from le_top)
  letI :
      CompleteSpace (G.ExactSucc n) :=
    FiniteDimensional.complete ℝ
      (G.ExactSucc n)
  infer_instance

/-- Finite-dimensional real positivity derives the positive-degree Hodge
representation hypotheses that were previously left abstract.

No Hodge decomposition is assumed in this theorem:
it is constructed by orthogonally projecting each closed cochain onto the
exact subspace. -/
noncomputable def representationSucc
    (n : ℕ) :
    GradedCausalHodgeRepresentationSucc
      (H G) n where

  harmonic_closed := by
    intro x hx
    exact
      ((harmonicSucc_iff_closed_and_coclosed
        G n x).1 hx).1

  closed_decompose := by
    intro z

    rcases
        Submodule.exists_add_mem_mem_orthogonal
          (K := G.ExactSucc n)
          (z : C (n + 1)) with
      ⟨e, heExact, h, hhOrth, hdecomp⟩

    have heClosed :
        G.d (n + 1) e = 0 :=
      G.exactSucc_le_closedSucc n heExact

    have hhEq :
        h = (z : C (n + 1)) - e := by
      rw [hdecomp]
      abel

    have hhClosed :
        G.d (n + 1) h = 0 := by
      rw [hhEq, map_sub, z.2,
        heClosed]
      simp

    have hhCoclosed :
        (G.d n).adjoint h = 0 := by
      have hm :
          h ∈ (G.d n).adjoint.ker := by
        rw [← exactSucc_orthogonal_eq_coclosed
          G n]
        exact hhOrth
      exact hm

    have hhHarmonic :
        h ∈ (H G).HarmonicSucc n :=
      (harmonicSucc_iff_closed_and_coclosed
        G n h).2
        ⟨hhClosed, hhCoclosed⟩

    exact
      ⟨⟨e, heExact⟩,
        ⟨⟨h, hhHarmonic⟩,
          hdecomp⟩⟩

  exact_harmonic_disjoint := by
    rw [harmonicSucc_eq_closed_inf_exactOrthogonal
      G n]
    exact
      (Submodule.orthogonal_disjoint
        (G.ExactSucc n)).mono_right
          inf_le_right

/-- Therefore every positive causal cohomology group of a finite-dimensional
real inner-product causal complex is canonically linearly equivalent to its
harmonic space. -/
noncomputable def harmonicEquivHSucc
    (n : ℕ) :
    (H G).HarmonicSucc n ≃ₗ[ℝ]
      G.HSucc n :=
  (representationSucc G n).harmonicEquivHSucc

end finiteRealHodgeData
end

end CausalGeometry
