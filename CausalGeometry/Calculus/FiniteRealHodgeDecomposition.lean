import CausalGeometry.Calculus.FiniteRealHodge
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
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

/-- Coexact positive-degree cochains are the range of the outgoing
codifferential d_(n+1)^*. -/
abbrev CoexactSucc
    (n : ℕ) :
    Submodule ℝ (C (n + 1)) :=
  (G.d (n + 1)).adjoint.range

/-- Coexact cochains are exactly the orthogonal complement of closed
cochains. -/
theorem closed_orthogonal_eq_coexact
    (n : ℕ) :
    (G.Closed (n + 1))ᗮ =
      G.CoexactSucc n := by
  change
    (G.d (n + 1)).kerᗮ =
      (G.d (n + 1)).adjoint.range
  exact
    LinearMap.orthogonal_ker
      (G.d (n + 1))

/-- Exact and harmonic cochains are orthogonal. -/
theorem exact_isOrtho_harmonic
    (n : ℕ) :
    G.ExactSucc n ⟂
      (H G).HarmonicSucc n := by
  rw [harmonicSucc_eq_closed_inf_exactOrthogonal
    G n]
  exact
    (Submodule.isOrtho_orthogonal_right
      (G.ExactSucc n)).mono_right
        inf_le_right

/-- Exact and coexact cochains are orthogonal because exact cochains are
closed. -/
theorem exact_isOrtho_coexact
    (n : ℕ) :
    G.ExactSucc n ⟂
      G.CoexactSucc n := by
  rw [← closed_orthogonal_eq_coexact
    G n]
  exact
    (Submodule.isOrtho_orthogonal_right
      (G.Closed (n + 1))).mono_left
        (G.exactSucc_le_closedSucc n)

/-- Harmonic and coexact cochains are orthogonal because harmonic cochains are
closed. -/
theorem harmonic_isOrtho_coexact
    (n : ℕ) :
    (H G).HarmonicSucc n ⟂
      G.CoexactSucc n := by
  rw [← closed_orthogonal_eq_coexact
    G n]
  exact
    (Submodule.isOrtho_orthogonal_right
      (G.Closed (n + 1))).mono_left
        (representationSucc G n).harmonic_closed

/-- The closed subspace admits an orthogonal projection in the
finite-dimensional real sector. -/
noncomputable local instance closedHasOrthogonalProjection
    (n : ℕ) :
    (G.Closed (n + 1)).HasOrthogonalProjection := by
  letI :
      FiniteDimensional ℝ
        (G.Closed (n + 1)) :=
    Submodule.finiteDimensional_of_le
      (show G.Closed (n + 1) ≤ ⊤ from le_top)
  letI :
      CompleteSpace (G.Closed (n + 1)) :=
    FiniteDimensional.complete ℝ
      (G.Closed (n + 1))
  infer_instance

/-- Strong positive-degree Hodge decomposition package.

The three pieces are not merely pairwise disjoint: they are pairwise
orthogonal, which supplies the correct direct-sum uniqueness. -/
structure OrthogonalDecompositionSucc
    (n : ℕ) : Prop where

  decompose :
    ∀ x : C (n + 1),
      ∃ e : G.ExactSucc n,
        ∃ h : (H G).HarmonicSucc n,
          ∃ c : G.CoexactSucc n,
            x =
              (e : C (n + 1)) +
                (h : C (n + 1)) +
                  (c : C (n + 1))

  exact_harmonic :
    G.ExactSucc n ⟂
      (H G).HarmonicSucc n

  exact_coexact :
    G.ExactSucc n ⟂
      G.CoexactSucc n

  harmonic_coexact :
    (H G).HarmonicSucc n ⟂
      G.CoexactSucc n

/-- Construct the full exact + harmonic + coexact decomposition. -/
noncomputable def orthogonalDecompositionSucc
    (n : ℕ) :
    G.OrthogonalDecompositionSucc n where

  decompose := by
    intro x

    rcases
        Submodule.exists_add_mem_mem_orthogonal
          (K := G.Closed (n + 1))
          x with
      ⟨z, hzClosed, c, hcOrth, hzc⟩

    let zClosed :
        G.Closed (n + 1) :=
      ⟨z, hzClosed⟩

    rcases
        (representationSucc G n)
          .closed_decompose zClosed with
      ⟨e, h, zeh⟩

    have hcCoexact :
        c ∈ G.CoexactSucc n := by
      rw [← closed_orthogonal_eq_coexact
        G n]
      exact hcOrth

    refine
      ⟨e, h, ⟨c, hcCoexact⟩, ?_⟩

    calc
      x =
          z + c :=
        hzc
      _ =
          ((e : G.ExactSucc n) :
              C (n + 1)) +
            ((h : (H G).HarmonicSucc n) :
              C (n + 1)) +
            c := by
              rw [zeh]

  exact_harmonic :=
    exact_isOrtho_harmonic G n

  exact_coexact :=
    exact_isOrtho_coexact G n

  harmonic_coexact :=
    harmonic_isOrtho_coexact G n

/-- Uniqueness of the three Hodge components.

This is the directness theorem: two exact/harmonic/coexact decompositions of
the same cochain have identical components. -/
theorem decomposition_components_unique
    (n : ℕ)
    {e e' : C (n + 1)}
    {h h' : C (n + 1)}
    {c c' : C (n + 1)}
    (he : e ∈ G.ExactSucc n)
    (he' : e' ∈ G.ExactSucc n)
    (hh : h ∈ (H G).HarmonicSucc n)
    (hh' : h' ∈ (H G).HarmonicSucc n)
    (hc : c ∈ G.CoexactSucc n)
    (hc' : c' ∈ G.CoexactSucc n)
    (hsum :
      e + h + c =
        e' + h' + c') :
    e = e' ∧
      h = h' ∧
        c = c' := by

  have hExactRestOrtho :
      G.ExactSucc n ⟂
        ((H G).HarmonicSucc n ⊔
          G.CoexactSucc n) := by
    rw [Submodule.isOrtho_sup_right]
    exact
      ⟨exact_isOrtho_harmonic G n,
        exact_isOrtho_coexact G n⟩

  have hExactRestDisjoint :
      Disjoint
        (G.ExactSucc n)
        ((H G).HarmonicSucc n ⊔
          G.CoexactSucc n) :=
    hExactRestOrtho.disjoint

  have heDiffExact :
      e - e' ∈ G.ExactSucc n :=
    (G.ExactSucc n).sub_mem he he'

  have hRest :
      (h - h') + (c - c') ∈
        ((H G).HarmonicSucc n ⊔
          G.CoexactSucc n) := by
    apply
      (Submodule.sup_mem_iff).2
    exact
      ⟨h - h',
        (G.CoexactSucc n).sub_mem hc hc',
        c - c',
        (H G).HarmonicSucc n |>.sub_mem hh hh',
        by abel⟩

  have heRestEq :
      e - e' =
        - ((h - h') + (c - c')) := by
    apply sub_eq_zero.mp
    have :
        (e - e') +
          ((h - h') + (c - c')) =
        0 := by
      rw [← sub_eq_zero]
      exact hsum
    abel

  have heDiffRest :
      e - e' ∈
        ((H G).HarmonicSucc n ⊔
          G.CoexactSucc n) := by
    rw [heRestEq]
    exact
      (((H G).HarmonicSucc n ⊔
        G.CoexactSucc n)).neg_mem hRest

  have heZero :
      e - e' = 0 :=
    (Submodule.disjoint_def.mp
      hExactRestDisjoint)
      (e - e')
      heDiffExact heDiffRest

  have heq :
      e = e' :=
    sub_eq_zero.mp heZero

  have hHCOrtho :
      (H G).HarmonicSucc n ⟂
        G.CoexactSucc n :=
    harmonic_isOrtho_coexact G n

  have hHCDisjoint :
      Disjoint
        ((H G).HarmonicSucc n)
        (G.CoexactSucc n) :=
    hHCOrtho.disjoint

  have hhDiff :
      h - h' ∈
        (H G).HarmonicSucc n :=
    (H G).HarmonicSucc n |>.sub_mem hh hh'

  have hcDiff :
      c - c' ∈
        G.CoexactSucc n :=
    (G.CoexactSucc n).sub_mem hc hc'

  have hhcZero :
      (h - h') + (c - c') = 0 := by
    subst e'
    simpa using hsum

  have hhEqNeg :
      h - h' = -(c - c') := by
    exact
      eq_neg_of_add_eq_zero_left hhcZero

  have hhDiffCoexact :
      h - h' ∈
        G.CoexactSucc n := by
    rw [hhEqNeg]
    exact
      (G.CoexactSucc n).neg_mem hcDiff

  have hhZero :
      h - h' = 0 :=
    (Submodule.disjoint_def.mp
      hHCDisjoint)
      (h - h')
      hhDiff hhDiffCoexact

  have hhEq :
      h = h' :=
    sub_eq_zero.mp hhZero

  subst h'

  have hcEq :
      c = c' := by
    simpa using hhcZero

  exact
    ⟨rfl, rfl, hcEq⟩

end finiteRealHodgeData
end

end CausalGeometry
