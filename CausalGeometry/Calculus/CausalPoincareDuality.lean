import CausalGeometry.Calculus.GradedHodge
import CausalGeometry.Calculus.FiniteRealHodge
import Mathlib.Tactic

namespace CausalGeometry

universe u v

/-- A Hodge-star-like equivalence between two positive degrees of one graded
causal Hodge complex, together with the exact spectral compatibility needed
for cohomological duality.

No Poincare duality is inferred from a vector-space isomorphism alone:
intertwining the two Hodge Laplacians is explicit data. -/
structure CausalHodgeStarIntertwinerSucc
    {K : Type u}
    {C : ℕ → Type v}
    [Field K]
    [∀ n, AddCommGroup (C n)]
    [∀ n, Module K (C n)]
    {G : GradedCausalCochainComplex K C}
    (H : GradedCausalHodgeData G)
    (n m : ℕ) where

  star :
    C (n + 1) ≃ₗ[K]
      C (m + 1)

  laplacian_intertwines :
    (H.laplacianSucc m).comp
        star.toLinearMap
      =
    star.toLinearMap.comp
        (H.laplacianSucc n)

namespace CausalHodgeStarIntertwinerSucc

variable
    {K : Type u}
    {C : ℕ → Type v}
    [Field K]
    [∀ n, AddCommGroup (C n)]
    [∀ n, Module K (C n)]
    {G : GradedCausalCochainComplex K C}
    {H : GradedCausalHodgeData G}
    {n m : ℕ}
    (D : CausalHodgeStarIntertwinerSucc H n m)

/-- A Laplacian-intertwining Hodge star maps harmonic cochains to harmonic
cochains. -/
def harmonicEquiv :
    H.HarmonicSucc n ≃ₗ[K]
      H.HarmonicSucc m where

  toFun := fun x =>
    ⟨D.star x, by
      change
        H.laplacianSucc m (D.star x) = 0
      have h :=
        LinearMap.congr_fun
          D.laplacian_intertwines x
      rw [x.2, map_zero] at h
      exact h⟩

  invFun := fun y =>
    ⟨D.star.symm y, by
      apply D.star.injective
      have h :=
        LinearMap.congr_fun
          D.laplacian_intertwines
          (D.star.symm y)
      simp only [
        LinearEquiv.apply_symm_apply
      ] at h
      change
        D.star
          (H.laplacianSucc n
            (D.star.symm y))
          =
        0
      rw [← h]
      rw [y.2]
      simp⟩

  left_inv := by
    intro x
    apply Subtype.ext
    simp

  right_inv := by
    intro y
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

/-- Poincare-type cohomology duality obtained from:
1. Hodge representation in the source degree,
2. a Laplacian-intertwining star,
3. Hodge representation in the complementary degree. -/
noncomputable def cohomologyEquiv
    (Rn :
      GradedCausalHodgeRepresentationSucc
        H n)
    (Rm :
      GradedCausalHodgeRepresentationSucc
        H m) :
    G.HSucc n ≃ₗ[K]
      G.HSucc m :=
  Rn.harmonicEquivHSucc.symm
    |>.trans D.harmonicEquiv
    |>.trans Rm.harmonicEquivHSucc

end CausalHodgeStarIntertwinerSucc

namespace finiteRealHodgeData

noncomputable section

variable
    {C : ℕ → Type v}
    [∀ n, NormedAddCommGroup (C n)]
    [∀ n, InnerProductSpace ℝ (C n)]
    [∀ n, FiniteDimensional ℝ (C n)]
    (G : GradedCausalCochainComplex ℝ C)

/-- In the finite-dimensional real sector, a Laplacian-intertwining Hodge
star automatically induces cohomology duality because both Hodge
representation hypotheses are already theorems. -/
noncomputable def cohomologyDualityOfStar
    {n m : ℕ}
    (D :
      CausalHodgeStarIntertwinerSucc
        (H G) n m) :
    G.HSucc n ≃ₗ[ℝ]
      G.HSucc m :=
  D.cohomologyEquiv
    (representationSucc G n)
    (representationSucc G m)

end
end finiteRealHodgeData

end CausalGeometry
