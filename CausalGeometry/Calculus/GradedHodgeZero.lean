import CausalGeometry.Calculus.GradedHodge
import Mathlib.Tactic

namespace CausalGeometry

universe u v

/-- Exact hypotheses needed to identify harmonic degree zero with H0.

In degree zero there is no incoming exact subspace, so the representation
problem reduces to equality between ker(Delta_0) and ker(d_0). -/
structure GradedCausalHodgeRepresentation0
    {K : Type u}
    {C : ℕ → Type v}
    [Field K]
    [∀ n, AddCommGroup (C n)]
    [∀ n, Module K (C n)]
    {G : GradedCausalCochainComplex K C}
    (H : GradedCausalHodgeData G) where

  harmonic_closed :
    H.Harmonic0 ≤ G.Closed 0

  closed_harmonic :
    G.Closed 0 ≤ H.Harmonic0

namespace GradedCausalHodgeRepresentation0

variable
    {K : Type u}
    {C : ℕ → Type v}
    [Field K]
    [∀ n, AddCommGroup (C n)]
    [∀ n, Module K (C n)]
    {G : GradedCausalCochainComplex K C}
    {H : GradedCausalHodgeData G}
    (R : GradedCausalHodgeRepresentation0 H)

/-- Degree-zero causal Hodge theorem under the exact equality-of-kernels
hypotheses. -/
def harmonicEquivH0 :
    H.Harmonic0 ≃ₗ[K] G.H0 where
  toFun := fun h =>
    ⟨h, R.harmonic_closed h.2⟩
  invFun := fun z =>
    ⟨z, R.closed_harmonic z.2⟩
  left_inv := by
    intro x
    apply Subtype.ext
    rfl
  right_inv := by
    intro x
    apply Subtype.ext
    rfl
  map_add' := by
    intro x y
    apply Subtype.ext
    rfl
  map_smul' := by
    intro a x
    apply Subtype.ext
    rfl

theorem h0_subsingleton_iff_harmonic0 :
    Subsingleton G.H0 ↔
      Subsingleton H.Harmonic0 := by
  exact
    R.harmonicEquivH0.toEquiv
      .subsingleton_congr.symm

end GradedCausalHodgeRepresentation0
end CausalGeometry
