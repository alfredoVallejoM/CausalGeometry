import CausalGeometry.Completion.LocalProjectiveField
import CausalGeometry.Completion.LocalProjectiveCharts
import Mathlib.LinearAlgebra.Span.Basic

namespace CausalGeometry

universe u

namespace LocalProjectivePair

variable {F : Type u} [Field F]

/-- The affine projective chart [1:t] is exactly the line spanned by (1,t). -/
theorem lineSubmodule_affine
    (t : F) :
    lineSubmodule
        (Quotient.mk _ (affine t)) =
      F ∙ ((1, t) : F × F) := by
  unfold lineSubmodule
  rw [lineEquivProjectivization_apply_mk]
  unfold pairToProjectivization
  rw [Projectivization.submodule_mk]

/-- Coordinate equation for the affine line [1:t]. -/
theorem mem_lineSubmodule_affine_iff
    (t : F)
    (z : F × F) :
    z ∈ lineSubmodule
        (Quotient.mk _ (affine t)) ↔
      z.2 = t * z.1 := by
  rw [lineSubmodule_affine]
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    have hx := congrArg Prod.fst ha
    have hy := congrArg Prod.snd ha
    simp at hx hy
    rw [← hx] at hy
    simpa [mul_comm] using hy.symm
  · intro hz
    refine ⟨z.1, ?_⟩
    apply Prod.ext
    · simp
    · simp [hz, mul_comm]

/-- The infinity chart [u:1] is exactly the line spanned by (u,1). -/
theorem lineSubmodule_infinity
    (u : Nonunit F) :
    lineSubmodule
        (Quotient.mk _ (infinityChart u)) =
      F ∙ ((u.1, 1) : F × F) := by
  unfold lineSubmodule
  rw [lineEquivProjectivization_apply_mk]
  unfold pairToProjectivization
  rw [Projectivization.submodule_mk]

/-- Coordinate equation for the infinity line [u:1]. -/
theorem mem_lineSubmodule_infinity_iff
    (u : Nonunit F)
    (z : F × F) :
    z ∈ lineSubmodule
        (Quotient.mk _ (infinityChart u)) ↔
      z.1 = u.1 * z.2 := by
  rw [lineSubmodule_infinity]
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    have hx := congrArg Prod.fst ha
    have hy := congrArg Prod.snd ha
    simp at hx hy
    rw [← hy] at hx
    simpa [mul_comm] using hx.symm
  · intro hz
    refine ⟨z.2, ?_⟩
    apply Prod.ext
    · simp [hz, mul_comm]
    · simp

/-- Coordinate equation of an arbitrary local-projective field point, exposed
through its canonical chart. -/
theorem mem_lineSubmodule_iff_chart
    (q : Line F)
    (z : F × F) :
    match (chartEquiv (R := F)).symm q with
    | Sum.inl t =>
        z ∈ lineSubmodule q ↔
          z.2 = t * z.1
    | Sum.inr u =>
        z ∈ lineSubmodule q ↔
          z.1 = u.1 * z.2 := by
  let c :=
    (chartEquiv (R := F)).symm q
  have hq :
      chartEquiv c = q :=
    (chartEquiv (R := F)).apply_symm_apply q
  cases hc : c with
  | inl t =>
      have hline :
          q =
            Quotient.mk _ (affine t) := by
        rw [← hq]
        rfl
      simpa [hline] using
        mem_lineSubmodule_affine_iff
          t z
  | inr u =>
      have hline :
          q =
            Quotient.mk _ (infinityChart u) := by
        rw [← hq]
        rfl
      simpa [hline] using
        mem_lineSubmodule_infinity_iff
          u z

end LocalProjectivePair
end CausalGeometry
