import CausalGeometry.Variational.BilinearLegendre
import CausalGeometry.Calculus.BilinearTransport
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic

namespace CausalGeometry

universe u v w x
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalBilinear

variable {K : Type w}
variable {Fiber : Configuration S → Type x}
variable [CommRing K]
variable [∀ C, AddCommGroup (Fiber C)]
variable [∀ C, Module K (Fiber C)]

namespace Field

variable
    (B : Field (K := K) (S := S) (Fiber := Fiber))

/-- Null/gauge velocity directions of a possibly degenerate Legendre map. -/
abbrev GaugeDirections
    (C : Configuration S) :
    Submodule K (Fiber C) :=
  (B.flat C).ker

/-- Primary momentum constraint surface: covectors actually realized by some
velocity through the singular Legendre map. -/
abbrev PrimaryConstraint
    (C : Configuration S) :
    Submodule K (Module.Dual K (Fiber C)) :=
  (B.flat C).range

/-- Physical velocity space after quotienting null Legendre directions. -/
abbrev ReducedVelocity
    (C : Configuration S) :=
  Fiber C ⧸ B.GaugeDirections C

/-- Constraint obstruction/cokernel: nonzero classes are momentum covectors
that cannot be produced by any velocity. -/
abbrev ConstraintCokernel
    (C : Configuration S) :=
  Module.Dual K (Fiber C) ⧸
    B.PrimaryConstraint C

/-- Canonical primary-constraint class of one covector. -/
def primaryConstraintClass
    (C : Configuration S) :
    Module.Dual K (Fiber C) →ₗ[K]
      B.ConstraintCokernel C :=
  Submodule.mkQ (B.PrimaryConstraint C)

@[simp] theorem primaryConstraintClass_eq_zero_iff
    (C : Configuration S)
    (omega : Module.Dual K (Fiber C)) :
    B.primaryConstraintClass C omega = 0 ↔
      omega ∈ B.PrimaryConstraint C := by
  exact Submodule.Quotient.mk_eq_zero

/-- A momentum is primary-admissible exactly when it is Legendre-related to
some velocity. -/
theorem mem_primaryConstraint_iff_exists_legendre
    (C : Configuration S)
    (omega : Module.Dual K (Fiber C)) :
    omega ∈ B.PrimaryConstraint C ↔
      ∃ x : Fiber C,
        (B.legendreCorrespondence C).relates x omega := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    exact hx
  · rintro ⟨x, hx⟩
    exact ⟨x, hx⟩

/-- The primary constraint class vanishes exactly for realizable Legendre
momenta. -/
theorem primaryConstraintClass_eq_zero_iff_exists_legendre
    (C : Configuration S)
    (omega : Module.Dual K (Fiber C)) :
    B.primaryConstraintClass C omega = 0 ↔
      ∃ x : Fiber C,
        (B.legendreCorrespondence C).relates x omega := by
  rw [B.primaryConstraintClass_eq_zero_iff]
  exact B.mem_primaryConstraint_iff_exists_legendre C omega

/-- First isomorphism theorem for a singular causal Legendre map.

The physically distinguishable velocity quotient is canonically equivalent to
the primary momentum surface. -/
noncomputable def reducedVelocityEquivPrimary
    (C : Configuration S) :
    B.ReducedVelocity C ≃ₗ[K]
      B.PrimaryConstraint C :=
  (B.flat C).quotKerEquivRange

/-- Regularity at one configuration means no nonzero gauge/null direction. -/
def LegendreRegularAt
    (C : Configuration S) : Prop :=
  B.GaugeDirections C = ⊥

/-- Singularity at one configuration means a nontrivial null direction exists. -/
def LegendreSingularAt
    (C : Configuration S) : Prop :=
  B.GaugeDirections C ≠ ⊥

theorem legendreRegularAt_iff_flat_injective
    (C : Configuration S) :
    B.LegendreRegularAt C ↔
      Function.Injective (B.flat C) := by
  unfold LegendreRegularAt GaugeDirections
  exact LinearMap.ker_eq_bot.symm

theorem legendreSingularAt_iff_exists_gauge
    (C : Configuration S) :
    B.LegendreSingularAt C ↔
      ∃ x : Fiber C,
        x ≠ 0 ∧
          B.flat C x = 0 := by
  rw [LegendreSingularAt]
  constructor
  · intro hne
    have hnontrivial :
        ∃ x : B.GaugeDirections C, x ≠ 0 := by
      by_contra h
      push_neg at h
      apply hne
      apply Submodule.eq_bot_iff.mpr
      intro x hx
      exact h ⟨x, hx⟩
    rcases hnontrivial with ⟨x, hx⟩
    exact ⟨x, by
      intro h0
      apply hx
      apply Subtype.ext
      exact h0, x.2⟩
  · rintro ⟨x, hx, hflat⟩ hbot
    have hxmem :
        x ∈ B.GaugeDirections C :=
      hflat
    rw [hbot] at hxmem
    exact hx hxmem

/-- Left nondegeneracy implies Legendre regularity, but does not by itself
claim surjectivity onto all covectors over arbitrary modules. -/
theorem legendreRegularAt_of_leftNondegenerate
    (hnd : B.LeftNondegenerate)
    (C : Configuration S) :
    B.LegendreRegularAt C := by
  rw [B.legendreRegularAt_iff_flat_injective C]
  exact B.flat_injective hnd C

end Field

namespace Field

variable
    (B : Field (K := K) (S := S) (Fiber := Fiber))
    (nabla : DependentLinearEquivConnection K S Fiber)

/-- Preserved bilinear geometry sends gauge/null directions to gauge/null
directions. -/
def gaugeDirectionTransport
    (hpres : B.PreservedByEquiv nabla)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    B.GaugeDirections C →ₗ[K]
      B.GaugeDirections (S.extend C e h) where

  toFun := fun x =>
    ⟨nabla.transport C e h x, by
      change
        B.flat (S.extend C e h)
            (nabla.transport C e h x)
          =
        0
      rw [B.flat_natural nabla hpres]
      rw [x.2]
      simp⟩

  map_add' := by
    intro x y
    apply Subtype.ext
    simp

  map_smul' := by
    intro a x
    apply Subtype.ext
    simp

/-- The forward covector transport preserves the primary constraint surface. -/
def primaryConstraintTransport
    (hpres : B.PreservedByEquiv nabla)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    B.PrimaryConstraint C →ₗ[K]
      B.PrimaryConstraint (S.extend C e h) where

  toFun := fun omega => by
    rcases omega.2 with ⟨x, hx⟩
    refine
      ⟨nabla.covectorPushforward C e h omega, ?_⟩
    refine
      ⟨nabla.transport C e h x, ?_⟩
    rw [← hx]
    exact
      (B.flat_natural
        nabla hpres C e h x).symm

  map_add' := by
    intro x y
    apply Subtype.ext
    simp

  map_smul' := by
    intro a x
    apply Subtype.ext
    simp

/-- A preserved primary-admissible momentum remains primary-admissible after
one causal transport step. -/
theorem primaryConstraint_preserved
    (hpres : B.PreservedByEquiv nabla)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e)
    (omega : Module.Dual K (Fiber C))
    (homega : omega ∈ B.PrimaryConstraint C) :
    nabla.covectorPushforward C e h omega ∈
      B.PrimaryConstraint (S.extend C e h) := by
  exact
    (B.primaryConstraintTransport
      nabla hpres C e h)
      ⟨omega, homega⟩ |>.2

/-- Gauge dimension/degeneracy is transported injectively along an invertible
preserved connection. -/
theorem gaugeDirectionTransport_injective
    (hpres : B.PreservedByEquiv nabla)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    Function.Injective
      (B.gaugeDirectionTransport
        nabla hpres C e h) := by
  intro x y hxy
  apply Subtype.ext
  exact
    (nabla.transport C e h).injective
      (congrArg Subtype.val hxy)

end Field
end CausalBilinear
end CausalGeometry
