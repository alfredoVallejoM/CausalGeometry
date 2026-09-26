import CausalGeometry.Calculus.RelativeCohomology
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

namespace GradedLinearTransport

variable
    {K : Type u}
    {C : ℕ → Type v}
    {D : ℕ → Type w}
    [Field K]
    [∀ n, AddCommGroup (C n)]
    [∀ n, Module K (C n)]
    [∀ n, AddCommGroup (D n)]
    [∀ n, Module K (D n)]
    {A : GradedCausalCochainComplex K C}
    {B : GradedCausalCochainComplex K D}
    (F : GradedLinearTransport A B)

/-- Degreewise surjectivity hypothesis for a restriction-like cochain map.

This is the additional hypothesis needed to turn the kernel relative complex
into a short exact sequence of cochain modules. -/
def DegreewiseSurjective : Prop :=
  ∀ n,
    Function.Surjective (F.map n)

/-- Relative inclusion is injective in every degree. -/
theorem relativeInclusion_injective
    (hF : F.Natural)
    (n : ℕ) :
    Function.Injective
      ((F.relativeInclusion hF).map n) := by
  intro x y hxy
  apply Subtype.ext
  exact hxy

/-- The image of the relative inclusion is exactly the kernel of F_n. -/
theorem relativeInclusion_range_eq_ker
    (hF : F.Natural)
    (n : ℕ) :
    LinearMap.range
        ((F.relativeInclusion hF).map n)
      =
    (F.map n).ker := by
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨r, rfl⟩
    exact r.2
  · intro x hx
    refine ⟨⟨x, hx⟩, rfl⟩

/-- Exactness of relative inclusion followed by F in every degree. -/
theorem relative_exact_at_source
    (hF : F.Natural)
    (n : ℕ) :
    LinearMap.range
        ((F.relativeInclusion hF).map n)
      =
    LinearMap.ker (F.map n) :=
  F.relativeInclusion_range_eq_ker hF n

/-- Under degreewise surjectivity, each target cochain has a source lift. -/
theorem target_has_lift
    (hF : F.DegreewiseSurjective)
    (n : ℕ)
    (y : D n) :
    ∃ x : C n,
      F.map n x = y :=
  hF n y

/-- Degreewise short-exact package.

The source deliberately records the three mathematical ingredients instead of
claiming a long exact cohomology sequence before the connecting morphism is
constructed. -/
structure RelativeShortExact
    (hNat : F.Natural) : Prop where

  inclusion_injective :
    ∀ n,
      Function.Injective
        ((F.relativeInclusion hNat).map n)

  exact_middle :
    ∀ n,
      LinearMap.range
          ((F.relativeInclusion hNat).map n)
        =
      LinearMap.ker (F.map n)

  restriction_surjective :
    ∀ n,
      Function.Surjective (F.map n)

/-- Degreewise surjectivity upgrades the relative-kernel construction to a
short exact cochain sequence. -/
def relativeShortExact
    (hNat : F.Natural)
    (hSurj : F.DegreewiseSurjective) :
    F.RelativeShortExact hNat where

  inclusion_injective :=
    F.relativeInclusion_injective hNat

  exact_middle :=
    F.relative_exact_at_source hNat

  restriction_surjective :=
    hSurj

end GradedLinearTransport
end CausalGeometry
