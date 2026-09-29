import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic

/-!
# Defects of heterogeneous linear squares

No inverse, flatness, finite dimension or square-zero differential is assumed.
This is an algebraic producer for tensor exchange and the EXISTING graded
causal differential. It does not replace either construction.
-/
namespace CausalGeometry.LinearSquare

universe u
variable {K : Type u} [CommRing K]
variable {A₀ A₁ A₂ B₀ B₁ B₂ C₀ C₁ : Type*}
variable [AddCommGroup A₀] [Module K A₀] [AddCommGroup A₁] [Module K A₁]
variable [AddCommGroup A₂] [Module K A₂] [AddCommGroup B₀] [Module K B₀]
variable [AddCommGroup B₁] [Module K B₁] [AddCommGroup B₂] [Module K B₂]
variable [AddCommGroup C₀] [Module K C₀] [AddCommGroup C₁] [Module K C₁]

/-- Target edge after source transport, minus target transport after source edge. -/
def defect (a : A₀ →ₗ[K] A₁) (b : B₀ →ₗ[K] B₁)
    (f₀ : A₀ →ₗ[K] B₀) (f₁ : A₁ →ₗ[K] B₁) : A₀ →ₗ[K] B₁ :=
  b.comp f₀ - f₁.comp a

@[simp] theorem defect_apply (a : A₀ →ₗ[K] A₁) (b : B₀ →ₗ[K] B₁)
    (f₀ : A₀ →ₗ[K] B₀) (f₁ : A₁ →ₗ[K] B₁) (x : A₀) :
    defect a b f₀ f₁ x = b (f₀ x) - f₁ (a x) := rfl

theorem defect_eq_zero_iff (a : A₀ →ₗ[K] A₁) (b : B₀ →ₗ[K] B₁)
    (f₀ : A₀ →ₗ[K] B₀) (f₁ : A₁ →ₗ[K] B₁) :
    defect a b f₀ f₁ = 0 ↔ b.comp f₀ = f₁.comp a := sub_eq_zero

/-- Horizontal pasting: D(GF)=D(G)F+G D(F), with independent endpoint maps. -/
theorem horizontal (a : A₀ →ₗ[K] A₁) (b : B₀ →ₗ[K] B₁) (c : C₀ →ₗ[K] C₁)
    (f₀ : A₀ →ₗ[K] B₀) (f₁ : A₁ →ₗ[K] B₁)
    (g₀ : B₀ →ₗ[K] C₀) (g₁ : B₁ →ₗ[K] C₁) :
    defect a c (g₀.comp f₀) (g₁.comp f₁) =
      (defect b c g₀ g₁).comp f₀ + g₁.comp (defect a b f₀ f₁) := by
  ext x
  simp only [defect_apply, LinearMap.comp_apply, LinearMap.add_apply, map_sub]
  abel

/-- Vertical pasting: defects along successive process steps telescope. -/
theorem vertical (a : A₀ →ₗ[K] A₁) (a' : A₁ →ₗ[K] A₂)
    (b : B₀ →ₗ[K] B₁) (b' : B₁ →ₗ[K] B₂)
    (f₀ : A₀ →ₗ[K] B₀) (f₁ : A₁ →ₗ[K] B₁) (f₂ : A₂ →ₗ[K] B₂) :
    defect (a'.comp a) (b'.comp b) f₀ f₂ =
      b'.comp (defect a b f₀ f₁) + (defect a' b' f₁ f₂).comp a := by
  ext x
  simp only [defect_apply, LinearMap.comp_apply, LinearMap.add_apply, map_sub]
  abel

@[simp] theorem identity_transport (a : A₀ →ₗ[K] A₁) :
    defect a a LinearMap.id LinearMap.id = 0 := by
  ext x
  simp [defect]

@[simp] theorem identity_edges (f : A₀ →ₗ[K] B₀) :
    defect LinearMap.id LinearMap.id f f = 0 := by
  ext x
  simp [defect]

/-- Additivity holds in the pair of transport maps, not in F↦F⊗F. -/
theorem add_transport (a : A₀ →ₗ[K] A₁) (b : B₀ →ₗ[K] B₁)
    (f₀ g₀ : A₀ →ₗ[K] B₀) (f₁ g₁ : A₁ →ₗ[K] B₁) :
    defect a b (f₀ + g₀) (f₁ + g₁) =
      defect a b f₀ f₁ + defect a b g₀ g₁ := by
  ext x
  simp [defect]
  abel

/-- The largest linear domain on which THIS square commutes pointwise.
It is not automatically invariant under a process or future contexts. -/
def compatibleDomain (a : A₀ →ₗ[K] A₁) (b : B₀ →ₗ[K] B₁)
    (f₀ : A₀ →ₗ[K] B₀) (f₁ : A₁ →ₗ[K] B₁) : Submodule K A₀ :=
  (defect a b f₀ f₁).ker

@[simp] theorem mem_compatibleDomain (a : A₀ →ₗ[K] A₁) (b : B₀ →ₗ[K] B₁)
    (f₀ : A₀ →ₗ[K] B₀) (f₁ : A₁ →ₗ[K] B₁) (x : A₀) :
    x ∈ compatibleDomain a b f₀ f₁ ↔ b (f₀ x) = f₁ (a x) := by
  change defect a b f₀ f₁ x = 0 ↔ _
  exact sub_eq_zero

theorem compatibleDomain_maximal (a : A₀ →ₗ[K] A₁) (b : B₀ →ₗ[K] B₁)
    (f₀ : A₀ →ₗ[K] B₀) (f₁ : A₁ →ₗ[K] B₁) (L : Submodule K A₀) :
    L ≤ compatibleDomain a b f₀ f₁ ↔ ∀ x ∈ L, b (f₀ x) = f₁ (a x) := by
  constructor
  · intro h x hx
    exact (mem_compatibleDomain a b f₀ f₁ x).mp (h hx)
  · intro h x hx
    exact (mem_compatibleDomain a b f₀ f₁ x).mpr (h x hx)

/-- Local compatibility propagates only when the intermediate input is compatible too. -/
theorem vertical_on_domain (a : A₀ →ₗ[K] A₁) (a' : A₁ →ₗ[K] A₂)
    (b : B₀ →ₗ[K] B₁) (b' : B₁ →ₗ[K] B₂)
    (f₀ : A₀ →ₗ[K] B₀) (f₁ : A₁ →ₗ[K] B₁) (f₂ : A₂ →ₗ[K] B₂)
    (x : A₀) (h₀ : defect a b f₀ f₁ x = 0)
    (h₁ : defect a' b' f₁ f₂ (a x) = 0) :
    defect (a'.comp a) (b'.comp b) f₀ f₂ x = 0 := by
  rw [vertical]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, h₀, h₁, map_zero, add_zero]

end CausalGeometry.LinearSquare
