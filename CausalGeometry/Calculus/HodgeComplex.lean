import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic

namespace CausalGeometry

universe u v₀ v₁ v₂

/-- Three-term linear causal cochain complex.

This is the finite/linear target of a causal realization; it is deliberately
abstracted from the raw event/configuration implementation. -/
structure CausalCochainComplex
    (K : Type u)
    (C0 : Type v₀)
    (C1 : Type v₁)
    (C2 : Type v₂)
    [Field K]
    [AddCommGroup C0] [Module K C0]
    [AddCommGroup C1] [Module K C1]
    [AddCommGroup C2] [Module K C2] where
  d0 : C0 →ₗ[K] C1
  d1 : C1 →ₗ[K] C2

  d_sq :
    d1.comp d0 = 0

namespace CausalCochainComplex

variable
    {K : Type u}
    {C0 : Type v₀}
    {C1 : Type v₁}
    {C2 : Type v₂}
    [Field K]
    [AddCommGroup C0] [Module K C0]
    [AddCommGroup C1] [Module K C1]
    [AddCommGroup C2] [Module K C2]
    (C : CausalCochainComplex K C0 C1 C2)

/-- Closed degree-one cochains. -/
def Closed1 : Submodule K C1 :=
  C.d1.ker

/-- Exact degree-one cochains. -/
def Exact1 : Submodule K C1 :=
  C.d0.range

/-- Exact cochains are closed by d^2=0. -/
theorem exact1_le_closed1 :
    C.Exact1 ≤ C.Closed1 := by
  intro x hx
  rcases hx with ⟨a, rfl⟩
  change C.d1 (C.d0 a) = 0
  have h :=
    LinearMap.congr_fun C.d_sq a
  simpa using h

/-- Exact degree-one cochains considered inside the closed submodule. -/
def ExactInClosed1 :
    Submodule K C.Closed1 :=
  C.Exact1.comap C.Closed1.subtype

/-- First cohomology of the abstract linear causal complex. -/
abbrev H1 :=
  C.Closed1 ⧸ C.ExactInClosed1

/-- Canonical class map from closed cochains. -/
def classOfClosed1 :
    C.Closed1 →ₗ[K] C.H1 :=
  Submodule.mkQ C.ExactInClosed1

@[simp] theorem classOfClosed1_eq_zero_iff
    (x : C.Closed1) :
    C.classOfClosed1 x = 0 ↔
      (x : C1) ∈ C.Exact1 := by
  change
    Submodule.Quotient.mk x = 0 ↔
      _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

end CausalCochainComplex

/-- Algebraic Hodge data on a three-term causal complex.

The codifferentials are explicit maps. Pairings certify their intended
adjoint meaning but no positivity or orthogonal decomposition is inferred from
the carrier. -/
structure CausalHodgeData
    {K : Type u}
    {C0 : Type v₀}
    {C1 : Type v₁}
    {C2 : Type v₂}
    [Field K]
    [AddCommGroup C0] [Module K C0]
    [AddCommGroup C1] [Module K C1]
    [AddCommGroup C2] [Module K C2]
    (C : CausalCochainComplex K C0 C1 C2) where

  codiff0 : C1 →ₗ[K] C0
  codiff1 : C2 →ₗ[K] C1

  pairing0 :
    C0 →ₗ[K] C0 →ₗ[K] K

  pairing1 :
    C1 →ₗ[K] C1 →ₗ[K] K

  pairing2 :
    C2 →ₗ[K] C2 →ₗ[K] K

  adjoint0 :
    ∀ x y,
      pairing1 (C.d0 x) y =
        pairing0 x (codiff0 y)

  adjoint1 :
    ∀ x y,
      pairing2 (C.d1 x) y =
        pairing1 x (codiff1 y)

namespace CausalHodgeData

variable
    {K : Type u}
    {C0 : Type v₀}
    {C1 : Type v₁}
    {C2 : Type v₂}
    [Field K]
    [AddCommGroup C0] [Module K C0]
    [AddCommGroup C1] [Module K C1]
    [AddCommGroup C2] [Module K C2]
    {C : CausalCochainComplex K C0 C1 C2}
    (H : CausalHodgeData C)

/-- Degree-zero Hodge Laplacian δ₀ d₀. -/
def laplacian0 : C0 →ₗ[K] C0 :=
  H.codiff0.comp C.d0

/-- Degree-one Hodge Laplacian d₀δ₀ + δ₁d₁. -/
def laplacian1 : C1 →ₗ[K] C1 :=
  C.d0.comp H.codiff0 +
    H.codiff1.comp C.d1

/-- Degree-two Hodge Laplacian d₁δ₁. -/
def laplacian2 : C2 →ₗ[K] C2 :=
  C.d1.comp H.codiff1

/-- Harmonic degree-zero cochains. -/
def Harmonic0 : Submodule K C0 :=
  H.laplacian0.ker

/-- Harmonic degree-one cochains. -/
def Harmonic1 : Submodule K C1 :=
  H.laplacian1.ker

/-- Harmonic degree-two cochains. -/
def Harmonic2 : Submodule K C2 :=
  H.laplacian2.ker

@[simp] theorem harmonic1_laplacian
    (x : H.Harmonic1) :
    H.laplacian1 x = 0 :=
  x.2

end CausalHodgeData

/-- Exact hypotheses needed to identify H1 with harmonic degree-one cochains.

These are theorem obligations, not fields smuggled into CausalHodgeData:
1. harmonic cochains are closed;
2. every closed cochain differs from a harmonic one by an exact cochain;
3. exact and harmonic submodules meet only at zero. -/
structure CausalHodgeRepresentation
    {K : Type u}
    {C0 : Type v₀}
    {C1 : Type v₁}
    {C2 : Type v₂}
    [Field K]
    [AddCommGroup C0] [Module K C0]
    [AddCommGroup C1] [Module K C1]
    [AddCommGroup C2] [Module K C2]
    {C : CausalCochainComplex K C0 C1 C2}
    (H : CausalHodgeData C) where

  harmonic_closed :
    H.Harmonic1 ≤ C.Closed1

  closed_decompose :
    ∀ z : C.Closed1,
      ∃ e : C.Exact1,
        ∃ h : H.Harmonic1,
          (z : C1) =
            (e : C1) + (h : C1)

  exact_harmonic_disjoint :
    Disjoint C.Exact1 H.Harmonic1

namespace CausalHodgeRepresentation

variable
    {K : Type u}
    {C0 : Type v₀}
    {C1 : Type v₁}
    {C2 : Type v₂}
    [Field K]
    [AddCommGroup C0] [Module K C0]
    [AddCommGroup C1] [Module K C1]
    [AddCommGroup C2] [Module K C2]
    {C : CausalCochainComplex K C0 C1 C2}
    {H : CausalHodgeData C}
    (R : CausalHodgeRepresentation H)

/-- Harmonic cochains embedded into the closed subspace. -/
def harmonicToClosed :
    H.Harmonic1 →ₗ[K] C.Closed1 where
  toFun := fun h =>
    ⟨h, R.harmonic_closed h.2⟩
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro a x
    rfl

/-- Canonical harmonic representative map into H1. -/
def harmonicToH1 :
    H.Harmonic1 →ₗ[K] C.H1 :=
  C.classOfClosed1.comp
    R.harmonicToClosed

/-- Distinct harmonic cochains define distinct cohomology classes. -/
theorem harmonicToH1_injective :
    Function.Injective R.harmonicToH1 := by
  intro x y hxy
  have hzero :
      R.harmonicToH1 (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]

  have hmem :
      ((x - y : H.Harmonic1) : C1) ∈
        C.Exact1 := by
    have hq :
        C.classOfClosed1
            (R.harmonicToClosed (x - y)) =
          0 := hzero
    exact
      (C.classOfClosed1_eq_zero_iff
        (R.harmonicToClosed (x - y))).1 hq

  have hhar :
      ((x - y : H.Harmonic1) : C1) ∈
        H.Harmonic1 :=
    (x - y).2

  have hz :
      ((x - y : H.Harmonic1) : C1) = 0 :=
    (Submodule.disjoint_def.mp
      R.exact_harmonic_disjoint)
      _
      hmem hhar

  apply sub_eq_zero.mp
  apply Subtype.ext
  exact hz

/-- Every H1 class has a harmonic representative. -/
theorem harmonicToH1_surjective :
    Function.Surjective R.harmonicToH1 := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ z =>
      rcases R.closed_decompose z with
        ⟨e, h, hdecomp⟩
      refine ⟨h, ?_⟩
      change
        Submodule.Quotient.mk
            (R.harmonicToClosed h)
          =
        Submodule.Quotient.mk z
      apply
        (Submodule.Quotient.eq
          C.ExactInClosed1).2
      change
        ((h : H.Harmonic1) : C1) -
            (z : C1)
          ∈
        C.Exact1
      have heq :
          ((h : H.Harmonic1) : C1) -
              (z : C1)
            =
          - (e : C1) := by
        rw [hdecomp]
        abel
      rw [heq]
      exact C.Exact1.neg_mem e.2

/-- Algebraic Hodge theorem in degree one under the explicit representation
hypotheses. -/
noncomputable def harmonicEquivH1 :
    H.Harmonic1 ≃ₗ[K] C.H1 :=
  LinearEquiv.ofBijective
    R.harmonicToH1
    ⟨R.harmonicToH1_injective,
      R.harmonicToH1_surjective⟩

@[simp] theorem harmonicEquivH1_apply
    (h : H.Harmonic1) :
    R.harmonicEquivH1 h =
      R.harmonicToH1 h :=
  rfl

/-- H1 vanishes exactly when the harmonic degree-one space is trivial. -/
theorem h1_subsingleton_iff_harmonic1 :
    Subsingleton C.H1 ↔
      Subsingleton H.Harmonic1 := by
  exact
    R.harmonicEquivH1.toEquiv
      .subsingleton_congr.symm

end CausalHodgeRepresentation
end CausalGeometry
