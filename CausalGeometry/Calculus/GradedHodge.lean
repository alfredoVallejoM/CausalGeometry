import CausalGeometry.Calculus.GradedComplex
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic

namespace CausalGeometry

universe u v

/-- Hodge data on an arbitrary nonnegative graded causal cochain complex.

The codifferential and pairings are explicit structure.  Positivity,
finite-dimensionality and Hodge decomposition are deliberately not built into
the carrier. -/
structure GradedCausalHodgeData
    {K : Type u}
    {C : ℕ → Type v}
    [Field K]
    [∀ n, AddCommGroup (C n)]
    [∀ n, Module K (C n)]
    (G : GradedCausalCochainComplex K C) where

  codiff : ∀ n, C (n + 1) →ₗ[K] C n

  pairing :
    ∀ n, C n →ₗ[K] C n →ₗ[K] K

  adjoint :
    ∀ n (x : C n) (y : C (n + 1)),
      pairing (n + 1) (G.d n x) y =
        pairing n x (codiff n y)

namespace GradedCausalHodgeData

variable
    {K : Type u}
    {C : ℕ → Type v}
    [Field K]
    [∀ n, AddCommGroup (C n)]
    [∀ n, Module K (C n)]
    {G : GradedCausalCochainComplex K C}
    (H : GradedCausalHodgeData G)

/-- Degree-zero Laplacian delta_0 d_0. -/
def laplacian0 : C 0 →ₗ[K] C 0 :=
  (H.codiff 0).comp (G.d 0)

/-- Laplacian in arbitrary positive degree n+1:
d_n delta_n + delta_(n+1) d_(n+1). -/
def laplacianSucc (n : ℕ) :
    C (n + 1) →ₗ[K] C (n + 1) :=
  (G.d n).comp (H.codiff n) +
    (H.codiff (n + 1)).comp (G.d (n + 1))

def Harmonic0 : Submodule K (C 0) :=
  H.laplacian0.ker

def HarmonicSucc (n : ℕ) :
    Submodule K (C (n + 1)) :=
  (H.laplacianSucc n).ker

@[simp] theorem harmonicSucc_laplacian
    (n : ℕ)
    (x : H.HarmonicSucc n) :
    H.laplacianSucc n x = 0 :=
  x.2

end GradedCausalHodgeData

/-- Exact hypotheses required to identify positive-degree causal cohomology
with harmonic cochains in one arbitrary degree.

Keeping these as theorem obligations prevents a formal Hodge decomposition
from being silently assumed in infinite-dimensional or indefinite settings. -/
structure GradedCausalHodgeRepresentationSucc
    {K : Type u}
    {C : ℕ → Type v}
    [Field K]
    [∀ n, AddCommGroup (C n)]
    [∀ n, Module K (C n)]
    {G : GradedCausalCochainComplex K C}
    (H : GradedCausalHodgeData G)
    (n : ℕ) where

  harmonic_closed :
    H.HarmonicSucc n ≤ G.Closed (n + 1)

  closed_decompose :
    ∀ z : G.Closed (n + 1),
      ∃ e : G.ExactSucc n,
        ∃ h : H.HarmonicSucc n,
          (z : C (n + 1)) =
            (e : C (n + 1)) +
              (h : C (n + 1))

  exact_harmonic_disjoint :
    Disjoint (G.ExactSucc n) (H.HarmonicSucc n)

namespace GradedCausalHodgeRepresentationSucc

variable
    {K : Type u}
    {C : ℕ → Type v}
    [Field K]
    [∀ n, AddCommGroup (C n)]
    [∀ n, Module K (C n)]
    {G : GradedCausalCochainComplex K C}
    {H : GradedCausalHodgeData G}
    {n : ℕ}
    (R : GradedCausalHodgeRepresentationSucc H n)

/-- Harmonic cochains embedded into the closed subspace. -/
def harmonicToClosed :
    H.HarmonicSucc n →ₗ[K] G.Closed (n + 1) where
  toFun := fun h =>
    ⟨h, R.harmonic_closed h.2⟩
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro a x
    rfl

/-- Canonical map from harmonic cochains to H^(n+1). -/
def harmonicToHSucc :
    H.HarmonicSucc n →ₗ[K] G.HSucc n :=
  (G.classOfClosedSucc n).comp
    R.harmonicToClosed

theorem harmonicToHSucc_injective :
    Function.Injective R.harmonicToHSucc := by
  intro x y hxy
  have hzero :
      R.harmonicToHSucc (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]

  have hmem :
      ((x - y : H.HarmonicSucc n) :
        C (n + 1)) ∈
      G.ExactSucc n := by
    have hq :
        G.classOfClosedSucc n
            (R.harmonicToClosed (x - y)) =
          0 := hzero
    exact
      (G.classOfClosedSucc_eq_zero_iff
        n (R.harmonicToClosed (x - y))).1 hq

  have hhar :
      ((x - y : H.HarmonicSucc n) :
        C (n + 1)) ∈
      H.HarmonicSucc n :=
    (x - y).2

  have hz :
      ((x - y : H.HarmonicSucc n) :
        C (n + 1)) = 0 :=
    (Submodule.disjoint_def.mp
      R.exact_harmonic_disjoint)
      _
      hmem hhar

  apply sub_eq_zero.mp
  apply Subtype.ext
  exact hz

theorem harmonicToHSucc_surjective :
    Function.Surjective R.harmonicToHSucc := by
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
          (G.ExactInClosedSucc n)).2
      change
        ((h : H.HarmonicSucc n) :
            C (n + 1)) -
          (z : C (n + 1))
          ∈
        G.ExactSucc n
      have heq :
          ((h : H.HarmonicSucc n) :
              C (n + 1)) -
            (z : C (n + 1))
            =
          - (e : C (n + 1)) := by
        rw [hdecomp]
        abel
      rw [heq]
      exact (G.ExactSucc n).neg_mem e.2

/-- Arbitrary positive-degree algebraic causal Hodge theorem. -/
noncomputable def harmonicEquivHSucc :
    H.HarmonicSucc n ≃ₗ[K] G.HSucc n :=
  LinearEquiv.ofBijective
    R.harmonicToHSucc
    ⟨R.harmonicToHSucc_injective,
      R.harmonicToHSucc_surjective⟩

@[simp] theorem harmonicEquivHSucc_apply
    (h : H.HarmonicSucc n) :
    R.harmonicEquivHSucc h =
      R.harmonicToHSucc h :=
  rfl

theorem hSucc_subsingleton_iff_harmonic :
    Subsingleton (G.HSucc n) ↔
      Subsingleton (H.HarmonicSucc n) := by
  exact
    R.harmonicEquivHSucc.toEquiv
      .subsingleton_congr.symm

end GradedCausalHodgeRepresentationSucc
end CausalGeometry
