import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic

namespace CausalGeometry

universe u v

/-- An unbounded nonnegative causal cochain complex.

The carrier family is indexed by natural degree.  The only structural law
bundled into the complex is d^2 = 0.  No Hodge decomposition, pairing,
finite-dimensionality, positivity or realization theorem is assumed here. -/
structure GradedCausalCochainComplex
    (K : Type u)
    (C : ℕ → Type v)
    [Field K]
    [∀ n, AddCommGroup (C n)]
    [∀ n, Module K (C n)] where

  d : ∀ n, C n →ₗ[K] C (n + 1)

  d_sq :
    ∀ n,
      (d (n + 1)).comp (d n) = 0

namespace GradedCausalCochainComplex

variable
    {K : Type u}
    {C : ℕ → Type v}
    [Field K]
    [∀ n, AddCommGroup (C n)]
    [∀ n, Module K (C n)]
    (G : GradedCausalCochainComplex K C)

/-- Closed cochains in arbitrary degree. -/
def Closed (n : ℕ) : Submodule K (C n) :=
  (G.d n).ker

/-- Exact cochains in successor degree n+1. -/
def ExactSucc (n : ℕ) : Submodule K (C (n + 1)) :=
  (G.d n).range

/-- d^2=0 implies that every exact successor-degree cochain is closed. -/
theorem exactSucc_le_closedSucc (n : ℕ) :
    G.ExactSucc n ≤ G.Closed (n + 1) := by
  intro x hx
  rcases hx with ⟨a, rfl⟩
  change G.d (n + 1) (G.d n a) = 0
  have h :=
    LinearMap.congr_fun (G.d_sq n) a
  simpa using h

/-- Exact cochains viewed as a submodule of closed cochains. -/
def ExactInClosedSucc (n : ℕ) :
    Submodule K (G.Closed (n + 1)) :=
  (G.ExactSucc n).comap
    (G.Closed (n + 1)).subtype

/-- Degree-zero cohomology.  There is no negative incoming differential. -/
abbrev H0 :=
  G.Closed 0

/-- Cohomology in degree n+1. -/
abbrev HSucc (n : ℕ) :=
  G.Closed (n + 1) ⧸ G.ExactInClosedSucc n

/-- Canonical quotient map from closed degree n+1 cochains to H^(n+1). -/
def classOfClosedSucc (n : ℕ) :
    G.Closed (n + 1) →ₗ[K] G.HSucc n :=
  Submodule.mkQ (G.ExactInClosedSucc n)

@[simp] theorem classOfClosedSucc_eq_zero_iff
    (n : ℕ)
    (x : G.Closed (n + 1)) :
    G.classOfClosedSucc n x = 0 ↔
      (x : C (n + 1)) ∈ G.ExactSucc n := by
  change
    Submodule.Quotient.mk x = 0 ↔
      _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

/-- Pointwise form of d^2=0. -/
@[simp] theorem d_d (n : ℕ) (x : C n) :
    G.d (n + 1) (G.d n x) = 0 := by
  have h :=
    LinearMap.congr_fun (G.d_sq n) x
  simpa using h

end GradedCausalCochainComplex
end CausalGeometry
