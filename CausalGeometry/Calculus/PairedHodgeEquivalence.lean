import CausalGeometry.Calculus.GradedHodgeCohomology
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

namespace PairedCochainTransport

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
    (P : PairedCochainTransport A B)

/-- Optional degreewise inverse law for one paired causal/restriction
transport.

This is deliberately a separate property.  Nothing in PairedCochainTransport
itself implies it. -/
structure DegreewiseInverse : Prop where

  source :
    ∀ n,
      (P.backward.map n).comp
          (P.forward.map n)
        =
      LinearMap.id

  target :
    ∀ n,
      (P.forward.map n).comp
          (P.backward.map n)
        =
      LinearMap.id

namespace DegreewiseInverse

variable (hInv : P.DegreewiseInverse)

/-- Under an explicitly supplied inverse law, each degree of the paired
transport becomes a genuine linear equivalence. -/
def degreeEquiv
    (n : ℕ) :
    C n ≃ₗ[K] D n where

  toFun :=
    P.forward.map n

  invFun :=
    P.backward.map n

  left_inv := by
    intro x
    have h :=
      LinearMap.congr_fun
        (hInv.source n) x
    simpa using h

  right_inv := by
    intro y
    have h :=
      LinearMap.congr_fun
        (hInv.target n) y
    simpa using h

  map_add' :=
    (P.forward.map n).map_add

  map_smul' :=
    (P.forward.map n).map_smul

@[simp] theorem degreeEquiv_apply
    (n : ℕ)
    (x : C n) :
    hInv.degreeEquiv n x =
      P.forward.map n x :=
  rfl

@[simp] theorem degreeEquiv_symm_apply
    (n : ℕ)
    (y : D n) :
    (hInv.degreeEquiv n).symm y =
      P.backward.map n y :=
  rfl

/-- If both directions are cochain-natural, degreewise invertibility descends
to an equivalence on positive causal cohomology. -/
def hSuccEquiv
    (hF : P.forward.Natural)
    (hB : P.backward.Natural)
    (n : ℕ) :
    A.HSucc n ≃ₗ[K] B.HSucc n where

  toFun :=
    P.forwardHSuccMap hF n

  invFun :=
    P.backwardHSuccMap hB n

  left_inv := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ z =>
        apply Quotient.sound
        change
          (((P.backward.map (n + 1)).comp
              (P.forward.map (n + 1)))
              (z : C (n + 1)) :
            C (n + 1))
            -
          (z : C (n + 1))
          ∈
        A.ExactSucc n
        have h :=
          LinearMap.congr_fun
            (hInv.source (n + 1))
            (z : C (n + 1))
        rw [h]
        simp

  right_inv := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ z =>
        apply Quotient.sound
        change
          (((P.forward.map (n + 1)).comp
              (P.backward.map (n + 1)))
              (z : D (n + 1)) :
            D (n + 1))
            -
          (z : D (n + 1))
          ∈
        B.ExactSucc n
        have h :=
          LinearMap.congr_fun
            (hInv.target (n + 1))
            (z : D (n + 1))
        rw [h]
        simp

  map_add' :=
    (P.forwardHSuccMap hF n).map_add

  map_smul' :=
    (P.forwardHSuccMap hF n).map_smul

/-- Degree-zero cohomology is equivalently preserved as well. -/
def h0Equiv
    (hF : P.forward.Natural)
    (hB : P.backward.Natural) :
    A.H0 ≃ₗ[K] B.H0 where

  toFun :=
    P.forwardH0Map hF

  invFun :=
    P.backwardH0Map hB

  left_inv := by
    intro x
    apply Subtype.ext
    have h :=
      LinearMap.congr_fun
        (hInv.source 0)
        (x : C 0)
    exact h

  right_inv := by
    intro y
    apply Subtype.ext
    have h :=
      LinearMap.congr_fun
        (hInv.target 0)
        (y : D 0)
    exact h

  map_add' :=
    (P.forwardH0Map hF).map_add

  map_smul' :=
    (P.forwardH0Map hF).map_smul

end DegreewiseInverse

variable
    (HA : GradedCausalHodgeData A)
    (HB : GradedCausalHodgeData B)

/-- Under degreewise inverse transport and two-sided Laplacian intertwining,
the harmonic sectors are linearly equivalent. -/
def harmonicSuccEquiv
    (hInv : P.DegreewiseInverse)
    (hLapF :
      ∀ n,
        (HB.laplacianSucc n).comp
            (P.forward.map (n + 1))
          =
        (P.forward.map (n + 1)).comp
            (HA.laplacianSucc n))
    (hLapB :
      ∀ n,
        (HA.laplacianSucc n).comp
            (P.backward.map (n + 1))
          =
        (P.backward.map (n + 1)).comp
            (HB.laplacianSucc n))
    (n : ℕ) :
    HA.HarmonicSucc n ≃ₗ[K]
      HB.HarmonicSucc n where

  toFun :=
    P.forwardHarmonicSuccMap
      HA HB hLapF n

  invFun :=
    P.backwardHarmonicSuccMap
      HA HB hLapB n

  left_inv := by
    intro x
    apply Subtype.ext
    have h :=
      LinearMap.congr_fun
        (hInv.source (n + 1))
        (x : C (n + 1))
    exact h

  right_inv := by
    intro y
    apply Subtype.ext
    have h :=
      LinearMap.congr_fun
        (hInv.target (n + 1))
        (y : D (n + 1))
    exact h

  map_add' :=
    (P.forwardHarmonicSuccMap
      HA HB hLapF n).map_add

  map_smul' :=
    (P.forwardHarmonicSuccMap
      HA HB hLapF n).map_smul

/-- Laplacian eigenspaces are preserved degreewise whenever Phi/Psi are true
inverse transports and both Laplacian squares commute. -/
def laplacianEigenspaceEquiv
    (hInv : P.DegreewiseInverse)
    (hLapF :
      ∀ n,
        (HB.laplacianSucc n).comp
            (P.forward.map (n + 1))
          =
        (P.forward.map (n + 1)).comp
            (HA.laplacianSucc n))
    (hLapB :
      ∀ n,
        (HA.laplacianSucc n).comp
            (P.backward.map (n + 1))
          =
        (P.backward.map (n + 1)).comp
            (HB.laplacianSucc n))
    (n : ℕ)
    (μ : K) :
    Module.End.eigenspace
        (HA.laplacianSucc n) μ
      ≃ₗ[K]
    Module.End.eigenspace
        (HB.laplacianSucc n) μ where

  toFun := fun x =>
    ⟨P.forward.map (n + 1) x, by
      apply Module.End.mem_eigenspace_iff.mpr
      have hx :
          HA.laplacianSucc n x =
            μ • (x : C (n + 1)) :=
        Module.End.mem_eigenspace_iff.mp x.2
      have h :=
        LinearMap.congr_fun
          (hLapF n)
          (x : C (n + 1))
      rw [h]
      rw [hx]
      simp⟩

  invFun := fun y =>
    ⟨P.backward.map (n + 1) y, by
      apply Module.End.mem_eigenspace_iff.mpr
      have hy :
          HB.laplacianSucc n y =
            μ • (y : D (n + 1)) :=
        Module.End.mem_eigenspace_iff.mp y.2
      have h :=
        LinearMap.congr_fun
          (hLapB n)
          (y : D (n + 1))
      rw [h]
      rw [hy]
      simp⟩

  left_inv := by
    intro x
    apply Subtype.ext
    have h :=
      LinearMap.congr_fun
        (hInv.source (n + 1))
        (x : C (n + 1))
    exact h

  right_inv := by
    intro y
    apply Subtype.ext
    have h :=
      LinearMap.congr_fun
        (hInv.target (n + 1))
        (y : D (n + 1))
    exact h

  map_add' := by
    intro x y
    apply Subtype.ext
    simp

  map_smul' := by
    intro a x
    apply Subtype.ext
    simp

/-- Hence every named Laplacian eigenspace has the same finite dimension under
an invertible Hodge transport. -/
theorem finrank_laplacianEigenspace_eq
    [∀ n, FiniteDimensional K (C n)]
    [∀ n, FiniteDimensional K (D n)]
    (hInv : P.DegreewiseInverse)
    (hLapF :
      ∀ n,
        (HB.laplacianSucc n).comp
            (P.forward.map (n + 1))
          =
        (P.forward.map (n + 1)).comp
            (HA.laplacianSucc n))
    (hLapB :
      ∀ n,
        (HA.laplacianSucc n).comp
            (P.backward.map (n + 1))
          =
        (P.backward.map (n + 1)).comp
            (HB.laplacianSucc n))
    (n : ℕ)
    (μ : K) :
    Module.finrank K
        (Module.End.eigenspace
          (HA.laplacianSucc n) μ)
      =
    Module.finrank K
        (Module.End.eigenspace
          (HB.laplacianSucc n) μ) := by
  exact
    LinearEquiv.finrank_eq
      (P.laplacianEigenspaceEquiv
        HA HB hInv hLapF hLapB n μ)

end PairedCochainTransport
end CausalGeometry
