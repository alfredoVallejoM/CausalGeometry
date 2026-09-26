import CausalGeometry.Calculus.GradedHodge
import CausalGeometry.Calculus.PairedCochainTransport
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
    (HA : GradedCausalHodgeData A)
    (HB : GradedCausalHodgeData B)

/-- Failure of Phi to commute with the codifferential. -/
def forwardCodiffDefect (n : ℕ) :
    C (n + 1) →ₗ[K] D n :=
  (HB.codiff n).comp
      (P.forward.map (n + 1)) -
    (P.forward.map n).comp
      (HA.codiff n)

/-- Failure of Psi to commute with the codifferential. -/
def backwardCodiffDefect (n : ℕ) :
    D (n + 1) →ₗ[K] C n :=
  (HA.codiff n).comp
      (P.backward.map (n + 1)) -
    (P.backward.map n).comp
      (HB.codiff n)

def ForwardCodiffNatural : Prop :=
  ∀ n,
    (HB.codiff n).comp
        (P.forward.map (n + 1)) =
      (P.forward.map n).comp
        (HA.codiff n)

def BackwardCodiffNatural : Prop :=
  ∀ n,
    (HA.codiff n).comp
        (P.backward.map (n + 1)) =
      (P.backward.map n).comp
        (HB.codiff n)

theorem forwardCodiffNatural_iff_defect_zero :
    P.ForwardCodiffNatural HA HB ↔
      ∀ n, P.forwardCodiffDefect HA HB n = 0 := by
  constructor
  · intro h n
    exact sub_eq_zero.mpr (h n)
  · intro h n
    exact sub_eq_zero.mp (h n)

theorem backwardCodiffNatural_iff_defect_zero :
    P.BackwardCodiffNatural HA HB ↔
      ∀ n, P.backwardCodiffDefect HA HB n = 0 := by
  constructor
  · intro h n
    exact sub_eq_zero.mpr (h n)
  · intro h n
    exact sub_eq_zero.mp (h n)

/-- Failure of Phi to intertwine the positive-degree Hodge Laplacian. -/
def forwardLaplacianSuccDefect (n : ℕ) :
    C (n + 1) →ₗ[K] D (n + 1) :=
  (HB.laplacianSucc n).comp
      (P.forward.map (n + 1)) -
    (P.forward.map (n + 1)).comp
      (HA.laplacianSucc n)

/-- Failure of Psi to intertwine the positive-degree Hodge Laplacian. -/
def backwardLaplacianSuccDefect (n : ℕ) :
    D (n + 1) →ₗ[K] C (n + 1) :=
  (HA.laplacianSucc n).comp
      (P.backward.map (n + 1)) -
    (P.backward.map (n + 1)).comp
      (HB.laplacianSucc n)

/-- If Phi commutes separately with d and delta, it commutes with every
positive-degree Hodge Laplacian. -/
theorem forward_laplacianSucc_natural
    (hD : P.forward.Natural)
    (hCodiff : P.ForwardCodiffNatural HA HB)
    (n : ℕ) :
    (HB.laplacianSucc n).comp
        (P.forward.map (n + 1)) =
      (P.forward.map (n + 1)).comp
        (HA.laplacianSucc n) := by
  ext x
  have hc0 :=
    LinearMap.congr_fun (hCodiff n) x
  have hd0 :=
    GradedLinearTransport.map_d hD n
      (HA.codiff n x)
  have hd1 :=
    GradedLinearTransport.map_d hD (n + 1) x
  have hc1 :=
    LinearMap.congr_fun
      (hCodiff (n + 1))
      (A.d (n + 1) x)
  change
    B.d n
        (HB.codiff n
          (P.forward.map (n + 1) x))
      +
      HB.codiff (n + 1)
        (B.d (n + 1)
          (P.forward.map (n + 1) x))
      =
    P.forward.map (n + 1)
      (A.d n (HA.codiff n x) +
        HA.codiff (n + 1)
          (A.d (n + 1) x))
  rw [hc0, hd0, hd1, hc1]
  exact
    (P.forward.map (n + 1)).map_add _ _ |>.symm

/-- The symmetric Psi theorem. -/
theorem backward_laplacianSucc_natural
    (hD : P.backward.Natural)
    (hCodiff : P.BackwardCodiffNatural HA HB)
    (n : ℕ) :
    (HA.laplacianSucc n).comp
        (P.backward.map (n + 1)) =
      (P.backward.map (n + 1)).comp
        (HB.laplacianSucc n) := by
  ext x
  have hc0 :=
    LinearMap.congr_fun (hCodiff n) x
  have hd0 :=
    GradedLinearTransport.map_d hD n
      (HB.codiff n x)
  have hd1 :=
    GradedLinearTransport.map_d hD (n + 1) x
  have hc1 :=
    LinearMap.congr_fun
      (hCodiff (n + 1))
      (B.d (n + 1) x)
  change
    A.d n
        (HA.codiff n
          (P.backward.map (n + 1) x))
      +
      HA.codiff (n + 1)
        (A.d (n + 1)
          (P.backward.map (n + 1) x))
      =
    P.backward.map (n + 1)
      (B.d n (HB.codiff n x) +
        HB.codiff (n + 1)
          (B.d (n + 1) x))
  rw [hc0, hd0, hd1, hc1]
  exact
    (P.backward.map (n + 1)).map_add _ _ |>.symm

/-- Phi maps harmonic cochains to harmonic cochains whenever it intertwines the
Hodge Laplacian. -/
def forwardHarmonicSuccMap
    (hLap :
      ∀ n,
        (HB.laplacianSucc n).comp
            (P.forward.map (n + 1)) =
          (P.forward.map (n + 1)).comp
            (HA.laplacianSucc n))
    (n : ℕ) :
    HA.HarmonicSucc n →ₗ[K]
      HB.HarmonicSucc n where
  toFun := fun x =>
    ⟨P.forward.map (n + 1) x, by
      have h :=
        LinearMap.congr_fun (hLap n) x
      change
        HB.laplacianSucc n
            (P.forward.map (n + 1) x) = 0
      rw [h]
      simp⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    simp
  map_smul' := by
    intro a x
    apply Subtype.ext
    simp

/-- Psi has the analogous harmonic transport. -/
def backwardHarmonicSuccMap
    (hLap :
      ∀ n,
        (HA.laplacianSucc n).comp
            (P.backward.map (n + 1)) =
          (P.backward.map (n + 1)).comp
            (HB.laplacianSucc n))
    (n : ℕ) :
    HB.HarmonicSucc n →ₗ[K]
      HA.HarmonicSucc n where
  toFun := fun x =>
    ⟨P.backward.map (n + 1) x, by
      have h :=
        LinearMap.congr_fun (hLap n) x
      change
        HA.laplacianSucc n
            (P.backward.map (n + 1) x) = 0
      rw [h]
      simp⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    simp
  map_smul' := by
    intro a x
    apply Subtype.ext
    simp

end PairedCochainTransport
end CausalGeometry
