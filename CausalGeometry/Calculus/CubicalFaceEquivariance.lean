import CausalGeometry.Calculus.CubicalOrientation
import CausalGeometry.Calculus.EventCubeFaceLaws
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalEventCube

/-- Normalize a permutation relative to one deleted axis:
move i to zero, apply sigma, then move sigma(i) back to zero.

The normalized permutation fixes zero. -/
def faceNormalizedPermutation
    {n : ℕ}
    (sigma : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) :
    Equiv.Perm (Fin (n + 1)) :=
  (i.cycleRange.symm.trans sigma).trans
    (sigma i).cycleRange

@[simp] theorem faceNormalizedPermutation_zero
    {n : ℕ}
    (sigma : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) :
    faceNormalizedPermutation sigma i 0 = 0 := by
  simp [faceNormalizedPermutation]

/-- Residual permutation induced by sigma on the n axes surviving deletion of i. -/
def faceResidualPermutation
    {n : ℕ}
    (sigma : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) :
    Equiv.Perm (Fin n) :=
  (Equiv.Perm.decomposeFin
    (faceNormalizedPermutation sigma i)).2

/-- The normalized permutation is reconstructed from zero and its residual
permutation. -/
theorem faceNormalizedPermutation_eq_decompose
    {n : ℕ}
    (sigma : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) :
    faceNormalizedPermutation sigma i =
      Equiv.Perm.decomposeFin.symm
        (0, faceResidualPermutation sigma i) := by

  let tau :=
    faceNormalizedPermutation sigma i

  have hround :
      Equiv.Perm.decomposeFin.symm
          (Equiv.Perm.decomposeFin tau)
        =
      tau :=
    Equiv.Perm.decomposeFin.symm_apply_apply tau

  have hfst :
      (Equiv.Perm.decomposeFin tau).1 = 0 := by
    have hz :=
      congrArg (fun p : Equiv.Perm (Fin (n + 1)) => p 0)
        hround
    simpa [tau] using hz

  symm
  calc
    Equiv.Perm.decomposeFin.symm
        (0, faceResidualPermutation sigma i)
        =
      Equiv.Perm.decomposeFin.symm
        (Equiv.Perm.decomposeFin tau) := by
          rw [hfst]
          rfl
    _ = tau := hround
    _ = faceNormalizedPermutation sigma i := rfl

/-- Coordinate identity characterizing the residual face permutation. -/
theorem faceResidual_succAbove
    {n : ℕ}
    (sigma : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1))
    (j : Fin n) :
    sigma (i.succAbove j) =
      (sigma i).succAbove
        (faceResidualPermutation sigma i j) := by

  let rho :=
    faceResidualPermutation sigma i

  have hnorm :=
    faceNormalizedPermutation_eq_decompose
      sigma i

  have hs :
      faceNormalizedPermutation sigma i j.succ =
        (rho j).succ := by
    rw [hnorm]
    simp [rho]

  change
    (sigma i).cycleRange
        (sigma
          (i.cycleRange.symm j.succ))
      =
    (rho j).succ at hs

  rw [Fin.cycleRange_symm_succ] at hs

  apply (sigma i).cycleRange.injective

  rw [hs]
  simp [rho]

/-- Lower faces commute with coordinate permutations up to the residual
permutation on surviving axes. -/
theorem permute_lowerFace
    {n : ℕ}
    (Q : CausalEventCube S (n + 1))
    (sigma : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) :
    (Q.permute sigma).lowerFace i =
      (Q.lowerFace (sigma i)).permute
        (faceResidualPermutation sigma i) := by
  apply CausalEventCube.ext
  · rfl
  · funext j
    change
      Q.frame.event
          (sigma (i.succAbove j))
        =
      Q.frame.event
        ((sigma i).succAbove
          (faceResidualPermutation sigma i j))
    rw [faceResidual_succAbove]

/-- Upper faces satisfy the same residual permutation law. -/
theorem permute_upperFace
    {n : ℕ}
    (Q : CausalEventCube S (n + 1))
    (sigma : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) :
    (Q.permute sigma).upperFace i =
      (Q.upperFace (sigma i)).permute
        (faceResidualPermutation sigma i) := by
  apply CausalEventCube.ext
  · apply S.configuration_eq_of_carrier_eq
    rfl
  · funext j
    change
      Q.frame.event
          (sigma (i.succAbove j))
        =
      Q.frame.event
        ((sigma i).succAbove
          (faceResidualPermutation sigma i j))
    rw [faceResidual_succAbove]

end CausalEventCube

namespace CausalCubicalCochain

variable {K : Type w} [Field K]

/-- Permutation sign is compatible with equivalence composition. -/
theorem permutationSign_trans
    {n : ℕ}
    (sigma tau : Equiv.Perm (Fin n)) :
    permutationSign (K := K) (sigma.trans tau) =
      permutationSign (K := K) tau *
        permutationSign (K := K) sigma := by
  simp [permutationSign, Equiv.Perm.sign_trans]

@[simp] theorem permutationSign_cycleRange
    {n : ℕ}
    (i : Fin n) :
    permutationSign (K := K) i.cycleRange =
      ((-1 : K) ^ i.val) := by
  simp [permutationSign, Fin.sign_cycleRange]

@[simp] theorem permutationSign_cycleRange_symm
    {n : ℕ}
    (i : Fin n) :
    permutationSign (K := K) i.cycleRange.symm =
      ((-1 : K) ^ i.val) := by
  simp [permutationSign,
    Equiv.Perm.sign_symm,
    Fin.sign_cycleRange]

/-- A cubical face sign squares to one. -/
theorem faceSign_square
    {n : ℕ}
    (i : Fin (n + 1)) :
    faceSign (K := K) i *
        faceSign (K := K) i
      =
    1 := by
  unfold faceSign
  rw [← pow_add]
  have heven :
      Even (i.val + i.val) :=
    ⟨i.val, by omega⟩
  exact Even.neg_one_pow heven

/-- Sign of the normalized permutation in terms of sigma and the two deleted
axis positions. -/
theorem permutationSign_faceNormalized
    {n : ℕ}
    (sigma : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) :
    permutationSign (K := K)
        (CausalEventCube.faceNormalizedPermutation sigma i)
      =
    faceSign (K := K) (sigma i) *
      permutationSign (K := K) sigma *
      faceSign (K := K) i := by
  unfold CausalEventCube.faceNormalizedPermutation
  rw [permutationSign_trans]
  rw [permutationSign_trans]
  rw [permutationSign_cycleRange]
  rw [permutationSign_cycleRange_symm]
  ring

/-- Sign of the normalized permutation is the sign of its residual part,
because the distinguished zero coordinate is fixed. -/
theorem permutationSign_faceResidual_eq_normalized
    {n : ℕ}
    (sigma : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) :
    permutationSign (K := K)
        (CausalEventCube.faceResidualPermutation sigma i)
      =
    permutationSign (K := K)
        (CausalEventCube.faceNormalizedPermutation sigma i) := by

  have h :=
    CausalEventCube.faceNormalizedPermutation_eq_decompose
      sigma i

  rw [h]

  unfold permutationSign

  simp [Equiv.Perm.decomposeFin.symm_sign]

/-- Cofactor sign identity:
(-1)^i sign(residual) = sign(sigma) (-1)^(sigma i). -/
theorem faceSign_mul_residualSign
    {n : ℕ}
    (sigma : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) :
    faceSign (K := K) i *
        permutationSign (K := K)
          (CausalEventCube.faceResidualPermutation sigma i)
      =
    permutationSign (K := K) sigma *
      faceSign (K := K) (sigma i) := by

  rw [permutationSign_faceResidual_eq_normalized]
  rw [permutationSign_faceNormalized]

  calc
    faceSign (K := K) i *
        (faceSign (K := K) (sigma i) *
          permutationSign (K := K) sigma *
          faceSign (K := K) i)
        =
      permutationSign (K := K) sigma *
        faceSign (K := K) (sigma i) *
        (faceSign (K := K) i *
          faceSign (K := K) i) := by
            ring
    _ =
      permutationSign (K := K) sigma *
        faceSign (K := K) (sigma i) := by
          rw [faceSign_square]
          ring

end CausalCubicalCochain
end CausalGeometry
