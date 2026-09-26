import CausalGeometry.Calculus.CubicalLeibnizSigns
import Mathlib.Tactic

namespace CausalGeometry

namespace CausalEventCube

/-- Deleting one position inside the enlarged left block acts internally by
succAbove on that block. -/
theorem succAbove_leftBlock_left
    {p q : ℕ}
    (j : Fin (p + 1))
    (a : Fin p) :
    let h :
        (p + 1) + q = p + q + 1 := by omega
    (leftBlockIndexOfEq h j).succAbove
        (leftBlockIndex p q a)
      =
    leftBlockIndexOfEq h
      (j.succAbove a) := by

  intro h

  apply Fin.ext

  unfold leftBlockIndexOfEq
    leftBlockIndex

  simp only [
    Fin.val_cast
  ]

  unfold Fin.succAbove

  split_ifs with h₁ h₂ <;>
    simp_all [Fin.lt_iff_val_lt_val] <;>
    omega

/-- Deleting a position from the enlarged left block shifts every right-block
coordinate by one. -/
theorem succAbove_leftBlock_right
    {p q : ℕ}
    (j : Fin (p + 1))
    (b : Fin q) :
    let h :
        (p + 1) + q = p + q + 1 := by omega
    (leftBlockIndexOfEq h j).succAbove
        (rightBlockIndex p q b)
      =
    rightBlockIndexOfEq h b := by

  intro h

  apply Fin.ext

  unfold leftBlockIndexOfEq
    rightBlockIndexOfEq
    leftBlockIndex
    rightBlockIndex

  simp only [
    Fin.val_cast
  ]

  unfold Fin.succAbove

  split_ifs with hlt <;>
    simp_all [Fin.lt_iff_val_lt_val] <;>
    omega

/-- Deleting a position inside the enlarged right block leaves all left-block
coordinates unchanged. -/
theorem succAbove_rightBlock_left
    {p q : ℕ}
    (j : Fin (q + 1))
    (a : Fin p) :
    let h :
        p + (q + 1) = p + q + 1 := by omega
    (rightBlockIndexOfEq h j).succAbove
        (leftBlockIndex p q a)
      =
    leftBlockIndexOfEq h a := by

  intro h

  apply Fin.ext

  unfold leftBlockIndexOfEq
    rightBlockIndexOfEq
    leftBlockIndex
    rightBlockIndex

  simp only [
    Fin.val_cast
  ]

  unfold Fin.succAbove

  split_ifs with hlt <;>
    simp_all [Fin.lt_iff_val_lt_val] <;>
    omega

/-- Deleting a position inside the enlarged right block acts by succAbove on
the local right-block coordinate. -/
theorem succAbove_rightBlock_right
    {p q : ℕ}
    (j : Fin (q + 1))
    (b : Fin q) :
    let h :
        p + (q + 1) = p + q + 1 := by omega
    (rightBlockIndexOfEq h j).succAbove
        (rightBlockIndex p q b)
      =
    rightBlockIndexOfEq h
      (j.succAbove b) := by

  intro h

  apply Fin.ext

  unfold rightBlockIndexOfEq
    rightBlockIndex

  simp only [
    Fin.val_cast
  ]

  unfold Fin.succAbove

  split_ifs with h₁ h₂ <;>
    simp_all [Fin.lt_iff_val_lt_val] <;>
    omega

end CausalEventCube
end CausalGeometry
