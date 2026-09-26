import CausalGeometry.Calculus.CubicalFrontBack
import Mathlib.Tactic

namespace CausalGeometry

universe u v

open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalEventCube

/-- Front faces never change the base configuration. -/
theorem frontFace_base
    (p q : ℕ)
    (Q : CausalEventCube S (p + q)) :
    (Q.frontFace p q).base = Q.base := by
  induction q generalizing Q with
  | zero =>
      simp [frontFace, castDim]
  | succ q ih =>
      change
        (frontFace p q
          ((castDim (Nat.add_succ p q) Q)
            .lowerFace (Fin.last (p + q)))).base
          =
        Q.base
      rw [ih]
      rfl

/-- The i-th event of the front p-face is the original i-th event among the
first p ambient coordinates. -/
theorem frontFace_event
    (p q : ℕ)
    (Q : CausalEventCube S (p + q))
    (i : Fin p) :
    (Q.frontFace p q).frame.event i =
      Q.frame.event (Fin.castAdd q i) := by
  induction q generalizing Q with
  | zero =>
      simp [frontFace, castDim]
  | succ q ih =>
      change
        (frontFace p q
          ((castDim (Nat.add_succ p q) Q)
            .lowerFace (Fin.last (p + q)))).frame.event i
          =
        Q.frame.event (Fin.castAdd (q + 1) i)

      rw [ih]

      change
        (castDim (Nat.add_succ p q) Q).frame.event
          ((Fin.last (p + q)).succAbove
            (Fin.castAdd q i))
          =
        Q.frame.event (Fin.castAdd (q + 1) i)

      congr 1

      apply Fin.ext
      simp [castDim]

/-- Front face of the canonical subset permutation is the selected-axis cube. -/
theorem selectedCube_eq_frontFace
    {p q : ℕ}
    (Q : CausalEventCube S (p + q))
    (A : AxisSubset (p + q) p) :
    Q.selectedCube A =
      (Q.permute (subsetPermutation A))
        .frontFace p q := by

  apply CausalEventCube.ext

  · rw [frontFace_base]
    rfl

  · funext i
    rw [frontFace_event]
    change
      Q.frame.event
          (Set.powersetCard.orderIsoOfFin A i).1
        =
      Q.frame.event
        (subsetPermutation A
          (Fin.castAdd q i))
    rw [subsetPermutation_left]
    rfl

end CausalEventCube
end CausalGeometry
