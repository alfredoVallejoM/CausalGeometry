import CausalGeometry.Calculus.CubicalLeibnizExpansion
import CausalGeometry.Calculus.CubicalSerrePresentationEquality
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalCubicalCochain

variable {K : Type w} [Field K]

/-- Full pointwise graded Leibniz identity in the dimension-stable subset
presentation. -/
theorem subsetSerreCup_leibniz_ofEq
    {p q : ℕ}
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q + 1)) :

    let hL :
        (p + 1) + q = p + q + 1 := by
          omega

    let hR :
        p + (q + 1) = p + q + 1 := by
          omega

    differential (S := S) (K := K) (p + q)
        (subsetSerreCup p q alpha beta) Q
      =
    subsetSerreCupOfEq hL
        (differential (S := S) (K := K) p alpha)
        beta Q
      +
    gradedSign (K := K) p *
      subsetSerreCupOfEq hR
        alpha
        (differential (S := S) (K := K) q beta)
        Q := by

  dsimp only

  let hL :
      (p + 1) + q = p + q + 1 := by
    omega

  let hR :
      p + (q + 1) = p + q + 1 := by
    omega

  rw [
    differential_subsetSerreCup_eq_incidenceSum
  ]

  rw [
    leibnizIncidenceSum_eq_left_add_right
  ]

  rw [
    ← sum_leftParent_eq_leftIncidence
  ]

  rw [
    ← sum_rightParent_eq_rightIncidence
  ]

  rw [
    ← subsetSerreCupOfEq_differential_left_eq_parentSum
  ]

  rw [
    ← graded_subsetSerreCupOfEq_differential_right_eq_parentSum
  ]

/-- Standard subset-cup pointwise Leibniz theorem, with the unavoidable
dimension transports written explicitly. -/
theorem subsetSerreCup_leibniz_cast
    {p q : ℕ}
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q + 1)) :

    let hL :
        (p + 1) + q = p + q + 1 := by
          omega

    let hR :
        p + (q + 1) = p + q + 1 := by
          omega

    differential (S := S) (K := K) (p + q)
        (subsetSerreCup p q alpha beta) Q
      =
    subsetSerreCup (p + 1) q
        (differential (S := S) (K := K) p alpha)
        beta
        (CausalEventCube.castDim hL.symm Q)
      +
    gradedSign (K := K) p *
      subsetSerreCup p (q + 1)
        alpha
        (differential (S := S) (K := K) q beta)
        (CausalEventCube.castDim hR.symm Q) := by

  dsimp only

  let hL :
      (p + 1) + q = p + q + 1 := by
    omega

  let hR :
      p + (q + 1) = p + q + 1 := by
    omega

  rw [subsetSerreCup_leibniz_ofEq]

  rw [
    subsetSerreCupOfEq_cast,
    subsetSerreCupOfEq_cast
  ]

/-- Full pointwise graded Leibniz theorem for the shuffle-summed Serre cup. -/
theorem serreCup_leibniz_cast
    {p q : ℕ}
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q + 1)) :

    let hL :
        (p + 1) + q = p + q + 1 := by
          omega

    let hR :
        p + (q + 1) = p + q + 1 := by
          omega

    differential (S := S) (K := K) (p + q)
        (serreCup p q alpha beta) Q
      =
    serreCup (p + 1) q
        (differential (S := S) (K := K) p alpha)
        beta
        (CausalEventCube.castDim hL.symm Q)
      +
    gradedSign (K := K) p *
      serreCup p (q + 1)
        alpha
        (differential (S := S) (K := K) q beta)
        (CausalEventCube.castDim hR.symm Q) := by

  dsimp only

  rw [
    ← subsetSerreCup_eq_serreCup
  ]

  rw [
    ← subsetSerreCup_eq_serreCup
  ]

  rw [
    ← subsetSerreCup_eq_serreCup
  ]

  exact
    subsetSerreCup_leibniz_cast
      alpha beta Q

/-- Cochain-level graded Leibniz theorem for the causal Serre cup. -/
theorem serreCup_leibniz
    (p q : ℕ)
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q) :
    differential (S := S) (K := K) (p + q)
        (serreCup p q alpha beta)
      =
    (by
      simpa [Nat.add_assoc] using
        serreCup (p + 1) q
          (differential (S := S) (K := K) p alpha)
          beta)
      +
    (gradedSign (K := K) p) •
      (by
        simpa [Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using
          serreCup p (q + 1)
            alpha
            (differential
              (S := S) (K := K) q beta)) := by

  funext Q

  have h :=
    serreCup_leibniz_cast
      (S := S) (K := K)
      alpha beta Q

  simpa using h

/-- The explicit all-degree Serre Leibniz defect vanishes identically. -/
theorem serreLeibnizDefect_eq_zero
    (p q : ℕ)
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q) :
    serreLeibnizDefect p q alpha beta = 0 := by

  unfold serreLeibnizDefect

  rw [
    serreCup_leibniz
      (S := S) (K := K)
      p q alpha beta
  ]

  abel

/-- The named proposition target is now a theorem in all degrees. -/
theorem serreCupLeibniz
    (p q : ℕ)
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q) :
    SerreCupLeibniz p q alpha beta :=
  serreLeibnizDefect_eq_zero
    (S := S) (K := K)
    p q alpha beta

end CausalCubicalCochain
end CausalGeometry
