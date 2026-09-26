import CausalGeometry.Calculus.CubicalLeibnizReindex
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

open EventSystem
open scoped BigOperators

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalCubicalCochain

variable {K : Type w} [Field K]

/-- Sum of all common face/subset incidence terms. -/
noncomputable def leibnizIncidenceSum
    {p q : ℕ}
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q + 1)) : K :=
  ∑ x : CausalEventCube.FaceSubsetIndex
      (p + q) p,
    leibnizIncidenceTerm
      alpha beta Q x.1 x.2

/-- Sum of all left incidence contributions. -/
noncomputable def leibnizLeftIncidenceSum
    {p q : ℕ}
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q + 1)) : K :=
  ∑ x : CausalEventCube.FaceSubsetIndex
      (p + q) p,
    leibnizLeftIncidenceTerm
      alpha beta Q x.1 x.2

/-- Sum of all right incidence contributions. -/
noncomputable def leibnizRightIncidenceSum
    {p q : ℕ}
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q + 1)) : K :=
  ∑ x : CausalEventCube.FaceSubsetIndex
      (p + q) p,
    leibnizRightIncidenceTerm
      alpha beta Q x.1 x.2

/-- Summing the termwise identity gives the full common-index decomposition. -/
theorem leibnizIncidenceSum_eq_left_add_right
    {p q : ℕ}
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q + 1)) :
    leibnizIncidenceSum alpha beta Q
      =
    leibnizLeftIncidenceSum alpha beta Q +
      leibnizRightIncidenceSum alpha beta Q := by

  unfold leibnizIncidenceSum
    leibnizLeftIncidenceSum
    leibnizRightIncidenceSum

  rw [← Finset.sum_add_distrib]

  apply Fintype.sum_congr

  intro x

  exact
    leibnizIncidenceTerm_eq_left_add_right
      alpha beta Q x.1 x.2

/-- Direct parent term appearing in the expansion of
(d alpha) cup beta. -/
noncomputable def leibnizLeftParentTerm
    {p q : ℕ}
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q + 1))
    (x : CausalEventCube.LeftLeibnizParentIndex p q) : K :=

  let B := x.1
  let j := x.2

  let hdim :
      (p + 1) + q = p + q + 1 := by
        omega

  subsetShuffleSign
      (K := K)
      (CausalEventCube.specializeAxisSubset
        hdim B)
    *
  faceSign (K := K) j
    *
  (alpha ((Q.selectedCube B).upperFace j) -
    alpha ((Q.selectedCube B).lowerFace j))
    *
  beta
    (CausalEventCube.complementCubeOfEq
      hdim Q B)

/-- Direct parent term appearing in the expansion of
(-1)^p alpha cup (d beta). -/
noncomputable def leibnizRightParentTerm
    {p q : ℕ}
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q + 1))
    (x : CausalEventCube.RightLeibnizParentIndex p q) : K :=

  let LA := x.1
  let j := x.2

  let hdim :
      p + (q + 1) = p + q + 1 := by
        omega

  gradedSign (K := K) p
    *
  subsetShuffleSign
      (K := K)
      (CausalEventCube.specializeAxisSubset
        hdim LA)
    *
  alpha (Q.selectedCube LA)
    *
  faceSign (K := K) j
    *
  (beta
      ((CausalEventCube.complementCubeOfEq
          hdim Q LA).upperFace j)
    -
   beta
      ((CausalEventCube.complementCubeOfEq
          hdim Q LA).lowerFace j))

/-- Common left incidence term is definitionally the left parent term attached
by the inverse reindexing equivalence. -/
theorem leibnizLeftIncidenceTerm_eq_parent
    {p q : ℕ}
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q + 1))
    (x : CausalEventCube.FaceSubsetIndex
      (p + q) p) :
    leibnizLeftIncidenceTerm
        alpha beta Q x.1 x.2
      =
    leibnizLeftParentTerm
        alpha beta Q
        (CausalEventCube.faceSubsetToLeftParent
          p q x) := by
  rcases x with ⟨i, A⟩
  rfl

/-- Symmetric right-parent comparison. -/
theorem leibnizRightIncidenceTerm_eq_parent
    {p q : ℕ}
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q + 1))
    (x : CausalEventCube.FaceSubsetIndex
      (p + q) p) :
    leibnizRightIncidenceTerm
        alpha beta Q x.1 x.2
      =
    leibnizRightParentTerm
        alpha beta Q
        (CausalEventCube.faceSubsetToRightParent
          p q x) := by
  rcases x with ⟨i, A⟩
  rfl

/-- Reindex the complete left parent sum by common incidences. -/
theorem sum_leftParent_eq_leftIncidence
    {p q : ℕ}
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q + 1)) :
    (∑ x :
        CausalEventCube.LeftLeibnizParentIndex
          p q,
        leibnizLeftParentTerm
          alpha beta Q x)
      =
    leibnizLeftIncidenceSum
      alpha beta Q := by

  unfold leibnizLeftIncidenceSum

  refine
    Fintype.sum_equiv
      (CausalEventCube.leftParentFaceSubsetEquiv
        p q)
      (fun x =>
        leibnizLeftParentTerm
          alpha beta Q x)
      (fun y =>
        leibnizLeftIncidenceTerm
          alpha beta Q y.1 y.2)
      ?_

  intro x

  have h :=
    leibnizLeftIncidenceTerm_eq_parent
      alpha beta Q
      ((CausalEventCube.leftParentFaceSubsetEquiv
        p q) x)

  rw [
    (CausalEventCube.leftParentFaceSubsetEquiv
      p q).symm_apply_apply
  ] at h

  exact h.symm

/-- Reindex the complete right parent sum by common incidences. -/
theorem sum_rightParent_eq_rightIncidence
    {p q : ℕ}
    (alpha : CausalCubicalCochain S K p)
    (beta : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q + 1)) :
    (∑ x :
        CausalEventCube.RightLeibnizParentIndex
          p q,
        leibnizRightParentTerm
          alpha beta Q x)
      =
    leibnizRightIncidenceSum
      alpha beta Q := by

  unfold leibnizRightIncidenceSum

  refine
    Fintype.sum_equiv
      (CausalEventCube.rightParentFaceSubsetEquiv
        p q)
      (fun x =>
        leibnizRightParentTerm
          alpha beta Q x)
      (fun y =>
        leibnizRightIncidenceTerm
          alpha beta Q y.1 y.2)
      ?_

  intro x

  have h :=
    leibnizRightIncidenceTerm_eq_parent
      alpha beta Q
      ((CausalEventCube.rightParentFaceSubsetEquiv
        p q) x)

  rw [
    (CausalEventCube.rightParentFaceSubsetEquiv
      p q).symm_apply_apply
  ] at h

  exact h.symm

end CausalCubicalCochain
end CausalGeometry
