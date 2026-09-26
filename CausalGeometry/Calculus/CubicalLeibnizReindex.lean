import CausalGeometry.Calculus.CubicalLeibnizIncidenceTerm
import Mathlib.Tactic

namespace CausalGeometry

universe u v

namespace CausalEventCube

/-- Remove one selected ambient axis from a (p+1)-subset at its local ordered
position. -/
def eraseAxisSubsetAtPosition
    {n p : ℕ}
    (B : AxisSubset n (p + 1))
    (j : Fin (p + 1)) :
    AxisSubset n p :=
  let i :=
    (Set.powersetCard.orderIsoOfFin B j).1
  ⟨B.val.erase i, by
    rw [
      Finset.card_erase_of_mem
        (Set.powersetCard.orderIsoOfFin B j).2,
      B.prop
    ]
    omega⟩

/-- The erased ambient axis is absent from the resulting subset. -/
theorem erasedAxis_not_mem
    {n p : ℕ}
    (B : AxisSubset n (p + 1))
    (j : Fin (p + 1)) :
    (Set.powersetCard.orderIsoOfFin B j).1
      ∉
    eraseAxisSubsetAtPosition B j := by
  simp [eraseAxisSubsetAtPosition]

/-- Reinserting the erased axis recovers the parent selected subset. -/
theorem insert_eraseAxisSubsetAtPosition
    {n p : ℕ}
    (B : AxisSubset (n + 1) (p + 1))
    (j : Fin (p + 1)) :
    insertAxisSubset
        (eraseAxisSubsetAtPosition B j)
        (Set.powersetCard.orderIsoOfFin B j).1
        (erasedAxis_not_mem B j)
      =
    B := by

  apply Subtype.ext

  change
    insert
        (Set.powersetCard.orderIsoOfFin B j).1
        (B.val.erase
          (Set.powersetCard.orderIsoOfFin B j).1)
      =
    B.val

  exact
    Finset.insert_erase
      (Set.powersetCard.orderIsoOfFin B j).2

/-- After erasing one local selected slot, its reinserted local position is the
original slot. -/
theorem insertedAxisPosition_erase
    {n p : ℕ}
    (B : AxisSubset (n + 1) (p + 1))
    (j : Fin (p + 1)) :

    let i :=
      (Set.powersetCard.orderIsoOfFin B j).1

    let A0 :=
      eraseAxisSubsetAtPosition B j

    let hi :=
      erasedAxis_not_mem B j

    insertedAxisPosition A0 i hi = j := by

  dsimp only

  let i :=
    (Set.powersetCard.orderIsoOfFin B j).1

  let A0 :=
    eraseAxisSubsetAtPosition B j

  let hi :
      i ∉ A0 :=
    erasedAxis_not_mem B j

  have hparent :
      insertAxisSubset A0 i hi = B := by
    simpa [i, A0, hi] using
      insert_eraseAxisSubsetAtPosition B j

  apply
    (Set.powersetCard.orderIsoOfFin B).injective

  change
    (Set.powersetCard.orderIsoOfFin B
      (insertedAxisPosition A0 i hi)).1
      =
    (Set.powersetCard.orderIsoOfFin B j).1

  rw [← hparent]

  rw [orderIso_insertedAxisPosition]

  rfl

/-- Parent indexing of the (d alpha) cup beta expansion. -/
abbrev LeftLeibnizParentIndex
    (p q : ℕ) :=
  Σ B : AxisSubset (p + q + 1) (p + 1),
    Fin (p + 1)

/-- Parent indexing of the alpha cup (d beta) expansion. -/
abbrev RightLeibnizParentIndex
    (p q : ℕ) :=
  Σ A : AxisSubset (p + q + 1) p,
    Fin (q + 1)

/-- Map a left-parent term to its ambient face and surviving selected subset. -/
noncomputable def leftParentToFaceSubset
    (p q : ℕ) :
    LeftLeibnizParentIndex p q →
      FaceSubsetIndex (p + q) p
  | ⟨B, j⟩ =>
      let i :=
        (Set.powersetCard.orderIsoOfFin B j).1
      let E :=
        eraseAxisSubsetAtPosition B j
      let hi :
          i ∉ E :=
        erasedAxis_not_mem B j
      ⟨i,
        dropAmbientSubset E i hi⟩

/-- Inverse map: insert the omitted ambient face axis into the lifted selected
face subset. -/
noncomputable def faceSubsetToLeftParent
    (p q : ℕ) :
    FaceSubsetIndex (p + q) p →
      LeftLeibnizParentIndex p q
  | ⟨i, A⟩ =>
      let LA :=
        liftFaceSubset i A
      let hi :=
        removedAxis_not_mem_liftFaceSubset i A
      let B :=
        insertAxisSubset LA i hi
      let j :=
        insertedAxisPosition LA i hi
      ⟨B, j⟩

@[simp] theorem leftParentToFaceSubset_faceSubsetToLeftParent
    (p q : ℕ)
    (x : FaceSubsetIndex (p + q) p) :
    leftParentToFaceSubset p q
        (faceSubsetToLeftParent p q x)
      =
    x := by

  rcases x with ⟨i, A⟩

  dsimp [
    leftParentToFaceSubset,
    faceSubsetToLeftParent
  ]

  apply Sigma.ext

  · exact
      CausalEventCube
        .orderIso_insertedAxisPosition
          (liftFaceSubset i A)
          i
          (removedAxis_not_mem_liftFaceSubset i A)

  · exact
      dropAmbientSubset_liftFaceSubset
        i A

@[simp] theorem faceSubsetToLeftParent_leftParentToFaceSubset
    (p q : ℕ)
    (x : LeftLeibnizParentIndex p q) :
    faceSubsetToLeftParent p q
        (leftParentToFaceSubset p q x)
      =
    x := by

  rcases x with ⟨B, j⟩

  dsimp [
    faceSubsetToLeftParent,
    leftParentToFaceSubset
  ]

  let i :=
    (Set.powersetCard.orderIsoOfFin B j).1

  let E :=
    eraseAxisSubsetAtPosition B j

  let hi :
      i ∉ E :=
    erasedAxis_not_mem B j

  have hlift :
      liftFaceSubset i
          (dropAmbientSubset E i hi)
        =
      E :=
    liftFaceSubset_dropAmbientSubset
      E i hi

  have hB :
      insertAxisSubset E i hi = B := by
    simpa [i, E, hi] using
      insert_eraseAxisSubsetAtPosition B j

  apply Sigma.ext

  · simpa [hlift, hB]

  · have hj :
        insertedAxisPosition E i hi = j := by
      simpa [i, E, hi] using
        insertedAxisPosition_erase B j
    simpa [hlift, hB] using hj

/-- Canonical equivalence for reindexing the left Leibniz sum. -/
noncomputable def leftParentFaceSubsetEquiv
    (p q : ℕ) :
    LeftLeibnizParentIndex p q ≃
      FaceSubsetIndex (p + q) p where

  toFun :=
    leftParentToFaceSubset p q

  invFun :=
    faceSubsetToLeftParent p q

  left_inv :=
    faceSubsetToLeftParent_leftParentToFaceSubset
      p q

  right_inv :=
    leftParentToFaceSubset_faceSubsetToLeftParent
      p q

/-- Map a right-parent term to the common face/subset incidence. -/
noncomputable def rightParentToFaceSubset
    (p q : ℕ) :
    RightLeibnizParentIndex p q →
      FaceSubsetIndex (p + q) p
  | ⟨LA, j⟩ =>
      let hdim :
          p + (q + 1) = p + q + 1 := by
            omega
      let i :=
        (Set.powersetCard.orderIsoOfFin
          (complementAxisSubset hdim LA) j).1
      let hi :
          i ∉ LA := by
        have hm :
            i ∈ complementAxisSubset hdim LA :=
          (Set.powersetCard.orderIsoOfFin
            (complementAxisSubset hdim LA) j).2
        simpa [complementAxisSubset] using hm
      ⟨i,
        dropAmbientSubset LA i hi⟩

/-- Inverse right-parent map from one common face/subset incidence. -/
noncomputable def faceSubsetToRightParent
    (p q : ℕ) :
    FaceSubsetIndex (p + q) p →
      RightLeibnizParentIndex p q
  | ⟨i, A⟩ =>
      let LA :=
        liftFaceSubset i A
      let hi :=
        removedAxis_not_mem_liftFaceSubset i A
      let hdim :
          p + (q + 1) = p + q + 1 := by
            omega
      let j :=
        complementAxisPosition
          hdim LA i hi
      ⟨LA, j⟩

@[simp] theorem rightParentToFaceSubset_faceSubsetToRightParent
    (p q : ℕ)
    (x : FaceSubsetIndex (p + q) p) :
    rightParentToFaceSubset p q
        (faceSubsetToRightParent p q x)
      =
    x := by

  rcases x with ⟨i, A⟩

  dsimp [
    rightParentToFaceSubset,
    faceSubsetToRightParent
  ]

  let LA :=
    liftFaceSubset i A

  let hi :
      i ∉ LA :=
    removedAxis_not_mem_liftFaceSubset i A

  let hdim :
      p + (q + 1) = p + q + 1 := by
    omega

  apply Sigma.ext

  · exact
      orderIso_complementAxisPosition
        hdim LA i hi

  · exact
      dropAmbientSubset_liftFaceSubset
        i A

@[simp] theorem faceSubsetToRightParent_rightParentToFaceSubset
    (p q : ℕ)
    (x : RightLeibnizParentIndex p q) :
    faceSubsetToRightParent p q
        (rightParentToFaceSubset p q x)
      =
    x := by

  rcases x with ⟨LA, j⟩

  dsimp [
    faceSubsetToRightParent,
    rightParentToFaceSubset
  ]

  let hdim :
      p + (q + 1) = p + q + 1 := by
    omega

  let i :=
    (Set.powersetCard.orderIsoOfFin
      (complementAxisSubset hdim LA) j).1

  let hi :
      i ∉ LA := by
    have hm :
        i ∈ complementAxisSubset hdim LA :=
      (Set.powersetCard.orderIsoOfFin
        (complementAxisSubset hdim LA) j).2
    simpa [complementAxisSubset] using hm

  have hlift :
      liftFaceSubset i
          (dropAmbientSubset LA i hi)
        =
      LA :=
    liftFaceSubset_dropAmbientSubset
      LA i hi

  apply Sigma.ext

  · exact hlift

  · have hj :
        complementAxisPosition
            hdim LA i hi
          =
        j := by
      apply
        (Set.powersetCard.orderIsoOfFin
          (complementAxisSubset hdim LA)).injective
      rw [orderIso_complementAxisPosition]
      rfl

    simpa [hlift] using hj

/-- Canonical equivalence for reindexing the right Leibniz sum. -/
noncomputable def rightParentFaceSubsetEquiv
    (p q : ℕ) :
    RightLeibnizParentIndex p q ≃
      FaceSubsetIndex (p + q) p where

  toFun :=
    rightParentToFaceSubset p q

  invFun :=
    faceSubsetToRightParent p q

  left_inv :=
    faceSubsetToRightParent_rightParentToFaceSubset
      p q

  right_inv :=
    rightParentToFaceSubset_faceSubsetToRightParent
      p q

end CausalEventCube
end CausalGeometry
