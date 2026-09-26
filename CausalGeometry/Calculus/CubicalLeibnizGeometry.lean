import CausalGeometry.Calculus.CubicalLeibnizGeometryBase
import Mathlib.Tactic

namespace CausalGeometry

universe u v

open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalEventCube

/-- The selected cube of the lower ambient face is obtained by deleting the
newly inserted selected axis from the enlarged ambient selected cube. -/
theorem lowerFace_selectedCube_eq_selectedCube_lowerFace
    {p q : ℕ}
    (Q : CausalEventCube S (p + q + 1))
    (i : Fin (p + q + 1))
    (A : AxisSubset (p + q) p) :

    let LA :=
      liftFaceSubset i A

    let hi :=
      removedAxis_not_mem_liftFaceSubset i A

    let B :=
      insertAxisSubset LA i hi

    let j :=
      insertedAxisPosition LA i hi

    (Q.lowerFace i).selectedCube A =
      (Q.selectedCube B).lowerFace j := by

  dsimp only

  let LA :=
    liftFaceSubset i A

  let hi :
      i ∉ LA :=
    removedAxis_not_mem_liftFaceSubset i A

  let B :=
    insertAxisSubset LA i hi

  let j :=
    insertedAxisPosition LA i hi

  apply CausalEventCube.ext

  · rfl

  · funext a

    change
      Q.frame.event
          (i.succAbove
            (Set.powersetCard.orderIsoOfFin A a).1)
        =
      Q.frame.event
        (Set.powersetCard.orderIsoOfFin
          B (j.succAbove a)).1

    rw [
      orderIso_insertAxis_succAbove
        LA i hi a,
      orderIso_liftFaceSubset
        i A a
    ]

/-- The selected cube of the upper ambient face is obtained by taking the
upper face at the inserted-axis position of the enlarged selected cube. -/
theorem upperFace_selectedCube_eq_selectedCube_upperFace
    {p q : ℕ}
    (Q : CausalEventCube S (p + q + 1))
    (i : Fin (p + q + 1))
    (A : AxisSubset (p + q) p) :

    let LA :=
      liftFaceSubset i A

    let hi :=
      removedAxis_not_mem_liftFaceSubset i A

    let B :=
      insertAxisSubset LA i hi

    let j :=
      insertedAxisPosition LA i hi

    (Q.upperFace i).selectedCube A =
      (Q.selectedCube B).upperFace j := by

  dsimp only

  let LA :=
    liftFaceSubset i A

  let hi :
      i ∉ LA :=
    removedAxis_not_mem_liftFaceSubset i A

  let B :=
    insertAxisSubset LA i hi

  let j :=
    insertedAxisPosition LA i hi

  apply CausalEventCube.ext

  · apply S.configuration_eq_of_carrier_eq

    change
      (Q.frame.after i).carrier =
        ((Q.selectedCube B).frame.after j).carrier

    rw [
      CausalCubeFrame.after_carrier,
      CausalCubeFrame.after_carrier
    ]

    congr 1

    change
      Q.frame.event i =
        Q.frame.event
          (Set.powersetCard.orderIsoOfFin B j).1

    rw [orderIso_insertedAxisPosition]

  · funext a

    change
      Q.frame.event
          (i.succAbove
            (Set.powersetCard.orderIsoOfFin A a).1)
        =
      Q.frame.event
        (Set.powersetCard.orderIsoOfFin
          B (j.succAbove a)).1

    rw [
      orderIso_insertAxis_succAbove
        LA i hi a,
      orderIso_liftFaceSubset
        i A a
    ]

/-- The selected factor of the lower face is also directly the ambient
selected cube of the lifted subset. -/
theorem lowerFace_selectedCube_eq_liftSelectedCube
    {p q : ℕ}
    (Q : CausalEventCube S (p + q + 1))
    (i : Fin (p + q + 1))
    (A : AxisSubset (p + q) p) :
    (Q.lowerFace i).selectedCube A =
      Q.selectedCube (liftFaceSubset i A) := by

  apply CausalEventCube.ext

  · rfl

  · funext a

    change
      Q.frame.event
          (i.succAbove
            (Set.powersetCard.orderIsoOfFin A a).1)
        =
      Q.frame.event
        (Set.powersetCard.orderIsoOfFin
          (liftFaceSubset i A) a).1

    rw [orderIso_liftFaceSubset]

/-- The complementary factor of the upper ambient face is exactly the
complementary factor associated to the enlarged selected subset B=A union {i}. -/
theorem upperFace_complementCube_eq_insertComplementCube
    {p q : ℕ}
    (Q : CausalEventCube S (p + q + 1))
    (i : Fin (p + q + 1))
    (A : AxisSubset (p + q) p) :

    let LA :=
      liftFaceSubset i A

    let hi :=
      removedAxis_not_mem_liftFaceSubset i A

    let B :=
      insertAxisSubset LA i hi

    let hdim :
        (p + 1) + q = p + q + 1 := by
          omega

    (Q.upperFace i).complementCube A =
      complementCubeOfEq hdim Q B := by

  dsimp only

  let LA :=
    liftFaceSubset i A

  let hi :
      i ∉ LA :=
    removedAxis_not_mem_liftFaceSubset i A

  let B :=
    insertAxisSubset LA i hi

  let hdim :
      (p + 1) + q = p + q + 1 := by
    omega

  apply CausalEventCube.ext

  · rw [complementCube_base]
    rw [complementCubeOfEq_base]

    exact
      upperFace_afterAxes_eq_afterAxes_insertLift
        Q i A

  · funext b

    change
      Q.frame.event
        (i.succAbove
          (Set.powersetCard.orderIsoOfFin
            A.complementAxes b).1)
        =
      Q.frame.event
        (Set.powersetCard.orderIsoOfFin
          (complementAxisSubset hdim B) b).1

    rw [
      complement_insert_liftFaceSubset
        (h := (rfl : p + q = p + q))
        i A
    ]

    rw [
      orderIso_liftFaceSubset
        i A.complementAxes b
    ]

/-- Lower complementary factor of the face is the lower local face of the
ambient complementary cube built from the lifted selected subset. -/
theorem lowerFace_complementCube_eq_liftComplement_lowerFace
    {p q : ℕ}
    (Q : CausalEventCube S (p + q + 1))
    (i : Fin (p + q + 1))
    (A : AxisSubset (p + q) p) :

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

    (Q.lowerFace i).complementCube A =
      (complementCubeOfEq hdim Q LA).lowerFace j := by

  dsimp only

  let LA :=
    liftFaceSubset i A

  let hi :
      i ∉ LA :=
    removedAxis_not_mem_liftFaceSubset i A

  let hdim :
      p + (q + 1) = p + q + 1 := by
    omega

  let j :=
    complementAxisPosition
      hdim LA i hi

  apply CausalEventCube.ext

  · rw [complementCube_base]
    rw [lowerFace_base]
    rw [complementCubeOfEq_base]

    exact
      lowerFace_afterAxes_eq_afterAxes_lift
        Q i A

  · funext b

    change
      Q.frame.event
        (i.succAbove
          (Set.powersetCard.orderIsoOfFin
            A.complementAxes b).1)
        =
      Q.frame.event
        (Set.powersetCard.orderIsoOfFin
          (complementAxisSubset hdim LA)
          (j.succAbove b)).1

    rw [
      orderIso_complement_lift_succAbove
        (h := (rfl : p + q = p + q))
        i A b
    ]

/-- Upper complementary factor of the face is the upper local face of the
same ambient complementary cube. -/
theorem upperFace_complementCube_eq_liftComplement_upperFace
    {p q : ℕ}
    (Q : CausalEventCube S (p + q + 1))
    (i : Fin (p + q + 1))
    (A : AxisSubset (p + q) p) :

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

    (Q.upperFace i).complementCube A =
      (complementCubeOfEq hdim Q LA).upperFace j := by

  dsimp only

  let LA :=
    liftFaceSubset i A

  let hi :
      i ∉ LA :=
    removedAxis_not_mem_liftFaceSubset i A

  let hdim :
      p + (q + 1) = p + q + 1 := by
    omega

  let j :=
    complementAxisPosition
      hdim LA i hi

  apply CausalEventCube.ext

  · apply S.configuration_eq_of_carrier_eq

    rw [complementCube_base]
    rw [upperFace_base]
    rw [complementCubeOfEq_base]
    rw [CausalCubeFrame.after_carrier]

    have hUpper :
        (Q.upperFace i).afterAxes A.val =
          Q.afterAxes
            (insertAxisSubset LA i hi).val :=
      upperFace_afterAxes_eq_afterAxes_insertLift
        Q i A

    have hLower :
        (complementCubeOfEq hdim Q LA).base =
          Q.afterAxes LA.val := by
      rw [complementCubeOfEq_base]

    rw [hUpper]

    change
      (Q.afterAxes
        (insertAxisSubset LA i hi).val).carrier
        =
      insert
        ((complementCubeOfEq hdim Q LA).frame.event j)
        (Q.afterAxes LA.val).carrier

    change
      (Q.base.carrier ∪
        Q.selectedEventSet
          (insertAxisSubset LA i hi).val)
        =
      insert
        (Q.frame.event
          (Set.powersetCard.orderIsoOfFin
            (complementAxisSubset hdim LA) j).1)
        (Q.base.carrier ∪
          Q.selectedEventSet LA.val)

    have hji :
        (Set.powersetCard.orderIsoOfFin
          (complementAxisSubset hdim LA) j).1
          =
        i := by
      exact
        orderIso_complementAxisPosition
          hdim LA i hi

    rw [hji]

    ext e

    change
      (e ∈ Q.base ∨
        ∃ k ∈
            (insertAxisSubset LA i hi).val,
          Q.frame.event k = e)
        ↔
      (e = Q.frame.event i ∨
        e ∈ Q.base ∨
          ∃ k ∈ LA.val,
            Q.frame.event k = e)

    change
      (e ∈ Q.base ∨
        ∃ k ∈ insert i LA.val,
          Q.frame.event k = e)
        ↔
      _

    constructor

    · intro h
      rcases h with hbase | hsel
      · exact Or.inr (Or.inl hbase)
      · rcases hsel with ⟨k, hk, hek⟩
        rcases Finset.mem_insert.mp hk with hki | hkLA
        · subst k
          exact Or.inl hek.symm
        · exact Or.inr
            (Or.inr ⟨k, hkLA, hek⟩)

    · intro h
      rcases h with hei | hrest
      · right
        exact
          ⟨i, Finset.mem_insert_self _ _, hei.symm⟩
      · rcases hrest with hbase | hsel
        · exact Or.inl hbase
        · right
          rcases hsel with ⟨k, hkLA, hek⟩
          exact
            ⟨k, Finset.mem_insert_of_mem hkLA, hek⟩

  · funext b

    change
      Q.frame.event
        (i.succAbove
          (Set.powersetCard.orderIsoOfFin
            A.complementAxes b).1)
        =
      Q.frame.event
        (Set.powersetCard.orderIsoOfFin
          (complementAxisSubset hdim LA)
          (j.succAbove b)).1

    rw [
      orderIso_complement_lift_succAbove
        (h := (rfl : p + q = p + q))
        i A b
    ]

end CausalEventCube
end CausalGeometry
