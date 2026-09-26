import CausalGeometry.Calculus.CubicalLeibnizIncidence
import Mathlib.Tactic

namespace CausalGeometry

universe u v

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalEventCube

/-- Transport an axis subset across an equality of ambient dimensions. -/
def castAxisSubset
    {n n' p : ℕ}
    (h : n = n')
    (A : AxisSubset n p) :
    AxisSubset n' p :=
  h ▸ A

@[simp] theorem castAxisSubset_rfl
    {n p : ℕ}
    (A : AxisSubset n p) :
    castAxisSubset rfl A = A :=
  rfl

/-- Insert one omitted ambient axis into a selected subset. -/
def insertAxisSubset
    {n p : ℕ}
    (A : AxisSubset (n + 1) p)
    (i : Fin (n + 1))
    (hi : i ∉ A) :
    AxisSubset (n + 1) (p + 1) :=
  ⟨insert i A.val, by
    rw [Finset.card_insert_of_not_mem hi, A.prop]⟩

@[simp] theorem insertAxisSubset_val
    {n p : ℕ}
    (A : AxisSubset (n + 1) p)
    (i : Fin (n + 1))
    (hi : i ∉ A) :
    (insertAxisSubset A i hi :
      Finset (Fin (n + 1)))
      =
    insert i A.val :=
  rfl

@[simp] theorem insertedAxis_mem
    {n p : ℕ}
    (A : AxisSubset (n + 1) p)
    (i : Fin (n + 1))
    (hi : i ∉ A) :
    i ∈ insertAxisSubset A i hi := by
  simp [insertAxisSubset]

/-- Local position of the newly inserted ambient axis inside the increasing
enumeration of A union {i}. -/
noncomputable def insertedAxisPosition
    {n p : ℕ}
    (A : AxisSubset (n + 1) p)
    (i : Fin (n + 1))
    (hi : i ∉ A) :
    Fin (p + 1) :=
  (Set.powersetCard.orderIsoOfFin
    (insertAxisSubset A i hi)).symm
      ⟨i, insertedAxis_mem A i hi⟩

/-- The inserted local position indeed enumerates back to i. -/
@[simp] theorem orderIso_insertedAxisPosition
    {n p : ℕ}
    (A : AxisSubset (n + 1) p)
    (i : Fin (n + 1))
    (hi : i ∉ A) :
    (Set.powersetCard.orderIsoOfFin
      (insertAxisSubset A i hi)
      (insertedAxisPosition A i hi)).1
      =
    i := by
  exact congrArg Subtype.val
    ((Set.powersetCard.orderIsoOfFin
      (insertAxisSubset A i hi))
      .apply_symm_apply
        ⟨i, insertedAxis_mem A i hi⟩)

/-- Erasing the newly inserted axis recovers the original selected finset. -/
theorem erase_insertAxisSubset
    {n p : ℕ}
    (A : AxisSubset (n + 1) p)
    (i : Fin (n + 1))
    (hi : i ∉ A) :
    (insertAxisSubset A i hi).val.erase i =
      A.val := by
  simp [insertAxisSubset, hi]

/-- Deleting the local position of the newly inserted axis from the increasing
enumeration of A union {i} recovers the increasing enumeration of A. -/
theorem orderIso_insertAxis_succAbove
    {n p : ℕ}
    (A : AxisSubset (n + 1) p)
    (i : Fin (n + 1))
    (hi : i ∉ A)
    (a : Fin p) :
    (Set.powersetCard.orderIsoOfFin
      (insertAxisSubset A i hi)
      ((insertedAxisPosition A i hi).succAbove a)).1
      =
    (Set.powersetCard.orderIsoOfFin A a).1 := by

  let B :=
    insertAxisSubset A i hi

  let j :=
    insertedAxisPosition A i hi

  let f : Fin p ↪o Fin (n + 1) :=
    OrderEmbedding.ofStrictMono
      (fun a =>
        (Set.powersetCard.orderIsoOfFin
          B (j.succAbove a)).1)
      (by
        intro a b hab
        exact
          (Set.powersetCard.orderIsoOfFin B)
            .strictMono
            (j.strictMono_succAbove hab))

  have hfmem :
      ∀ a : Fin p,
        f a ∈ A.val := by
    intro a

    have hBmem :
        f a ∈ B.val :=
      (Set.powersetCard.orderIsoOfFin
        B (j.succAbove a)).2

    have hne :
        f a ≠ i := by
      intro hEq

      have hpos :
          j.succAbove a = j := by
        apply
          (Set.powersetCard.orderIsoOfFin B).injective
        apply Subtype.ext
        simpa [f] using hEq

      exact
        j.succAbove_ne a hpos

    change
      f a ∈ insert i A.val at hBmem

    rcases Finset.mem_insert.mp hBmem with
      hEq | hA
    · exact (hne hEq).elim
    · exact hA

  have hfun :
      f =
        A.val.orderEmbOfFin A.prop :=
    Finset.orderEmbOfFin_unique'
      A.prop hfmem

  have ha :=
    congrArg
      (fun e : Fin p ↪o Fin (n + 1) =>
        e a)
      hfun

  exact ha

/-- Generic complement of a selected axis subset when the complementary
cardinality is supplied explicitly. -/
def complementAxisSubset
    {n p q : ℕ}
    (h : p + q = n)
    (A : AxisSubset n p) :
    AxisSubset n q :=
  ⟨A.valᶜ, by
    simp [Finset.card_compl,
      Fintype.card_fin, A.prop]
    omega⟩

@[simp] theorem complementAxisSubset_val
    {n p q : ℕ}
    (h : p + q = n)
    (A : AxisSubset n p) :
    (complementAxisSubset h A :
      Finset (Fin n))
      =
    A.valᶜ :=
  rfl

/-- Any omitted axis lies in the complementary subset. -/
theorem mem_complementAxisSubset
    {n p q : ℕ}
    (h : p + q = n)
    (A : AxisSubset n p)
    (i : Fin n)
    (hi : i ∉ A) :
    i ∈ complementAxisSubset h A := by
  simpa [complementAxisSubset] using hi

/-- Local position of an omitted ambient axis inside the increasing
enumeration of the complementary block. -/
noncomputable def complementAxisPosition
    {n p q : ℕ}
    (h : p + q = n)
    (A : AxisSubset n p)
    (i : Fin n)
    (hi : i ∉ A) :
    Fin q :=
  (Set.powersetCard.orderIsoOfFin
    (complementAxisSubset h A)).symm
      ⟨i,
        mem_complementAxisSubset
          h A i hi⟩

@[simp] theorem orderIso_complementAxisPosition
    {n p q : ℕ}
    (h : p + q = n)
    (A : AxisSubset n p)
    (i : Fin n)
    (hi : i ∉ A) :
    (Set.powersetCard.orderIsoOfFin
      (complementAxisSubset h A)
      (complementAxisPosition h A i hi)).1
      =
    i := by
  exact congrArg Subtype.val
    ((Set.powersetCard.orderIsoOfFin
      (complementAxisSubset h A))
      .apply_symm_apply
        ⟨i,
          mem_complementAxisSubset
            h A i hi⟩)

/-- Complement of a lifted face subset is obtained by inserting the removed
axis into the lift of the face complement. -/
theorem complement_liftFaceSubset
    {n p q : ℕ}
    (h : p + q = n)
    (i : Fin (n + 1))
    (A : AxisSubset n p) :
    (complementAxisSubset
        (by omega : p + (q + 1) = n + 1)
        (liftFaceSubset i A)).val
      =
    insert i
      (liftFaceSubset i
        (complementAxisSubset h A)).val := by

  ext k

  by_cases hki : k = i

  · subst k
    simp [
      complementAxisSubset,
      removedAxis_not_mem_liftFaceSubset
    ]

  · rcases Fin.exists_succAbove_eq hki with
      ⟨j, rfl⟩

    have hmem :
        i.succAbove j ∈ liftFaceSubset i A ↔
          j ∈ A := by
      rw [mem_liftFaceSubset_iff]
      constructor
      · rintro ⟨j', hj', hEq⟩
        have :
            j' = j :=
          i.succAbove_right_injective hEq
        subst j'
        exact hj'
      · intro hj
        exact ⟨j, hj, rfl⟩

    have hmemComp :
        i.succAbove j ∈
            liftFaceSubset i
              (complementAxisSubset h A)
          ↔
        j ∉ A := by
      rw [mem_liftFaceSubset_iff]
      constructor
      · rintro ⟨j', hj', hEq⟩
        have :
            j' = j :=
          i.succAbove_right_injective hEq
        subst j'
        simpa [complementAxisSubset] using hj'
      · intro hj
        refine ⟨j, ?_, rfl⟩
        simpa [complementAxisSubset] using hj

    simp only [
      complementAxisSubset_val,
      Finset.mem_compl,
      Finset.mem_insert,
      i.succAbove_ne,
      false_or
    ]

    rw [hmem, hmemComp]

/-- If the omitted axis is inserted into the lifted selected subset, the
complement of that enlarged subset is exactly the lift of the face
complement. -/
theorem complement_insert_liftFaceSubset
    {n p q : ℕ}
    (h : p + q = n)
    (i : Fin (n + 1))
    (A : AxisSubset n p) :
    complementAxisSubset
        (by omega : (p + 1) + q = n + 1)
        (insertAxisSubset
          (liftFaceSubset i A)
          i
          (removedAxis_not_mem_liftFaceSubset i A))
      =
    liftFaceSubset i
      (complementAxisSubset h A) := by

  apply Subtype.ext

  let LA :=
    liftFaceSubset i A

  let LC :=
    liftFaceSubset i
      (complementAxisSubset h A)

  have hcomp :
      (complementAxisSubset
        (by omega : p + (q + 1) = n + 1)
        LA).val
        =
      insert i LC.val := by
    simpa [LA, LC] using
      complement_liftFaceSubset
        h i A

  ext k

  have hiLC :
      i ∉ LC :=
    removedAxis_not_mem_liftFaceSubset
      i (complementAxisSubset h A)

  change
    k ∈
      (insert i LA.val)ᶜ
      ↔
    k ∈ LC.val

  have hkComp :
      k ∈ LA.valᶜ ↔
        k = i ∨ k ∈ LC.val := by
    rw [← hcomp]
    simp [eq_comm]

  constructor

  · intro hk
    have hkLA :
        k ∈ LA.valᶜ := by
      simpa using hk

    rcases hkComp.mp hkLA with
      hki | hkLC
    · subst k
      simpa using hk
    · exact hkLC

  · intro hkLC

    have hki : k ≠ i := by
      intro hEq
      subst k
      exact hiLC hkLC

    have hkLA :
        k ∈ LA.valᶜ :=
      hkComp.mpr (Or.inr hkLC)

    simpa [hki] using hkLA

/-- Strong AxisSubset form of complement_liftFaceSubset. -/
theorem complementAxisSubset_lift_eq_insert
    {n p q : ℕ}
    (h : p + q = n)
    (i : Fin (n + 1))
    (A : AxisSubset n p) :
    complementAxisSubset
        (by omega : p + (q + 1) = n + 1)
        (liftFaceSubset i A)
      =
    insertAxisSubset
      (liftFaceSubset i
        (complementAxisSubset h A))
      i
      (removedAxis_not_mem_liftFaceSubset
        i (complementAxisSubset h A)) := by

  apply Subtype.ext

  exact
    complement_liftFaceSubset
      h i A

/-- The local omitted-axis position in the ambient complement is exactly the
inserted-axis position in the lifted face complement. -/
theorem complementAxisPosition_lift_eq_insertedAxisPosition
    {n p q : ℕ}
    (h : p + q = n)
    (i : Fin (n + 1))
    (A : AxisSubset n p) :
    complementAxisPosition
        (by omega : p + (q + 1) = n + 1)
        (liftFaceSubset i A)
        i
        (removedAxis_not_mem_liftFaceSubset i A)
      =
    insertedAxisPosition
      (liftFaceSubset i
        (complementAxisSubset h A))
      i
      (removedAxis_not_mem_liftFaceSubset
        i (complementAxisSubset h A)) := by

  have hset :=
    complementAxisSubset_lift_eq_insert
      h i A

  unfold complementAxisPosition
    insertedAxisPosition

  rw [hset]

/-- Removing the omitted-axis position from the ambient complementary
enumeration recovers the lifted enumeration of the face complement. -/
theorem orderIso_complement_lift_succAbove
    {n p q : ℕ}
    (h : p + q = n)
    (i : Fin (n + 1))
    (A : AxisSubset n p)
    (a : Fin q) :
    (Set.powersetCard.orderIsoOfFin
      (complementAxisSubset
        (by omega : p + (q + 1) = n + 1)
        (liftFaceSubset i A))
      ((complementAxisPosition
          (by omega : p + (q + 1) = n + 1)
          (liftFaceSubset i A)
          i
          (removedAxis_not_mem_liftFaceSubset i A)).succAbove a)).1
      =
    i.succAbove
      (Set.powersetCard.orderIsoOfFin
        (complementAxisSubset h A) a).1 := by

  rw [
    complementAxisSubset_lift_eq_insert
      h i A,
    complementAxisPosition_lift_eq_insertedAxisPosition
      h i A
  ]

  rw [
    orderIso_insertAxis_succAbove
      (liftFaceSubset i
        (complementAxisSubset h A))
      i
      (removedAxis_not_mem_liftFaceSubset
        i (complementAxisSubset h A))
      a
  ]

  change
    (Set.powersetCard.orderIsoOfFin
      (liftFaceSubset i
        (complementAxisSubset h A)) a).1
      =
    _

  rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]

  rfl

/-- For the specialized complementAxes API, the generic complement agrees
definitionally after the ambient-dimension equation is chosen. -/
theorem complementAxisSubset_eq_complementAxes
    {p q : ℕ}
    (A : AxisSubset (p + q) p) :
    complementAxisSubset rfl A =
      A.complementAxes := by
  rfl

end CausalEventCube
end CausalGeometry
