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
