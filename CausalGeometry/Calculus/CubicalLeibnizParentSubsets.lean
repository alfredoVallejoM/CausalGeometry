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
