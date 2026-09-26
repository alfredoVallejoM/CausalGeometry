import CausalGeometry.Calculus.CubicalLeibnizCoefficients
import CausalGeometry.Calculus.CubicalBackFaceStructure
import Mathlib.Tactic

namespace CausalGeometry

universe u v

open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalEventCube

/-- Complementary cube when p+q equals the ambient dimension only
propositionally. -/
noncomputable def complementCubeOfEq
    {n p q : ℕ}
    (h : p + q = n)
    (Q : CausalEventCube S n)
    (A : AxisSubset n p) :
    CausalEventCube S q := by
  subst n
  exact Q.complementCube A

@[simp] theorem complementCubeOfEq_base
    {n p q : ℕ}
    (h : p + q = n)
    (Q : CausalEventCube S n)
    (A : AxisSubset n p) :
    (complementCubeOfEq h Q A).base =
      Q.afterAxes A.val := by
  subst n
  rfl

@[simp] theorem complementCubeOfEq_event
    {n p q : ℕ}
    (h : p + q = n)
    (Q : CausalEventCube S n)
    (A : AxisSubset n p)
    (j : Fin q) :
    (complementCubeOfEq h Q A).frame.event j =
      Q.frame.event
        (Set.powersetCard.orderIsoOfFin
          (complementAxisSubset h A) j).1 := by
  subst n
  rfl

/-- Executing a selected subset on a lower face is the same configuration as
executing its lifted ambient subset from the original base. -/
theorem lowerFace_afterAxes_eq_afterAxes_lift
    {n p : ℕ}
    (Q : CausalEventCube S (n + 1))
    (i : Fin (n + 1))
    (A : AxisSubset n p) :
    (Q.lowerFace i).afterAxes A.val =
      Q.afterAxes (liftFaceSubset i A).val := by

  apply S.configuration_eq_of_carrier_eq

  ext e

  change
    (e ∈ Q.base ∨
      ∃ a ∈ A.val,
        Q.frame.event (i.succAbove a) = e)
      ↔
    (e ∈ Q.base ∨
      ∃ k ∈ (liftFaceSubset i A).val,
        Q.frame.event k = e)

  constructor

  · intro h
    rcases h with hbase | hsel
    · exact Or.inl hbase
    · rcases hsel with ⟨a, ha, hea⟩
      right
      refine
        ⟨i.succAbove a, ?_, hea⟩
      rw [mem_liftFaceSubset_iff]
      exact ⟨a, ha, rfl⟩

  · intro h
    rcases h with hbase | hsel
    · exact Or.inl hbase
    · rcases hsel with ⟨k, hk, hek⟩
      rw [mem_liftFaceSubset_iff] at hk
      rcases hk with ⟨a, ha, rfl⟩
      exact Or.inr ⟨a, ha, hek⟩

/-- Executing a selected subset on the upper i-face is the same as executing
the lifted subset together with i in the ambient cube. -/
theorem upperFace_afterAxes_eq_afterAxes_insertLift
    {n p : ℕ}
    (Q : CausalEventCube S (n + 1))
    (i : Fin (n + 1))
    (A : AxisSubset n p) :

    let LA :=
      liftFaceSubset i A

    let hi :=
      removedAxis_not_mem_liftFaceSubset i A

    (Q.upperFace i).afterAxes A.val =
      Q.afterAxes
        (insertAxisSubset LA i hi).val := by

  dsimp only

  let LA :=
    liftFaceSubset i A

  let hi :
      i ∉ LA :=
    removedAxis_not_mem_liftFaceSubset i A

  apply S.configuration_eq_of_carrier_eq

  ext e

  change
    (e ∈ Q.frame.after i ∨
      ∃ a ∈ A.val,
        Q.frame.event (i.succAbove a) = e)
      ↔
    (e ∈ Q.base ∨
      ∃ k ∈
          (insertAxisSubset LA i hi).val,
        Q.frame.event k = e)

  rw [CausalCubeFrame.after_carrier]

  constructor

  · intro h

    rcases h with hbase | hsel

    · rcases hbase with hei | hQ
      · right
        refine ⟨i, ?_, ?_⟩
        · exact insertedAxis_mem LA i hi
        · exact hei.symm
      · exact Or.inl hQ

    · rcases hsel with ⟨a, ha, hea⟩
      right
      refine
        ⟨i.succAbove a, ?_, hea⟩
      change
        i.succAbove a ∈
          insert i LA.val
      right
      rw [mem_liftFaceSubset_iff]
      exact ⟨a, ha, rfl⟩

  · intro h

    rcases h with hbase | hsel

    · exact Or.inl (Or.inr hbase)

    · rcases hsel with ⟨k, hk, hek⟩

      change
        k ∈ insert i LA.val at hk

      rcases Finset.mem_insert.mp hk with
        hki | hkLA

      · subst k
        exact Or.inl (Or.inl hek.symm)

      · rw [mem_liftFaceSubset_iff] at hkLA
        rcases hkLA with ⟨a, ha, rfl⟩
        exact Or.inr ⟨a, ha, hek⟩

end CausalEventCube
end CausalGeometry
