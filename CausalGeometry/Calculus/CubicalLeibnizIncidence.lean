import CausalGeometry.Calculus.CubicalSubsetGeometry
import Mathlib.Order.Fin.Tuple
import Mathlib.Tactic

namespace CausalGeometry

universe u v

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalEventCube

/-- Lift a p-subset of the n surviving axes of the i-th face to the ambient
(n+1)-cube.  The lifted subset automatically omits i. -/
noncomputable def liftFaceSubset
    {n p : ℕ}
    (i : Fin (n + 1))
    (A : AxisSubset n p) :
    AxisSubset (n + 1) p :=
  Set.powersetCard.ofFinEmbEquiv
    ((Set.powersetCard.ofFinEmbEquiv.symm A).trans
      i.succAboveOrderEmb)

/-- Membership in a lifted face subset is exactly membership of the unique
preimage under succAbove. -/
theorem mem_liftFaceSubset_iff
    {n p : ℕ}
    (i : Fin (n + 1))
    (A : AxisSubset n p)
    (k : Fin (n + 1)) :
    k ∈ liftFaceSubset i A ↔
      ∃ j : Fin n,
        j ∈ A ∧
          i.succAbove j = k := by

  rw [Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range]

  constructor

  · rintro ⟨a, ha⟩

    let j : Fin n :=
      (Set.powersetCard.ofFinEmbEquiv.symm A) a

    refine ⟨j, ?_, ?_⟩

    · rw [← Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem]
      exact ⟨a, rfl⟩

    · exact ha

  · rintro ⟨j, hjA, rfl⟩

    rw [← Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem] at hjA

    rcases hjA with ⟨a, ha⟩

    refine ⟨a, ?_⟩

    change
      i.succAbove
          ((Set.powersetCard.ofFinEmbEquiv.symm A) a)
        =
      i.succAbove j

    rw [ha]

/-- The removed ambient axis never belongs to a lifted face subset. -/
theorem removedAxis_not_mem_liftFaceSubset
    {n p : ℕ}
    (i : Fin (n + 1))
    (A : AxisSubset n p) :
    i ∉ liftFaceSubset i A := by

  intro hi

  rw [Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range] at hi

  rcases hi with ⟨j, hj⟩

  exact i.succAbove_ne
    ((Set.powersetCard.ofFinEmbEquiv.symm A) j)
    hj.symm

/-- Order embedding of an ambient p-subset into the complement of i, provided
i is not selected. -/
noncomputable def ambientSubsetIntoComplement
    {n p : ℕ}
    (A : AxisSubset (n + 1) p)
    (i : Fin (n + 1))
    (hi : i ∉ A) :
    Fin p ↪o {x : Fin (n + 1) // x ≠ i} :=

  let f :=
    Set.powersetCard.ofFinEmbEquiv.symm A

  { toFun := fun j =>
      ⟨f j, by
        intro hEq
        apply hi
        subst hEq
        rw [← Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem]
        exact ⟨j, rfl⟩⟩

    inj' := by
      intro a b h
      apply f.injective
      exact congrArg Subtype.val h

    map_rel_iff' := by
      intro a b
      exact f.map_rel_iff }

/-- Drop one omitted ambient axis and recover a p-subset of the corresponding
n-dimensional face. -/
noncomputable def dropAmbientSubset
    {n p : ℕ}
    (A : AxisSubset (n + 1) p)
    (i : Fin (n + 1))
    (hi : i ∉ A) :
    AxisSubset n p :=
  Set.powersetCard.ofFinEmbEquiv
    ((ambientSubsetIntoComplement A i hi).trans
      (finSuccAboveOrderIso i).symm.toOrderEmbedding)

/-- Dropping the subset lifted from a face recovers the original subset. -/
theorem dropAmbientSubset_liftFaceSubset
    {n p : ℕ}
    (i : Fin (n + 1))
    (A : AxisSubset n p) :
    dropAmbientSubset
        (liftFaceSubset i A)
        i
        (removedAxis_not_mem_liftFaceSubset i A)
      =
    A := by

  apply Set.powersetCard.ofFinEmbEquiv.injective

  apply OrderEmbedding.ext

  intro j

  change
    (finSuccAboveOrderIso i).symm
      ⟨
        i.succAbove
          ((Set.powersetCard.ofFinEmbEquiv.symm A) j),
        _
      ⟩
      =
    (Set.powersetCard.ofFinEmbEquiv.symm A) j

  exact
    congrArg Subtype.val
      ((finSuccAboveOrderIso i).symm_apply_apply
        ((Set.powersetCard.ofFinEmbEquiv.symm A) j))

/-- Lifting after dropping an ambient subset that omits i recovers that
ambient subset. -/
theorem liftFaceSubset_dropAmbientSubset
    {n p : ℕ}
    (A : AxisSubset (n + 1) p)
    (i : Fin (n + 1))
    (hi : i ∉ A) :
    liftFaceSubset i
        (dropAmbientSubset A i hi)
      =
    A := by

  apply Set.powersetCard.ofFinEmbEquiv.injective

  apply OrderEmbedding.ext

  intro j

  let f :=
    Set.powersetCard.ofFinEmbEquiv.symm A

  let g :=
    ambientSubsetIntoComplement A i hi

  change
    i.succAbove
      ((finSuccAboveOrderIso i).symm
        (g j))
      =
    f j

  have h :=
    (finSuccAboveOrderIso i).apply_symm_apply
      (g j)

  exact congrArg Subtype.val h

/-- Common indexing type for one ambient face and one p-subset of its surviving
axes. -/
abbrev FaceSubsetIndex
    (n p : ℕ) :=
  Σ i : Fin (n + 1),
    AxisSubset n p

/-- Equivalent ambient indexing: a p-subset together with one omitted axis. -/
abbrev OmittedAxisIndex
    (n p : ℕ) :=
  Σ A : AxisSubset (n + 1) p,
    {i : Fin (n + 1) // i ∉ A}

/-- Canonical equivalence between the two indexings used by the Leibniz
expansion. -/
noncomputable def faceSubsetOmittedEquiv
    (n p : ℕ) :
    FaceSubsetIndex n p ≃
      OmittedAxisIndex n p where

  toFun := fun x =>
    ⟨liftFaceSubset x.1 x.2,
      ⟨x.1,
        removedAxis_not_mem_liftFaceSubset
          x.1 x.2⟩⟩

  invFun := fun x =>
    ⟨x.2.1,
      dropAmbientSubset
        x.1 x.2.1 x.2.2⟩

  left_inv := by
    intro x
    apply Sigma.ext
    · rfl
    · exact
        dropAmbientSubset_liftFaceSubset
          x.1 x.2

  right_inv := by
    intro x
    apply Sigma.ext
    · exact
        liftFaceSubset_dropAmbientSubset
          x.1 x.2.1 x.2.2
    · apply Subtype.ext
      rfl

end CausalEventCube
end CausalGeometry
