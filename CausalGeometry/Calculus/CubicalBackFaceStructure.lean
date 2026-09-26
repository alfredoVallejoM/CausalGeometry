import CausalGeometry.Calculus.CubicalFrontBack
import CausalGeometry.Calculus.CubicalSubsetGeometry
import CausalGeometry.Calculus.CubicalSubsetCup
import Mathlib.Tactic

namespace CausalGeometry

universe u v

open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalEventCube

/-- Primitive events carried by the first p coordinates of a (p+q)-cube. -/
def prefixEventSet
    (p q : ℕ)
    (Q : CausalEventCube S (p + q)) :
    Set Event :=
  {e | ∃ i : Fin p,
      Q.frame.event (Fin.castAdd q i) = e}

@[simp] theorem mem_prefixEventSet_iff
    (p q : ℕ)
    (Q : CausalEventCube S (p + q))
    (e : Event) :
    e ∈ Q.prefixEventSet p q ↔
      ∃ i : Fin p,
        Q.frame.event (Fin.castAdd q i) = e :=
  Iff.rfl

theorem castAdd_zero_index
    (p q : ℕ) :
    Fin.castAdd q (0 : Fin (p + 1))
      =
    (0 : Fin (p + 1 + q)) := by
  apply Fin.ext
  rfl

theorem castAdd_succ_index
    (p q : ℕ)
    (i : Fin p) :
    Fin.castAdd q i.succ
      =
    (Fin.castAdd q i).succ := by
  apply Fin.ext
  rfl

theorem zero_succAbove_castAdd
    (p q : ℕ)
    (i : Fin p) :
    (0 : Fin ((p + q) + 1)).succAbove
        (Fin.castAdd q i)
      =
    Fin.cast
      (by omega)
      (Fin.castAdd q i.succ) := by
  apply Fin.ext
  rfl

/-- Back faces retain exactly the final q event coordinates. -/
theorem backFace_event
    (p q : ℕ)
    (Q : CausalEventCube S (p + q))
    (j : Fin q) :
    (Q.backFace p q).frame.event j =
      Q.frame.event (Fin.natAdd p j) := by
  induction p generalizing Q with

  | zero =>
      simp [backFace, castDim]

  | succ p ih =>
      change
        (backFace p q
          ((castDim (Nat.succ_add p q) Q)
            .upperFace (0 : Fin ((p + q) + 1)))).frame.event j
          =
        Q.frame.event (Fin.natAdd (p + 1) j)

      rw [ih]

      change
        (castDim (Nat.succ_add p q) Q).frame.event
          ((0 : Fin ((p + q) + 1)).succAbove
            (Fin.natAdd p j))
          =
        Q.frame.event (Fin.natAdd (p + 1) j)

      apply congrArg Q.frame.event

      apply Fin.ext
      rfl

/-- The base of the back q-face is the original base together with exactly the
first p primitive events. -/
theorem backFace_base_carrier
    (p q : ℕ)
    (Q : CausalEventCube S (p + q)) :
    (Q.backFace p q).base.carrier =
      Q.base.carrier ∪
        Q.prefixEventSet p q := by

  induction p generalizing Q with

  | zero =>
      ext e
      simp [backFace, castDim,
        prefixEventSet]

  | succ p ih =>
      let Q' :
          CausalEventCube S ((p + q) + 1) :=
        castDim (Nat.succ_add p q) Q

      let U :
          CausalEventCube S (p + q) :=
        Q'.upperFace
          (0 : Fin ((p + q) + 1))

      change
        (backFace p q U).base.carrier =
          Q.base.carrier ∪
            Q.prefixEventSet (p + 1) q

      rw [ih U]

      ext e

      change
        (e ∈ U.base ∨
          ∃ i : Fin p,
            U.frame.event
                (Fin.castAdd q i)
              =
            e)
          ↔
        (e ∈ Q.base ∨
          ∃ i : Fin (p + 1),
            Q.frame.event
                (Fin.castAdd q i)
              =
            e)

      have hbase :
          e ∈ U.base ↔
            e = Q.frame.event
                (Fin.castAdd q
                  (0 : Fin (p + 1)))
              ∨
            e ∈ Q.base := by
        change
          e ∈ Q'.frame.after 0 ↔
            _
        rw [CausalCubeFrame.after_carrier]
        simp only [Set.mem_insert_iff]
        constructor
        · intro h
          rcases h with h | h
          · left
            simpa [Q', castDim,
              castAdd_zero_index] using h
          · right
            simpa [Q', castDim] using h
        · intro h
          rcases h with h | h
          · left
            simpa [Q', castDim,
              castAdd_zero_index] using h
          · right
            simpa [Q', castDim] using h

      have hevent :
          ∀ i : Fin p,
            U.frame.event (Fin.castAdd q i)
              =
            Q.frame.event
              (Fin.castAdd q i.succ) := by
        intro i
        change
          Q'.frame.event
              ((0 : Fin ((p + q) + 1)).succAbove
                (Fin.castAdd q i))
            =
          Q.frame.event
            (Fin.castAdd q i.succ)

        simp only [Fin.zero_succAbove]

        simpa [Q', castDim] using
          rfl

      rw [hbase]

      constructor

      · intro h
        rcases h with
          (hzero | hbaseQ) | htail
        · right
          exact ⟨0, hzero.symm⟩
        · exact Or.inl hbaseQ
        · right
          rcases htail with ⟨i, hi⟩
          refine ⟨i.succ, ?_⟩
          rw [← hevent i]
          exact hi

      · intro h
        rcases h with hbaseQ | hpref
        · exact Or.inl (Or.inr hbaseQ)
        · rcases hpref with ⟨i, hi⟩
          refine Fin.cases ?_ ?_ i
          · exact Or.inl
              (Or.inl hi.symm)
          · intro j
            exact Or.inr
              ⟨j, by
                rw [hevent j]
                exact hi⟩

/-- For the canonical permutation associated to A, the first p event set is
exactly the selected event set A. -/
theorem prefixEventSet_permute_subset
    {p q : ℕ}
    (Q : CausalEventCube S (p + q))
    (A : AxisSubset (p + q) p) :
    (Q.permute (subsetPermutation A))
        .prefixEventSet p q
      =
    Q.selectedEventSet A.val := by

  ext e

  constructor

  · rintro ⟨i, hi⟩

    refine ⟨
      (Set.powersetCard.orderIsoOfFin A i).1,
      (Set.powersetCard.orderIsoOfFin A i).2,
      ?_⟩

    change
      Q.frame.event
          (subsetPermutation A
            (Fin.castAdd q i))
        =
      e

    rw [subsetPermutation_left]

    exact hi

  · rintro ⟨k, hkA, hk⟩

    let i : Fin p :=
      (Set.powersetCard.orderIsoOfFin A).symm
        ⟨k, hkA⟩

    refine ⟨i, ?_⟩

    change
      Q.frame.event
          (subsetPermutation A
            (Fin.castAdd q i))
        =
      e

    rw [subsetPermutation_left]

    have hi :
        (Set.powersetCard.orderIsoOfFin A i).1 =
          k := by
      exact congrArg Subtype.val
        ((Set.powersetCard.orderIsoOfFin A)
          .apply_symm_apply ⟨k, hkA⟩)

    rw [hi]

    exact hk

/-- The canonical back face has exactly the same base configuration as the
intrinsic complementary cube. -/
theorem backFace_subset_base
    {p q : ℕ}
    (Q : CausalEventCube S (p + q))
    (A : AxisSubset (p + q) p) :
    ((Q.permute (subsetPermutation A))
      .backFace p q).base
      =
    (Q.complementCube A).base := by

  apply S.configuration_eq_of_carrier_eq

  rw [backFace_base_carrier]

  rw [prefixEventSet_permute_subset]

  rfl

/-- The canonical back face is exactly the complementary intrinsic cube. -/
theorem complementCube_eq_backFace
    {p q : ℕ}
    (Q : CausalEventCube S (p + q))
    (A : AxisSubset (p + q) p) :
    Q.complementCube A =
      (Q.permute (subsetPermutation A))
        .backFace p q := by

  apply CausalEventCube.ext

  · symm
    exact backFace_subset_base Q A

  · funext j

    rw [backFace_event]

    change
      Q.frame.event
          (Set.powersetCard.orderIsoOfFin
            A.complementAxes j).1
        =
      Q.frame.event
        (subsetPermutation A
          (Fin.natAdd p j))

    rw [subsetPermutation_right]

    rfl

end CausalEventCube
end CausalGeometry
