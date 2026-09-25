import CausalGeometry.Calculus.CohomologyEquivH1
import CausalGeometry.Calculus.CohomologyEquivH2

namespace CausalGeometry

universe u₁ v₁ u₂ v₂ u₃ v₃ w

open EventSystem

variable
    {Event₁ : Type u₁} {Label₁ : Type v₁}
    {Event₂ : Type u₂} {Label₂ : Type v₂}
    {Event₃ : Type u₃} {Label₃ : Type v₃}
    {S₁ : EventSystem Event₁ Label₁}
    {S₂ : EventSystem Event₂ Label₂}
    {S₃ : EventSystem Event₃ Label₃}

namespace EventSystemEquiv

variable {K : Type w} [AddCommGroup K]

/-- Pullback of one-forms along the identity is identity. -/
@[simp] theorem pullOneForm_refl
    (S : EventSystem Event₁ Label₁)
    (ω : CausalOneForm S K) :
    (EventSystemEquiv.refl S).pullOneForm ω =
      ω := by
  apply CausalOneForm.ext
  intro C d
  unfold pullOneForm
  have hC :=
    EventSystemEquiv.refl_mapConfiguration
      S C
  cases hC
  congr 1
  apply EventDirection.ext
  rfl

/-- One-form pullback is contravariantly functorial. -/
theorem pullOneForm_trans
    (E₁₂ : EventSystemEquiv S₁ S₂)
    (E₂₃ : EventSystemEquiv S₂ S₃)
    (ω : CausalOneForm S₃ K) :
    (E₁₂.trans E₂₃).pullOneForm ω =
      E₁₂.pullOneForm
        (E₂₃.pullOneForm ω) := by
  apply CausalOneForm.ext
  intro C d
  unfold pullOneForm
  have hC :=
    E₁₂.trans_mapConfiguration
      E₂₃ C
  cases hC
  congr 1
  apply EventDirection.ext
  rfl

/-- Pullback of two-forms along identity is identity. -/
@[simp] theorem pullTwoForm_refl
    (S : EventSystem Event₁ Label₁)
    (ω : CausalTwoForm S K) :
    (EventSystemEquiv.refl S).pullTwoForm ω =
      ω := by
  apply CausalTwoForm.ext
  intro C e f d
  unfold pullTwoForm
  congr 1
  exact
    EventSystemEquiv.concurrencyDiamond_eq
      _ _

/-- Two-form pullback is contravariantly functorial. -/
theorem pullTwoForm_trans
    (E₁₂ : EventSystemEquiv S₁ S₂)
    (E₂₃ : EventSystemEquiv S₂ S₃)
    (ω : CausalTwoForm S₃ K) :
    (E₁₂.trans E₂₃).pullTwoForm ω =
      E₁₂.pullTwoForm
        (E₂₃.pullTwoForm ω) := by
  apply CausalTwoForm.ext
  intro C e f d
  unfold pullTwoForm
  have hC :=
    E₁₂.trans_mapConfiguration
      E₂₃ C
  cases hC
  congr 1
  exact
    EventSystemEquiv.concurrencyDiamond_eq
      _ _

/-- H1 transport along identity is identity. -/
@[simp] theorem h1Map_refl
    (S : EventSystem Event₁ Label₁)
    (x :
      CausalCohomology.H1
        (S := S) (K := K)) :
    (EventSystemEquiv.refl S).h1Map x =
      x := by
  induction x using QuotientAddGroup.induction_on with
  | H ω =>
      rw [
        EventSystemEquiv.h1Map_classOfClosed
      ]
      congr 1
      apply Subtype.ext
      simpa using
        EventSystemEquiv.pullOneForm_refl
          S (ω : CausalOneForm S K)

/-- H1 transport respects composition of primitive causal isomorphisms. -/
theorem h1Map_trans
    (E₁₂ : EventSystemEquiv S₁ S₂)
    (E₂₃ : EventSystemEquiv S₂ S₃)
    (x :
      CausalCohomology.H1
        (S := S₁) (K := K)) :
    (E₁₂.trans E₂₃).h1Map x =
      E₂₃.h1Map (E₁₂.h1Map x) := by
  induction x using QuotientAddGroup.induction_on with
  | H ω =>
      rw [
        EventSystemEquiv.h1Map_classOfClosed,
        EventSystemEquiv.h1Map_classOfClosed,
        EventSystemEquiv.h1Map_classOfClosed
      ]
      congr 1
      apply Subtype.ext
      change
        (E₁₂.trans E₂₃).symm.pullOneForm
            (ω : CausalOneForm S₁ K)
          =
        E₂₃.symm.pullOneForm
          (E₁₂.symm.pullOneForm
            (ω : CausalOneForm S₁ K))
      rw [EventSystemEquiv.symm_trans]
      exact
        EventSystemEquiv.pullOneForm_trans
          E₂₃.symm E₁₂.symm
          (ω : CausalOneForm S₁ K)

/-- H2 transport along identity is identity. -/
@[simp] theorem h2Map_refl
    (S : EventSystem Event₁ Label₁)
    (x :
      CausalCohomology.H2
        (S := S) (K := K)) :
    (EventSystemEquiv.refl S).h2Map x =
      x := by
  induction x using QuotientAddGroup.induction_on with
  | H ω =>
      rw [
        EventSystemEquiv.h2Map_classOfClosedTwo
      ]
      congr 1
      apply Subtype.ext
      simpa using
        EventSystemEquiv.pullTwoForm_refl
          S (ω : CausalTwoForm S K)

/-- H2 transport respects composition. -/
theorem h2Map_trans
    (E₁₂ : EventSystemEquiv S₁ S₂)
    (E₂₃ : EventSystemEquiv S₂ S₃)
    (x :
      CausalCohomology.H2
        (S := S₁) (K := K)) :
    (E₁₂.trans E₂₃).h2Map x =
      E₂₃.h2Map (E₁₂.h2Map x) := by
  induction x using QuotientAddGroup.induction_on with
  | H ω =>
      rw [
        EventSystemEquiv.h2Map_classOfClosedTwo,
        EventSystemEquiv.h2Map_classOfClosedTwo,
        EventSystemEquiv.h2Map_classOfClosedTwo
      ]
      congr 1
      apply Subtype.ext
      change
        (E₁₂.trans E₂₃).symm.pullTwoForm
            (ω : CausalTwoForm S₁ K)
          =
        E₂₃.symm.pullTwoForm
          (E₁₂.symm.pullTwoForm
            (ω : CausalTwoForm S₁ K))
      rw [EventSystemEquiv.symm_trans]
      exact
        EventSystemEquiv.pullTwoForm_trans
          E₂₃.symm E₁₂.symm
          (ω : CausalTwoForm S₁ K)

/-- Group-level H1 equivalence of the identity event-system isomorphism is
the identity AddEquiv. -/
theorem h1AddEquiv_refl
    (S : EventSystem Event₁ Label₁) :
    (EventSystemEquiv.refl S).h1AddEquiv
      =
    AddEquiv.refl
      (CausalCohomology.H1
        (S := S) (K := K)) := by
  ext x
  exact
    EventSystemEquiv.h1Map_refl
      S x

/-- H1 equivalence is functorial under composition. -/
theorem h1AddEquiv_trans
    (E₁₂ : EventSystemEquiv S₁ S₂)
    (E₂₃ : EventSystemEquiv S₂ S₃) :
    (E₁₂.trans E₂₃).h1AddEquiv
      =
    E₁₂.h1AddEquiv.trans
      E₂₃.h1AddEquiv := by
  ext x
  exact
    EventSystemEquiv.h1Map_trans
      E₁₂ E₂₃ x

@[simp] theorem h2AddEquiv_refl
    (S : EventSystem Event₁ Label₁) :
    (EventSystemEquiv.refl S).h2AddEquiv
      =
    AddEquiv.refl
      (CausalCohomology.H2
        (S := S) (K := K)) := by
  ext x
  exact
    EventSystemEquiv.h2Map_refl
      S x

theorem h2AddEquiv_trans
    (E₁₂ : EventSystemEquiv S₁ S₂)
    (E₂₃ : EventSystemEquiv S₂ S₃) :
    (E₁₂.trans E₂₃).h2AddEquiv
      =
    E₁₂.h2AddEquiv.trans
      E₂₃.h2AddEquiv := by
  ext x
  exact
    EventSystemEquiv.h2Map_trans
      E₁₂ E₂₃ x

end EventSystemEquiv
end CausalGeometry
