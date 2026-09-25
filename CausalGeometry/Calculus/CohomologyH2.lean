import CausalGeometry.Calculus.Cohomology

namespace CausalGeometry

universe u v w
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalCohomology

variable {K : Type w} [AddCommGroup K]

/-- Antisymmetric raw degree-two cochains form an additive subgroup. -/
def SkewTwoCochains :
    AddSubgroup (RawTwoCochain S K) where
  carrier := fun φ =>
    ∀ (C : Configuration S)
      (e f : Event)
      (d : ConcurrencyDiamond C e f),
      φ C f e d.symm =
        - φ C e f d
  zero_mem' := by
    intro C e f d
    simp
  add_mem' := by
    intro φ ψ hφ hψ C e f d
    rw [Pi.add_apply, Pi.add_apply,
      Pi.add_apply, Pi.add_apply,
      hφ C e f d, hψ C e f d]
    simp
    abel
  neg_mem' := by
    intro φ hφ C e f d
    rw [Pi.neg_apply, Pi.neg_apply,
      Pi.neg_apply, Pi.neg_apply,
      hφ C e f d]
    simp

/-- Packaged causal two-forms are exactly skew raw two-cochains. -/
def twoFormEquivSkew :
    CausalTwoForm S K ≃
      SkewTwoCochains (S := S) (K := K) where
  toFun := fun ω =>
    ⟨fun C e f d => ω.value d,
      fun C e f d => ω.skew d⟩
  invFun := fun φ =>
    { value := fun d =>
        φ.1 _ _ _ d
      skew := by
        intro C e f d
        exact φ.2 C e f d }
  left_inv := by
    intro ω
    apply CausalTwoForm.ext
    intro C e f d
    rfl
  right_inv := by
    intro φ
    apply Subtype.ext
    funext C e f d
    rfl

instance :
    AddCommGroup (CausalTwoForm S K) :=
  (twoFormEquivSkew
    (S := S) (K := K)).addCommGroup

@[simp] theorem twoForm_zero_value
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    (0 : CausalTwoForm S K).value d = 0 := by
  rfl

@[simp] theorem twoForm_add_value
    (ω η : CausalTwoForm S K)
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    (ω + η).value d =
      ω.value d + η.value d := by
  rfl

@[simp] theorem twoForm_neg_value
    (ω : CausalTwoForm S K)
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    (-ω).value d =
      - ω.value d := by
  rfl

/-- The packed degree-one exterior differential. -/
def d1Alt :
    CausalOneForm S K →+
      CausalTwoForm S K where
  toFun :=
    CausalTwoForm.ofExteriorDerivative
  map_zero' := by
    apply CausalTwoForm.ext
    intro C e f d
    simp [
      CausalTwoForm.ofExteriorDerivative,
      CausalOneForm.exteriorDerivative,
      CausalOneForm.variationEF,
      CausalOneForm.variationFE
    ]
  map_add' := by
    intro ω η
    apply CausalTwoForm.ext
    intro C e f d
    simp [
      CausalTwoForm.ofExteriorDerivative,
      CausalOneForm.exteriorDerivative,
      CausalOneForm.variationEF,
      CausalOneForm.variationFE
    ]
    abel

/-- Packed and raw d1 carry the same scalar value on every diamond. -/
@[simp] theorem d1Alt_value
    (ω : CausalOneForm S K)
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    (d1Alt (S := S) (K := K) ω).value d =
      d1 (S := S) (K := K) ω C e f d :=
  rfl

/-- Closed causal two-forms form an additive subgroup. -/
def ClosedTwoForms :
    AddSubgroup (CausalTwoForm S K) where
  carrier :=
    CausalTwoForm.Closed
  zero_mem' := by
    have h0 :
        (0 : CausalTwoForm S K) =
          CausalTwoForm.zero := by
      apply CausalTwoForm.ext
      intro C e f d
      rfl
    rw [h0]
    exact CausalTwoForm.zero_closed
  add_mem' := by
    intro ω η hω hη
    have hadd :
        ω + η =
          CausalTwoForm.add ω η := by
      apply CausalTwoForm.ext
      intro C e f d
      rfl
    rw [hadd]
    exact CausalTwoForm.add_closed
      hω hη
  neg_mem' := by
    intro ω hω
    have hneg :
        -ω =
          CausalTwoForm.neg ω := by
      apply CausalTwoForm.ext
      intro C e f d
      rfl
    rw [hneg]
    exact CausalTwoForm.neg_closed hω

/-- Exact causal two-forms are exterior derivatives of one-forms. -/
def ExactTwoForms :
    AddSubgroup (CausalTwoForm S K) :=
  (d1Alt (S := S) (K := K)).range

/-- Second d-squared law gives exact two-forms are closed. -/
theorem exactTwo_le_closed :
    ExactTwoForms (S := S) (K := K) ≤
      ClosedTwoForms (S := S) (K := K) := by
  intro η hη
  rcases hη with ⟨ω, rfl⟩
  exact
    CausalExteriorComplex.exteriorDerivative_closed
      ω

/-- Exact subgroup inside the closed subgroup. -/
def ExactTwoInClosed :
    AddSubgroup
      (ClosedTwoForms (S := S) (K := K)) :=
  (ExactTwoForms (S := S) (K := K)).comap
    (ClosedTwoForms (S := S) (K := K)).subtype

/-- Second causal cohomology group. -/
abbrev H2 :=
  QuotientAddGroup.quotient
    (ExactTwoInClosed (S := S) (K := K))

/-- Canonical class map for closed causal two-forms. -/
def classOfClosedTwo :
    ClosedTwoForms (S := S) (K := K) →+
      H2 (S := S) (K := K) :=
  QuotientAddGroup.mk'
    (ExactTwoInClosed (S := S) (K := K))

/-- A closed two-form has trivial H2 class exactly when it is exact. -/
theorem classOfClosedTwo_eq_zero_iff
    (ω :
      ClosedTwoForms (S := S) (K := K)) :
    classOfClosedTwo (S := S) (K := K) ω = 0 ↔
      (ω : CausalTwoForm S K) ∈
        ExactTwoForms (S := S) (K := K) := by
  rw [QuotientAddGroup.eq_zero_iff]
  rfl

/-- Every exterior derivative represents the zero H2 class. -/
theorem exteriorDerivative_class_zero
    (ω : CausalOneForm S K) :
    classOfClosedTwo
        (S := S) (K := K)
        ⟨d1Alt (S := S) (K := K) ω,
          exactTwo_le_closed
            (S := S) (K := K)
            ⟨ω, rfl⟩⟩ =
      0 := by
  apply
    (classOfClosedTwo_eq_zero_iff
      (S := S) (K := K)).2
  exact ⟨ω, rfl⟩

end CausalCohomology
end CausalGeometry
