import CausalGeometry.Calculus.CubeEquivariance
import CausalGeometry.Calculus.FormEquivariance
import CausalGeometry.Calculus.CohomologyH2

namespace CausalGeometry

universe u₁ v₁ u₂ v₂ w

open EventSystem

variable
    {Event₁ : Type u₁} {Label₁ : Type v₁}
    {Event₂ : Type u₂} {Label₂ : Type v₂}
    {S₁ : EventSystem Event₁ Label₁}
    {S₂ : EventSystem Event₂ Label₂}

namespace EventSystemEquiv

variable (E : EventSystemEquiv S₁ S₂)
variable {K : Type w} [AddCommGroup K]

/-- Variation of a two-form along one cube direction is natural under
primitive causal-system isomorphism. -/
theorem variationAlong_two_natural
    (ω : CausalTwoForm S₂ K)
    {C : Configuration S₁}
    {ι : Type*}
    (Q : CausalCubeFrame S₁ C ι)
    (i j k : ι)
    (hji : j ≠ i)
    (hki : k ≠ i)
    (hjk : j ≠ k) :
    CausalTwoForm.variationAlong
        (E.pullTwoForm ω)
        Q i j k hji hki hjk
      =
    CausalTwoForm.variationAlong
        ω
        (E.mapCubeFrame Q)
        i j k hji hki hjk := by
  unfold CausalTwoForm.variationAlong
    pullTwoForm
  rw [
    E.map_cube_diamondAfter_value
      ω Q i j k hji hki hjk,
    E.map_cube_diamond_value
      ω Q j k hjk
  ]

/-- Exterior derivative of causal two-forms is natural. -/
theorem exteriorDerivative_two_natural
    (ω : CausalTwoForm S₂ K)
    {C : Configuration S₁}
    {ι : Type*}
    (Q : CausalCubeFrame S₁ C ι)
    (i j k : ι)
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k) :
    CausalTwoForm.exteriorDerivative
        (E.pullTwoForm ω)
        Q i j k hij hik hjk
      =
    CausalTwoForm.exteriorDerivative
        ω
        (E.mapCubeFrame Q)
        i j k hij hik hjk := by
  unfold CausalTwoForm.exteriorDerivative
  rw [
    E.variationAlong_two_natural
      ω Q i j k
      hij.symm hik.symm hjk,
    E.variationAlong_two_natural
      ω Q j i k
      hij hjk.symm hik,
    E.variationAlong_two_natural
      ω Q k i j
      hik hjk hij
  ]

/-- Closedness of causal two-forms is representation invariant. -/
theorem pullTwoForm_closed
    {ω : CausalTwoForm S₂ K}
    (hω : ω.Closed) :
    (E.pullTwoForm ω).Closed := by
  intro C ι Q i j k hij hik hjk
  rw [
    E.exteriorDerivative_two_natural
      ω Q i j k hij hik hjk
  ]
  exact hω
    (E.mapCubeFrame Q)
    i j k hij hik hjk

/-- Closed two-forms are additively equivalent under causal-system
isomorphism. -/
def closedTwoFormAddEquiv :
    CausalCohomology.ClosedTwoForms
        (S := S₁) (K := K) ≃+
      CausalCohomology.ClosedTwoForms
        (S := S₂) (K := K) where
  toFun := fun ω =>
    ⟨E.symm.pullTwoForm
        (ω : CausalTwoForm S₁ K),
      E.symm.pullTwoForm_closed ω.2⟩

  invFun := fun ω =>
    ⟨E.pullTwoForm
        (ω : CausalTwoForm S₂ K),
      E.pullTwoForm_closed ω.2⟩

  left_inv := by
    intro ω
    apply Subtype.ext
    exact E.pullTwoForm_symm_pullTwoForm
      (ω : CausalTwoForm S₁ K)

  right_inv := by
    intro ω
    apply Subtype.ext
    exact E.symm_pullTwoForm_pullTwoForm
      (ω : CausalTwoForm S₂ K)

  map_add' := by
    intro ω η
    apply Subtype.ext
    rfl

/-- Exactness of two-forms is preserved. -/
theorem closedTwoFormAddEquiv_exact
    (ω :
      CausalCohomology.ClosedTwoForms
        (S := S₁) (K := K))
    (hω :
      (ω : CausalTwoForm S₁ K) ∈
        CausalCohomology.ExactTwoForms
          (S := S₁) (K := K)) :
    ((E.closedTwoFormAddEquiv ω :
        CausalCohomology.ClosedTwoForms
          (S := S₂) (K := K)) :
      CausalTwoForm S₂ K) ∈
        CausalCohomology.ExactTwoForms
          (S := S₂) (K := K) := by
  rcases hω with ⟨α, hα⟩
  refine ⟨E.symm.pullOneForm α, ?_⟩
  change
    CausalTwoForm.ofExteriorDerivative
        (E.symm.pullOneForm α)
      =
    E.symm.pullTwoForm
      (ω : CausalTwoForm S₁ K)
  rw [
    ← E.symm.pullTwoForm_exteriorDerivative α
  ]
  exact congrArg E.symm.pullTwoForm hα

/-- Exactness is reflected as well. -/
theorem closedTwoFormAddEquiv_exact_iff
    (ω :
      CausalCohomology.ClosedTwoForms
        (S := S₁) (K := K)) :
    (((E.closedTwoFormAddEquiv ω :
        CausalCohomology.ClosedTwoForms
          (S := S₂) (K := K)) :
      CausalTwoForm S₂ K) ∈
        CausalCohomology.ExactTwoForms
          (S := S₂) (K := K))
      ↔
    ((ω : CausalTwoForm S₁ K) ∈
        CausalCohomology.ExactTwoForms
          (S := S₁) (K := K)) := by
  constructor
  · intro h
    have hback :=
      E.symm.closedTwoFormAddEquiv_exact
        (E.closedTwoFormAddEquiv ω) h
    simpa using hback
  · exact E.closedTwoFormAddEquiv_exact ω

/-- Map on second causal cohomology. -/
def h2Map :
    CausalCohomology.H2
        (S := S₁) (K := K) →+
      CausalCohomology.H2
        (S := S₂) (K := K) :=
  QuotientAddGroup.lift
    (CausalCohomology.ExactTwoInClosed
      (S := S₁) (K := K))
    ((CausalCohomology.classOfClosedTwo
        (S := S₂) (K := K)).comp
      E.closedTwoFormAddEquiv.toAddMonoidHom)
    (by
      intro ω hω
      apply AddMonoidHom.mem_ker.mpr
      apply
        (CausalCohomology.classOfClosedTwo_eq_zero_iff
          (S := S₂) (K := K)).2
      change
        ((E.closedTwoFormAddEquiv ω :
            CausalCohomology.ClosedTwoForms
              (S := S₂) (K := K)) :
          CausalTwoForm S₂ K) ∈
            CausalCohomology.ExactTwoForms
              (S := S₂) (K := K)
      change
        (ω : CausalTwoForm S₁ K) ∈
          CausalCohomology.ExactTwoForms
            (S := S₁) (K := K) at hω
      exact
        E.closedTwoFormAddEquiv_exact
          ω hω)

/-- H2 map on a represented closed two-form. -/
@[simp] theorem h2Map_classOfClosedTwo
    (ω :
      CausalCohomology.ClosedTwoForms
        (S := S₁) (K := K)) :
    E.h2Map
        (CausalCohomology.classOfClosedTwo
          (S := S₁) (K := K) ω)
      =
    CausalCohomology.classOfClosedTwo
      (S := S₂) (K := K)
      (E.closedTwoFormAddEquiv ω) := by
  rfl

theorem h2Map_symm_h2Map
    (x :
      CausalCohomology.H2
        (S := S₁) (K := K)) :
    E.symm.h2Map (E.h2Map x) = x := by
  induction x using QuotientAddGroup.induction_on with
  | H ω =>
      rw [E.h2Map_classOfClosedTwo,
        E.symm.h2Map_classOfClosedTwo]
      congr 1
      apply Subtype.ext
      exact E.pullTwoForm_symm_pullTwoForm
        (ω : CausalTwoForm S₁ K)

theorem h2Map_h2Map_symm
    (x :
      CausalCohomology.H2
        (S := S₂) (K := K)) :
    E.h2Map (E.symm.h2Map x) = x := by
  induction x using QuotientAddGroup.induction_on with
  | H ω =>
      rw [E.symm.h2Map_classOfClosedTwo,
        E.h2Map_classOfClosedTwo]
      congr 1
      apply Subtype.ext
      exact E.symm_pullTwoForm_pullTwoForm
        (ω : CausalTwoForm S₂ K)

/-- Second causal cohomology is invariant under primitive causal-system
isomorphism. -/
def h2AddEquiv :
    CausalCohomology.H2
        (S := S₁) (K := K) ≃+
      CausalCohomology.H2
        (S := S₂) (K := K) where
  toFun := E.h2Map
  invFun := E.symm.h2Map
  left_inv := E.h2Map_symm_h2Map
  right_inv := E.h2Map_h2Map_symm
  map_add' := by
    intro x y
    exact map_add E.h2Map x y

end EventSystemEquiv
end CausalGeometry
