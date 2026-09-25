import CausalGeometry.Calculus.FormEquivariance

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

/-- Closed one-forms are additively equivalent under causal-system
isomorphism. -/
def closedOneFormAddEquiv :
    CausalCohomology.ClosedOneForms
        (S := S₁) (K := K) ≃+
      CausalCohomology.ClosedOneForms
        (S := S₂) (K := K) where
  toFun := fun ω =>
    ⟨E.symm.pullOneForm (ω : CausalOneForm S₁ K),
      E.symm.pullOneForm_closed ω.2⟩

  invFun := fun ω =>
    ⟨E.pullOneForm (ω : CausalOneForm S₂ K),
      E.pullOneForm_closed ω.2⟩

  left_inv := by
    intro ω
    apply Subtype.ext
    exact E.pullOneForm_symm_pullOneForm
      (ω : CausalOneForm S₁ K)

  right_inv := by
    intro ω
    apply Subtype.ext
    exact E.symm_pullOneForm_pullOneForm
      (ω : CausalOneForm S₂ K)

  map_add' := by
    intro ω η
    apply Subtype.ext
    rfl

@[simp] theorem closedOneFormAddEquiv_apply_coe
    (ω :
      CausalCohomology.ClosedOneForms
        (S := S₁) (K := K)) :
    ((E.closedOneFormAddEquiv ω :
        CausalCohomology.ClosedOneForms
          (S := S₂) (K := K)) :
      CausalOneForm S₂ K)
      =
    E.symm.pullOneForm
      (ω : CausalOneForm S₁ K) :=
  rfl

/-- Exactness is preserved by the forward cohomological equivalence. -/
theorem closedOneFormAddEquiv_exact
    (ω :
      CausalCohomology.ClosedOneForms
        (S := S₁) (K := K))
    (hω :
      (ω : CausalOneForm S₁ K) ∈
        CausalCohomology.ExactOneForms
          (S := S₁) (K := K)) :
    ((E.closedOneFormAddEquiv ω :
        CausalCohomology.ClosedOneForms
          (S := S₂) (K := K)) :
      CausalOneForm S₂ K) ∈
        CausalCohomology.ExactOneForms
          (S := S₂) (K := K) := by
  rcases hω with ⟨F, hF⟩
  refine ⟨E.symm.pullObservable F, ?_⟩
  change
    CausalOneForm.exact
        (E.symm.pullObservable F) =
      E.symm.pullOneForm
        (ω : CausalOneForm S₁ K)
  rw [← E.symm.pullOneForm_exact F]
  exact congrArg E.symm.pullOneForm hF

/-- Exactness is also reflected by the equivalence. -/
theorem closedOneFormAddEquiv_exact_iff
    (ω :
      CausalCohomology.ClosedOneForms
        (S := S₁) (K := K)) :
    (((E.closedOneFormAddEquiv ω :
        CausalCohomology.ClosedOneForms
          (S := S₂) (K := K)) :
      CausalOneForm S₂ K) ∈
        CausalCohomology.ExactOneForms
          (S := S₂) (K := K))
      ↔
    ((ω : CausalOneForm S₁ K) ∈
        CausalCohomology.ExactOneForms
          (S := S₁) (K := K)) := by
  constructor
  · intro h
    have hback :=
      E.symm.closedOneFormAddEquiv_exact
        (E.closedOneFormAddEquiv ω) h
    simpa using hback
  · exact E.closedOneFormAddEquiv_exact ω

/-- Map on first causal cohomology induced by a causal-system isomorphism. -/
def h1Map :
    CausalCohomology.H1
        (S := S₁) (K := K) →+
      CausalCohomology.H1
        (S := S₂) (K := K) :=
  QuotientAddGroup.lift
    (CausalCohomology.ExactInClosed
      (S := S₁) (K := K))
    ((CausalCohomology.classOfClosed
        (S := S₂) (K := K)).comp
      E.closedOneFormAddEquiv.toAddMonoidHom)
    (by
      intro ω hω
      apply AddMonoidHom.mem_ker.mpr
      apply
        (CausalCohomology.classOfClosed_eq_zero_iff
          (S := S₂) (K := K)).2
      change
        ((E.closedOneFormAddEquiv ω :
            CausalCohomology.ClosedOneForms
              (S := S₂) (K := K)) :
          CausalOneForm S₂ K) ∈
            CausalCohomology.ExactOneForms
              (S := S₂) (K := K)
      change
        (ω : CausalOneForm S₁ K) ∈
          CausalCohomology.ExactOneForms
            (S := S₁) (K := K) at hω
      exact
        E.closedOneFormAddEquiv_exact ω hω)

/-- Cohomology map on a represented closed form. -/
@[simp] theorem h1Map_classOfClosed
    (ω :
      CausalCohomology.ClosedOneForms
        (S := S₁) (K := K)) :
    E.h1Map
        (CausalCohomology.classOfClosed
          (S := S₁) (K := K) ω)
      =
    CausalCohomology.classOfClosed
      (S := S₂) (K := K)
      (E.closedOneFormAddEquiv ω) := by
  rfl

/-- Forward then inverse map is identity on H1. -/
theorem h1Map_symm_h1Map
    (x :
      CausalCohomology.H1
        (S := S₁) (K := K)) :
    E.symm.h1Map (E.h1Map x) = x := by
  induction x using QuotientAddGroup.induction_on with
  | H ω =>
      rw [E.h1Map_classOfClosed,
        E.symm.h1Map_classOfClosed]
      congr 1
      apply Subtype.ext
      exact E.pullOneForm_symm_pullOneForm
        (ω : CausalOneForm S₁ K)

/-- Inverse then forward map is identity on H1. -/
theorem h1Map_h1Map_symm
    (x :
      CausalCohomology.H1
        (S := S₂) (K := K)) :
    E.h1Map (E.symm.h1Map x) = x := by
  induction x using QuotientAddGroup.induction_on with
  | H ω =>
      rw [E.symm.h1Map_classOfClosed,
        E.h1Map_classOfClosed]
      congr 1
      apply Subtype.ext
      exact E.symm_pullOneForm_pullOneForm
        (ω : CausalOneForm S₂ K)

/-- First causal cohomology is invariant under primitive causal-system
isomorphism. -/
def h1AddEquiv :
    CausalCohomology.H1
        (S := S₁) (K := K) ≃+
      CausalCohomology.H1
        (S := S₂) (K := K) where
  toFun := E.h1Map
  invFun := E.symm.h1Map
  left_inv := E.h1Map_symm_h1Map
  right_inv := E.h1Map_h1Map_symm
  map_add' := by
    intro x y
    exact map_add E.h1Map x y

end EventSystemEquiv
end CausalGeometry
