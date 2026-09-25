import CausalGeometry.Calculus.ExteriorComplex
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace CausalGeometry

universe u v w
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalCohomology

variable {K : Type w}

/-- Causal one-forms are just dependent functions once proof fields are
forgotten, so their additive structure is transported pointwise. -/
def oneFormEquivFun :
    CausalOneForm S K ≃
      ((C : Configuration S) →
        EventDirection S C → K) where
  toFun := CausalOneForm.value
  invFun := fun f => ⟨f⟩
  left_inv := by
    intro ω
    cases ω
    rfl
  right_inv := by
    intro f
    rfl

instance [AddCommGroup K] :
    AddCommGroup (CausalOneForm S K) :=
  (oneFormEquivFun (S := S) (K := K)).addCommGroup

@[simp] theorem zero_value
    [AddCommGroup K]
    (C : Configuration S)
    (d : EventDirection S C) :
    (0 : CausalOneForm S K).value C d = 0 := by
  rfl

@[simp] theorem add_value
    [AddCommGroup K]
    (ω η : CausalOneForm S K)
    (C : Configuration S)
    (d : EventDirection S C) :
    (ω + η).value C d =
      ω.value C d + η.value C d := by
  rfl

@[simp] theorem neg_value
    [AddCommGroup K]
    (ω : CausalOneForm S K)
    (C : Configuration S)
    (d : EventDirection S C) :
    (-ω).value C d =
      -ω.value C d := by
  rfl

/-- Raw degree-two cochains. Antisymmetry is not required in the codomain of
the differential; the actual exterior derivative lands in the antisymmetric
subspace by the separate theorem already proved. -/
abbrev RawTwoCochain
    (S : EventSystem Event Label)
    (K : Type w) :=
  (C : Configuration S) →
    (e f : Event) →
      ConcurrencyDiamond C e f → K

variable [AddCommGroup K]

/-- Degree-zero to degree-one causal exterior differential. -/
def d0 :
    (Configuration S → K) →+
      CausalOneForm S K where
  toFun := CausalOneForm.exact
  map_zero' := by
    apply CausalOneForm.ext
    intro C d
    simp [CausalOneForm.exact,
      causalDifference]
  map_add' := by
    intro F G
    apply CausalOneForm.ext
    intro C d
    simp [CausalOneForm.exact,
      causalDifference]
    abel

/-- Degree-one to raw degree-two exterior differential. -/
def d1 :
    CausalOneForm S K →+
      RawTwoCochain S K where
  toFun := fun ω C e f d =>
    CausalOneForm.exteriorDerivative ω d
  map_zero' := by
    funext C e f d
    simp [
      CausalOneForm.exteriorDerivative,
      CausalOneForm.variationEF,
      CausalOneForm.variationFE
    ]
  map_add' := by
    intro ω η
    funext C e f d
    simp [
      CausalOneForm.exteriorDerivative,
      CausalOneForm.variationEF,
      CausalOneForm.variationFE
    ]
    abel

/-- Algebraic d1∘d0=0. -/
theorem d1_d0
    (F : Configuration S → K) :
    d1 (S := S) (K := K)
        (d0 (S := S) (K := K) F) =
      0 := by
  funext C e f d
  exact
    CausalOneForm.exact_closed F d

/-- Closed causal one-forms. -/
def ClosedOneForms :
    AddSubgroup (CausalOneForm S K) :=
  (d1 (S := S) (K := K)).ker

/-- Exact causal one-forms. -/
def ExactOneForms :
    AddSubgroup (CausalOneForm S K) :=
  (d0 (S := S) (K := K)).range

theorem mem_ClosedOneForms_iff
    (ω : CausalOneForm S K) :
    ω ∈ ClosedOneForms (S := S) (K := K) ↔
      ω.Closed := by
  constructor
  · intro h C e f d
    have hzero :=
      AddMonoidHom.mem_ker.mp h
    have hv :=
      congrFun
        (congrFun
          (congrFun
            (congrFun hzero C) e) f) d
    exact hv
  · intro h
    apply AddMonoidHom.mem_ker.mpr
    funext C e f d
    exact h d

theorem exact_le_closed :
    ExactOneForms (S := S) (K := K) ≤
      ClosedOneForms (S := S) (K := K) := by
  intro ω hω
  rcases hω with ⟨F, rfl⟩
  apply AddMonoidHom.mem_ker.mpr
  exact d1_d0 (S := S) (K := K) F

/-- Exact subgroup seen inside the closed subgroup. -/
def ExactInClosed :
    AddSubgroup
      (ClosedOneForms (S := S) (K := K)) :=
  (ExactOneForms (S := S) (K := K)).comap
    (ClosedOneForms (S := S) (K := K)).subtype

/-- First causal cohomology group. -/
abbrev H1 :=
  QuotientAddGroup.quotient
    (ExactInClosed (S := S) (K := K))

/-- Canonical cohomology class of a closed one-form. -/
def classOfClosed :
    ClosedOneForms (S := S) (K := K) →+
      H1 (S := S) (K := K) :=
  QuotientAddGroup.mk'
    (ExactInClosed (S := S) (K := K))

/-- A closed form represents zero in H1 exactly when it is exact. -/
theorem classOfClosed_eq_zero_iff
    (ω :
      ClosedOneForms (S := S) (K := K)) :
    classOfClosed (S := S) (K := K) ω = 0 ↔
      (ω : CausalOneForm S K) ∈
        ExactOneForms (S := S) (K := K) := by
  rw [QuotientAddGroup.eq_zero_iff]
  rfl

/-- Every potential has the trivial H1 class. -/
theorem exact_class_zero
    (F : Configuration S → K) :
    classOfClosed
        (S := S) (K := K)
        ⟨d0 (S := S) (K := K) F,
          exact_le_closed
            (S := S) (K := K)
            ⟨F, rfl⟩⟩ =
      0 := by
  apply
    (classOfClosed_eq_zero_iff
      (S := S) (K := K)).2
  exact ⟨F, rfl⟩

end CausalCohomology
end CausalGeometry
