import CausalGeometry.Calculus.Cohomology
import CausalGeometry.Calculus.HodgeComplex
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Tactic

namespace CausalGeometry

universe u v w
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalCohomology

variable {K : Type w}

/-- Additive equivalence between causal one-forms and their underlying
dependent function space. -/
def oneFormAddEquivFun
    [AddCommGroup K] :
    CausalOneForm S K ≃+
      ((C : Configuration S) →
        EventDirection S C → K) where
  toEquiv :=
    oneFormEquivFun
  map_add' := by
    intro ω η
    rfl

/-- Scalar module structure on causal one-forms, transported pointwise from
the underlying dependent function space. -/
instance [Field K] :
    Module K (CausalOneForm S K) :=
  (oneFormAddEquivFun
    (S := S) (K := K)).module K

@[simp] theorem smul_oneForm_value
    [Field K]
    (a : K)
    (ω : CausalOneForm S K)
    (C : Configuration S)
    (d : EventDirection S C) :
    (a • ω).value C d =
      a • ω.value C d := by
  rfl

variable [Field K]

/-- Linear degree-zero differential of the concrete event/configuration
complex. -/
def d0Linear :
    (Configuration S → K) →ₗ[K]
      CausalOneForm S K where
  toFun :=
    CausalOneForm.exact
  map_add' := by
    intro F G
    exact
      (d0 (S := S) (K := K)).map_add F G
  map_smul' := by
    intro a F
    apply CausalOneForm.ext
    intro C d
    simp [
      CausalOneForm.exact,
      causalDifference
    ]

/-- Linear degree-one differential into raw concurrency-diamond cochains. -/
def d1Linear :
    CausalOneForm S K →ₗ[K]
      RawTwoCochain S K where
  toFun := fun ω C e f d =>
    CausalOneForm.exteriorDerivative ω d
  map_add' := by
    intro ω η
    exact
      (d1 (S := S) (K := K)).map_add ω η
  map_smul' := by
    intro a ω
    funext C e f d
    simp [
      CausalOneForm.exteriorDerivative,
      CausalOneForm.variationEF,
      CausalOneForm.variationFE
    ]
    module

@[simp] theorem d0Linear_apply
    (F : Configuration S → K) :
    d0Linear (S := S) (K := K) F =
      CausalOneForm.exact F :=
  rfl

@[simp] theorem d1Linear_apply
    (ω : CausalOneForm S K)
    (C : Configuration S)
    (e f : Event)
    (d : ConcurrencyDiamond C e f) :
    d1Linear (S := S) (K := K) ω
        C e f d =
      CausalOneForm.exteriorDerivative ω d :=
  rfl

/-- Canonical three-term linear cochain complex extracted directly from one
primitive causal event system. -/
def eventCochainComplex :
    CausalCochainComplex
      K
      (Configuration S → K)
      (CausalOneForm S K)
      (RawTwoCochain S K) where
  d0 :=
    d0Linear
  d1 :=
    d1Linear
  d_sq := by
    apply LinearMap.ext
    intro F
    funext C e f d
    exact
      CausalOneForm.exact_closed F d

/-- Abstract-linear closedness is exactly the previously defined causal
closedness of one-forms. -/
theorem mem_eventClosed1_iff
    (ω : CausalOneForm S K) :
    ω ∈
        (eventCochainComplex
          (S := S) (K := K)).Closed1
      ↔
    ω.Closed := by
  change
    d1Linear (S := S) (K := K) ω = 0 ↔
      ω.Closed
  constructor
  · intro h C e f d
    have hv :=
      congrFun
        (congrFun
          (congrFun
            (congrFun h C) e) f) d
    exact hv
  · intro h
    funext C e f d
    exact h d

/-- Abstract-linear exactness is exactly the existing causal exactness
predicate. -/
theorem mem_eventExact1_iff
    (ω : CausalOneForm S K) :
    ω ∈
        (eventCochainComplex
          (S := S) (K := K)).Exact1
      ↔
    ω ∈ ExactOneForms
      (S := S) (K := K) := by
  constructor
  · rintro ⟨F, hF⟩
    exact ⟨F, hF⟩
  · rintro ⟨F, hF⟩
    exact ⟨F, hF⟩

/-- Closed one-forms in the abstract linear complex identify canonically with
the already established closed causal one-forms. -/
def eventClosed1AddEquiv :
    (eventCochainComplex
      (S := S) (K := K)).Closed1 ≃+
      ClosedOneForms (S := S) (K := K) where
  toFun := fun ω =>
    ⟨ω.1,
      (mem_ClosedOneForms_iff
        (S := S) (K := K) ω.1).2
        ((mem_eventClosed1_iff
          (S := S) (K := K) ω.1).1 ω.2)⟩
  invFun := fun ω =>
    ⟨ω.1,
      (mem_eventClosed1_iff
        (S := S) (K := K) ω.1).2
        ((mem_ClosedOneForms_iff
          (S := S) (K := K) ω.1).1 ω.2)⟩
  left_inv := by
    intro ω
    apply Subtype.ext
    rfl
  right_inv := by
    intro ω
    apply Subtype.ext
    rfl
  map_add' := by
    intro ω η
    apply Subtype.ext
    rfl

end CausalCohomology

/-- Hodge data specialized to the concrete event/configuration causal
cochain complex. -/
abbrev CausalEventHodgeData
    {Event : Type u} {Label : Type v}
    (S : EventSystem Event Label)
    (K : Type w)
    [Field K] :=
  CausalHodgeData
    (CausalCohomology.eventCochainComplex
      (S := S) (K := K))

/-- Hodge representation hypotheses specialized to the concrete causal
complex. -/
abbrev CausalEventHodgeRepresentation
    {Event : Type u} {Label : Type v}
    {S : EventSystem Event Label}
    {K : Type w}
    [Field K]
    (H : CausalEventHodgeData S K) :=
  CausalHodgeRepresentation H

namespace CausalEventHodgeRepresentation

variable {K : Type w} [Field K]
variable
    {H : CausalEventHodgeData S K}
    (R : CausalEventHodgeRepresentation H)

/-- A harmonic one-cochain gives an actual closed causal one-form. -/
def harmonicToCausalClosed :
    H.Harmonic1 →+
      CausalCohomology.ClosedOneForms
        (S := S) (K := K) where
  toFun := fun h =>
    CausalCohomology.eventClosed1AddEquiv
      (R.harmonicToClosed h)
  map_zero' := by
    rfl
  map_add' := by
    intro x y
    rfl

/-- Canonical map from harmonic one-cochains into the already established
causal H1 quotient. -/
def harmonicToCausalH1 :
    H.Harmonic1 →+
      CausalCohomology.H1
        (S := S) (K := K) :=
  (CausalCohomology.classOfClosed
    (S := S) (K := K)).comp
      R.harmonicToCausalClosed

/-- Harmonic representatives are injective in concrete causal H1. -/
theorem harmonicToCausalH1_injective :
    Function.Injective
      R.harmonicToCausalH1 := by
  intro x y hxy
  have hzero :
      R.harmonicToCausalH1 (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]

  have hexactCausal :
      ((x - y : H.Harmonic1) :
        CausalOneForm S K) ∈
      CausalCohomology.ExactOneForms
        (S := S) (K := K) := by
    apply
      (CausalCohomology.classOfClosed_eq_zero_iff
        (S := S) (K := K)).1
    exact hzero

  have hexactLinear :
      ((x - y : H.Harmonic1) :
        CausalOneForm S K) ∈
      (CausalCohomology.eventCochainComplex
        (S := S) (K := K)).Exact1 :=
    (CausalCohomology.mem_eventExact1_iff
      (S := S) (K := K) _).2
      hexactCausal

  have hharm :
      ((x - y : H.Harmonic1) :
        CausalOneForm S K) ∈
      H.Harmonic1 :=
    (x - y).2

  have hz :
      ((x - y : H.Harmonic1) :
        CausalOneForm S K) = 0 :=
    (Submodule.disjoint_def.mp
      R.exact_harmonic_disjoint)
      _
      hexactLinear hharm

  apply sub_eq_zero.mp
  apply Subtype.ext
  exact hz

/-- Every concrete causal H1 class has a harmonic representative whenever the
Hodge representation hypotheses hold. -/
theorem harmonicToCausalH1_surjective :
    Function.Surjective
      R.harmonicToCausalH1 := by
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H z =>
      let zLin :
          (CausalCohomology.eventCochainComplex
            (S := S) (K := K)).Closed1 :=
        (CausalCohomology.eventClosed1AddEquiv
          (S := S) (K := K)).symm z

      rcases R.closed_decompose zLin with
        ⟨e, h, hdecomp⟩

      refine ⟨h, ?_⟩
      apply sub_eq_zero.mp
      rw [← map_sub]

      apply
        (CausalCohomology.classOfClosed_eq_zero_iff
          (S := S) (K := K)).2

      have he :
          (e : CausalOneForm S K) ∈
            CausalCohomology.ExactOneForms
              (S := S) (K := K) :=
        (CausalCohomology.mem_eventExact1_iff
          (S := S) (K := K) e).1 e.2

      have hdiff :
          ((h : H.Harmonic1) :
              CausalOneForm S K) -
            (z : CausalOneForm S K) =
          - (e : CausalOneForm S K) := by
        change
          ((h : H.Harmonic1) :
              CausalOneForm S K) -
            (zLin : CausalOneForm S K) =
          - (e : CausalOneForm S K)
        rw [hdecomp]
        abel

      change
        ((h : H.Harmonic1) :
            CausalOneForm S K) -
          (z : CausalOneForm S K) ∈
        CausalCohomology.ExactOneForms
          (S := S) (K := K)
      rw [hdiff]
      exact
        (CausalCohomology.ExactOneForms
          (S := S) (K := K)).neg_mem he

/-- Concrete causal Hodge theorem: harmonic degree-one cochains are additively
equivalent to the original event-based causal H1. -/
noncomputable def harmonicAddEquivCausalH1 :
    H.Harmonic1 ≃+
      CausalCohomology.H1
        (S := S) (K := K) :=
  AddEquiv.ofBijective
    R.harmonicToCausalH1
    ⟨R.harmonicToCausalH1_injective,
      R.harmonicToCausalH1_surjective⟩

/-- Vanishing of concrete causal H1 is equivalent to triviality of the
harmonic subspace. -/
theorem causalH1_subsingleton_iff_harmonic1 :
    Subsingleton
        (CausalCohomology.H1
          (S := S) (K := K))
      ↔
    Subsingleton H.Harmonic1 := by
  exact
    R.harmonicAddEquivCausalH1.toEquiv
      .subsingleton_congr.symm

end CausalEventHodgeRepresentation
end CausalGeometry
