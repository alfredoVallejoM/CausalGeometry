import CausalGeometry.Calculus.DependentLinearConnection

namespace CausalGeometry

universe u v w x
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace DependentLinearCausalConnection

variable {K : Type w}
variable {Fiber : Configuration S → Type x}
variable [Ring K]
variable [∀ C, AddCommGroup (Fiber C)]
variable [∀ C, Module K (Fiber C)]

/-- A dependent section of the causal fiber family. -/
abbrev Section :=
  (C : Configuration S) → Fiber C

/-- Covariant finite difference of a dependent section.

The result lives in the target fiber; no identification of source and target
fibers is required. -/
def covariantDifference
    (∇ : DependentLinearCausalConnection K S Fiber)
    (F : Section (S := S) (Fiber := Fiber))
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    Fiber (S.extend C e h) :=
  F (S.extend C e h) -
    ∇.transport C e h (F C)

/-- A section is parallel along one enabled event exactly when its covariant
finite difference vanishes there. -/
def ParallelAt
    (∇ : DependentLinearCausalConnection K S Fiber)
    (F : Section (S := S) (Fiber := Fiber))
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) : Prop :=
  F (S.extend C e h) =
    ∇.transport C e h (F C)

theorem covariantDifference_eq_zero_iff
    (∇ : DependentLinearCausalConnection K S Fiber)
    (F : Section (S := S) (Fiber := Fiber))
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    ∇.covariantDifference F C e h = 0 ↔
      ∇.ParallelAt F C e h := by
  unfold covariantDifference ParallelAt
  exact sub_eq_zero

/-- Dependent curvature at one vector, expressed in the f-then-e endpoint
fiber. The e-then-f result is cast across endpoint equality before
subtraction. -/
def curvatureAt
    (∇ : DependentLinearCausalConnection K S Fiber)
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f)
    (x : Fiber C) :
    Fiber d.afterFE :=
  cast
      (congrArg Fiber
        (ConcurrencyDiamond.endpoint_eq d))
      (∇.transportEF d x) -
    ∇.transportFE d x

/-- Flatness is exactly pointwise vanishing of dependent curvature. -/
theorem flatOn_iff_curvatureAt_eq_zero
    (∇ : DependentLinearCausalConnection K S Fiber)
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    ∇.FlatOn d ↔
      ∀ x, ∇.curvatureAt d x = 0 := by
  constructor
  · intro h x
    unfold curvatureAt
    rw [h x]
    simp
  · intro h x
    have hx := h x
    unfold curvatureAt at hx
    exact sub_eq_zero.mp hx

/-- Covariant square defect along the e-then-f route. -/
def squareDefectEF
    (∇ : DependentLinearCausalConnection K S Fiber)
    (F : Section (S := S) (Fiber := Fiber))
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    Fiber d.afterEF :=
  F d.afterEF -
    ∇.transportEF d (F C)

/-- Covariant square defect along the f-then-e route. -/
def squareDefectFE
    (∇ : DependentLinearCausalConnection K S Fiber)
    (F : Section (S := S) (Fiber := Fiber))
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    Fiber d.afterFE :=
  F d.afterFE -
    ∇.transportFE d (F C)

/-- After identifying the two endpoint fibers, the discrepancy between the
two square defects is precisely negative dependent curvature on the starting
section value. -/
theorem squareDefect_difference_eq_neg_curvature
    (∇ : DependentLinearCausalConnection K S Fiber)
    (F : Section (S := S) (Fiber := Fiber))
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    cast
        (congrArg Fiber
          (ConcurrencyDiamond.endpoint_eq d))
        (∇.squareDefectEF F d) -
      ∇.squareDefectFE F d =
        - ∇.curvatureAt d (F C) := by
  have hEq :
      d.afterEF = d.afterFE :=
    ConcurrencyDiamond.endpoint_eq d
  cases hEq
  unfold squareDefectEF squareDefectFE curvatureAt
  simp
  abel

end DependentLinearCausalConnection
end CausalGeometry
