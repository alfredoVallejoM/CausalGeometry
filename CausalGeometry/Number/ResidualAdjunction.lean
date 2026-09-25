import CausalGeometry.Foundation.AdjunctionBridge
import CausalGeometry.Number.Residual

namespace CausalGeometry

universe u

namespace ResiduatedMultiplication

open CausalDivisibility

variable {α : Type u}
variable [PartialOrder α] [Mul α]
variable (R : ResiduatedMultiplication α)

/-- Structural pair carried by left multiplication and its left residual.

This is the arithmetic realization of the foundational Phi/Psi pattern. -/
def leftPairedTransform
    (x : α) :
    PairedTransform α α :=
  (R.leftExtensionRestriction x).toPaired

/-- Structural pair carried by right multiplication and its right residual. -/
def rightPairedTransform
    (x : α) :
    PairedTransform α α :=
  (R.rightExtensionRestriction x).toPaired

@[simp] theorem leftPaired_forward
    (x y : α) :
    (R.leftPairedTransform x).forward y =
      x * y :=
  rfl

@[simp] theorem leftPaired_backward
    (x z : α) :
    (R.leftPairedTransform x).backward z =
      R.leftResidual x z :=
  rfl

@[simp] theorem rightPaired_forward
    (x y : α) :
    (R.rightPairedTransform x).forward y =
      y * x :=
  rfl

@[simp] theorem rightPaired_backward
    (x z : α) :
    (R.rightPairedTransform x).backward z =
      R.rightResidual z x :=
  rfl

/-- Residuation proves an optional adjunction bridge for the structural pair;
adjunction is derived arithmetic structure, not part of PairedTransform. -/
def leftAdjointBridge
    (x : α) :
    AdjointBridge
      (R.leftPairedTransform x) :=
  (R.leftExtensionRestriction x).toAdjointBridge

def rightAdjointBridge
    (x : α) :
    AdjointBridge
      (R.rightPairedTransform x) :=
  (R.rightExtensionRestriction x).toAdjointBridge

theorem leftAdjunction
    (x y z : α) :
    (R.leftPairedTransform x).forward y ≤ z ↔
      y ≤
        (R.leftPairedTransform x).backward z :=
  (R.leftAdjointBridge x).adjunction y z

theorem rightAdjunction
    (x y z : α) :
    (R.rightPairedTransform x).forward y ≤ z ↔
      y ≤
        (R.rightPairedTransform x).backward z :=
  (R.rightAdjointBridge x).adjunction y z

/-- The source round trip Psi(Phi(y)) is exactly the correlative closure. -/
@[simp] theorem left_sourceRoundTrip_eq_closure
    (x y : α) :
    (R.leftPairedTransform x).sourceRoundTrip y =
      (R.leftExtensionRestriction x).closure y :=
  rfl

@[simp] theorem right_sourceRoundTrip_eq_closure
    (x y : α) :
    (R.rightPairedTransform x).sourceRoundTrip y =
      (R.rightExtensionRestriction x).closure y :=
  rfl

/-- The target round trip Phi(Psi(z)) is exactly the realizable interior. -/
@[simp] theorem left_targetRoundTrip_eq_interior
    (x z : α) :
    (R.leftPairedTransform x).targetRoundTrip z =
      (R.leftExtensionRestriction x).interior z :=
  rfl

@[simp] theorem right_targetRoundTrip_eq_interior
    (x z : α) :
    (R.rightPairedTransform x).targetRoundTrip z =
      (R.rightExtensionRestriction x).interior z :=
  rfl

/-- Source closure is extensive. -/
theorem left_sourceRoundTrip_extensive
    (x y : α) :
    y ≤
      (R.leftPairedTransform x).sourceRoundTrip y :=
  R.leftUnit x y

theorem right_sourceRoundTrip_extensive
    (x y : α) :
    y ≤
      (R.rightPairedTransform x).sourceRoundTrip y :=
  R.rightUnit x y

/-- Target round trip is reductive. -/
theorem left_targetRoundTrip_reductive
    (x z : α) :
    (R.leftPairedTransform x).targetRoundTrip z ≤ z :=
  R.leftCounit x z

theorem right_targetRoundTrip_reductive
    (x z : α) :
    (R.rightPairedTransform x).targetRoundTrip z ≤ z :=
  R.rightCounit z x

/-- A target is fixed by the left Phi/Psi round trip exactly when it is left
divisible by the chosen multiplier. -/
theorem left_targetFixed_iff_leftDivides
    (x z : α) :
    (R.leftPairedTransform x).TargetFixed z ↔
      LeftDivides x z := by
  change
    x * R.leftResidual x z = z ↔
      LeftDivides x z
  exact R.exactLeftDivision_iff_leftDivides
    x z

/-- Right-handed analogue. -/
theorem right_targetFixed_iff_rightDivides
    (x z : α) :
    (R.rightPairedTransform x).TargetFixed z ↔
      RightDivides x z := by
  change
    R.rightResidual z x * x = z ↔
      RightDivides x z
  exact R.exactRightDivision_iff_rightDivides
    z x

/-- Under cancellative multiplication, residual restriction loses no
information on values that were just extended: Psi(Phi(y))=y. -/
theorem left_sourceRoundTrip_eq_self_of_cancel
    [CancelMonoid α]
    (x y : α) :
    (R.leftPairedTransform x).sourceRoundTrip y =
      y := by
  apply mul_left_cancel x
  change
    x * R.leftResidual x (x * y) =
      x * y
  exact
    (R.exactLeftDivision_iff_leftDivides
      x (x * y)).2
      ⟨y, rfl⟩

theorem right_sourceRoundTrip_eq_self_of_cancel
    [CancelMonoid α]
    (x y : α) :
    (R.rightPairedTransform x).sourceRoundTrip y =
      y := by
  apply mul_right_cancel x
  change
    R.rightResidual (y * x) x * x =
      y * x
  exact
    (R.exactRightDivision_iff_rightDivides
      (y * x) x).2
      ⟨y, rfl⟩

/-- With cancellation, the residual pairs are source-side fixed everywhere,
while target fixed points remain precisely the divisible elements. -/
theorem left_sourceFixed_of_cancel
    [CancelMonoid α]
    (x y : α) :
    (R.leftPairedTransform x).SourceFixed y :=
  R.left_sourceRoundTrip_eq_self_of_cancel
    x y

theorem right_sourceFixed_of_cancel
    [CancelMonoid α]
    (x y : α) :
    (R.rightPairedTransform x).SourceFixed y :=
  R.right_sourceRoundTrip_eq_self_of_cancel
    x y

end ResiduatedMultiplication
end CausalGeometry
