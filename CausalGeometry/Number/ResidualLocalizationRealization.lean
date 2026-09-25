import CausalGeometry.Number.ResidualAdjunction
import CausalGeometry.Number.ResidualLocalization
import CausalGeometry.Realization.PairedPartialCompatibility

namespace CausalGeometry

universe u

namespace CausalLocalization

open CausalDivisibility

variable {α : Type u}
variable [Monoid α] [PartialOrder α]
variable {S : Submonoid α}

namespace RightFractionCalculus

variable (C : RightFractionCalculus S)

/-- Source inclusion viewed through the generic realization API. -/
def sourceRealization :
    Realization α C.QuotientType where
  toFun := C.sourceHom

@[simp] theorem sourceRealization_apply
    (x : α) :
    C.sourceRealization x =
      C.sourceHom x :=
  rfl

variable (R : ResiduatedMultiplication α)

/-- Canonical partial paired realization for left multiplication/residual.

The target admissible locus is exactly left divisibility by s. -/
def leftResidualRealization
    (s : S) :
    PairedRealizationCompatibilityOn
      C.sourceRealization
      C.sourceRealization
      (R.leftPairedTransform (s : α))
      (C.leftDenominatorPair s)
      (fun z =>
        LeftDivides (s : α) z) where
  forward := by
    intro x
    exact C.leftForward_compat s x
  forward_admissible := by
    intro x
    exact ⟨x, rfl⟩
  backward_on := by
    intro z hz
    exact C.leftBackward_compat_of_divides
      R s z hz

/-- Canonical partial paired realization for right multiplication/residual. -/
def rightResidualRealization
    (s : S) :
    PairedRealizationCompatibilityOn
      C.sourceRealization
      C.sourceRealization
      (R.rightPairedTransform (s : α))
      (C.rightDenominatorPair s)
      (fun z =>
        RightDivides (s : α) z) where
  forward := by
    intro x
    exact C.rightForward_compat s x
  forward_admissible := by
    intro x
    exact ⟨x, rfl⟩
  backward_on := by
    intro z hz
    exact C.rightBackward_compat_of_divides
      R z s hz

/-- Source round trips commute with localization globally, because a freshly
multiplied value is automatically divisible. -/
theorem left_sourceRoundTrip_realizes
    (s : S) (x : α) :
    C.sourceHom
        ((R.leftPairedTransform
          (s : α)).sourceRoundTrip x) =
      (C.leftDenominatorPair s).sourceRoundTrip
        (C.sourceHom x) :=
  (C.leftResidualRealization R s).sourceRoundTrip x

theorem right_sourceRoundTrip_realizes
    (s : S) (x : α) :
    C.sourceHom
        ((R.rightPairedTransform
          (s : α)).sourceRoundTrip x) =
      (C.rightDenominatorPair s).sourceRoundTrip
        (C.sourceHom x) :=
  (C.rightResidualRealization R s).sourceRoundTrip x

/-- Target round trips commute exactly where residual division is exact. -/
theorem left_targetRoundTrip_realizes
    (s : S) (z : α)
    (hz : LeftDivides (s : α) z) :
    C.sourceHom
        ((R.leftPairedTransform
          (s : α)).targetRoundTrip z) =
      (C.leftDenominatorPair s).targetRoundTrip
        (C.sourceHom z) :=
  (C.leftResidualRealization R s).targetRoundTrip
    z hz

theorem right_targetRoundTrip_realizes
    (s : S) (z : α)
    (hz : RightDivides (s : α) z) :
    C.sourceHom
        ((R.rightPairedTransform
          (s : α)).targetRoundTrip z) =
      (C.rightDenominatorPair s).targetRoundTrip
        (C.sourceHom z) :=
  (C.rightResidualRealization R s).targetRoundTrip
    z hz

/-- If source inclusion is faithful, the declared left-divisible target locus
is maximal: backward/Psi compatibility holds at z iff z is left divisible. -/
theorem left_backward_compat_iff_divides
    (hfaith : C.SourceFaithful)
    (s : S) (z : α) :
    C.sourceHom
        ((R.leftPairedTransform
          (s : α)).backward z) =
      (C.leftDenominatorPair s).backward
        (C.sourceHom z) ↔
      LeftDivides (s : α) z := by
  change
    C.sourceHom
        (R.leftResidual (s : α) z) =
      C.denominatorInverse s *
        C.sourceHom z ↔
      LeftDivides (s : α) z
  constructor
  · intro h
    exact
      (C.inverse_mul_source_eq_residual_iff_leftDivides
        R hfaith s z).1 h.symm
  · intro h
    exact
      (C.inverse_mul_source_eq_residual_iff_leftDivides
        R hfaith s z).2 h |>.symm

/-- Right-handed maximality theorem. -/
theorem right_backward_compat_iff_divides
    (hfaith : C.SourceFaithful)
    (s : S) (z : α) :
    C.sourceHom
        ((R.rightPairedTransform
          (s : α)).backward z) =
      (C.rightDenominatorPair s).backward
        (C.sourceHom z) ↔
      RightDivides (s : α) z := by
  change
    C.sourceHom
        (R.rightResidual z (s : α)) =
      C.sourceHom z *
        C.denominatorInverse s ↔
      RightDivides (s : α) z
  constructor
  · intro h
    exact
      (C.source_mul_inverse_eq_residual_iff_rightDivides
        R hfaith z s).1 h.symm
  · intro h
    exact
      (C.source_mul_inverse_eq_residual_iff_rightDivides
        R hfaith z s).2 h |>.symm

end RightFractionCalculus
end CausalLocalization
end CausalGeometry
