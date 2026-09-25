import CausalGeometry.Foundation.PairedTransform
import CausalGeometry.Number.LeftFractionCalculus
import CausalGeometry.Number.Residual
import CausalGeometry.Number.RightFractionCalculus

namespace CausalGeometry

universe u

namespace CausalLocalization

variable {α : Type u}
variable [Monoid α] [PartialOrder α]
variable {S : Submonoid α}

/-- Left multiplication by a selected denominator and multiplication by its
certified inverse form an actual paired equivalence inside any right fraction
calculus. -/
def RightFractionCalculus.leftDenominatorPair
    (C : RightFractionCalculus S)
    (s : S) :
    PairedTransform C.QuotientType C.QuotientType where
  forward := fun x =>
    C.sourceHom (s : α) * x
  backward := fun x =>
    C.denominatorInverse s * x

@[simp] theorem RightFractionCalculus.leftDenominatorPair_sourceRoundTrip
    (C : RightFractionCalculus S)
    (s : S)
    (x : C.QuotientType) :
    (C.leftDenominatorPair s).sourceRoundTrip x =
      x := by
  simp [PairedTransform.sourceRoundTrip,
    RightFractionCalculus.leftDenominatorPair,
    mul_assoc]

@[simp] theorem RightFractionCalculus.leftDenominatorPair_targetRoundTrip
    (C : RightFractionCalculus S)
    (s : S)
    (x : C.QuotientType) :
    (C.leftDenominatorPair s).targetRoundTrip x =
      x := by
  simp [PairedTransform.targetRoundTrip,
    RightFractionCalculus.leftDenominatorPair,
    mul_assoc]

/-- Right multiplication by a denominator and its inverse gives the analogous
paired equivalence for right residuals. -/
def RightFractionCalculus.rightDenominatorPair
    (C : RightFractionCalculus S)
    (s : S) :
    PairedTransform C.QuotientType C.QuotientType where
  forward := fun x =>
    x * C.sourceHom (s : α)
  backward := fun x =>
    x * C.denominatorInverse s

@[simp] theorem RightFractionCalculus.rightDenominatorPair_sourceRoundTrip
    (C : RightFractionCalculus S)
    (s : S)
    (x : C.QuotientType) :
    (C.rightDenominatorPair s).sourceRoundTrip x =
      x := by
  simp [PairedTransform.sourceRoundTrip,
    RightFractionCalculus.rightDenominatorPair,
    mul_assoc]

@[simp] theorem RightFractionCalculus.rightDenominatorPair_targetRoundTrip
    (C : RightFractionCalculus S)
    (s : S)
    (x : C.QuotientType) :
    (C.rightDenominatorPair s).targetRoundTrip x =
      x := by
  simp [PairedTransform.targetRoundTrip,
    RightFractionCalculus.rightDenominatorPair,
    mul_assoc]

namespace RightFractionCalculus

variable
    (C : RightFractionCalculus S)
    (R : ResiduatedMultiplication α)

/-- Exact left residual division is realized by multiplying by the inverse
denominator in the localization. -/
theorem exactLeftDivision_localizes
    (s : S) (z : α)
    (h :
      R.ExactLeftDivision (s : α) z) :
    C.denominatorInverse s *
        C.sourceHom z =
      C.sourceHom
        (R.leftResidual (s : α) z) := by
  rw [← h, map_mul, ← mul_assoc,
    C.inverse_mul_denominator, one_mul]

/-- Divisibility is sufficient because residuation saturates exactly on the
left-divisible locus. -/
theorem leftDivides_localizes
    (s : S) (z : α)
    (h :
      CausalDivisibility.LeftDivides
        (s : α) z) :
    C.denominatorInverse s *
        C.sourceHom z =
      C.sourceHom
        (R.leftResidual (s : α) z) :=
  C.exactLeftDivision_localizes R s z
    ((R.exactLeftDivision_iff_leftDivides
      (s : α) z).2 h)

/-- Exact right residual division is realized by multiplying by the inverse
denominator on the right. -/
theorem exactRightDivision_localizes
    (z : α) (s : S)
    (h :
      R.ExactRightDivision z (s : α)) :
    C.sourceHom z *
        C.denominatorInverse s =
      C.sourceHom
        (R.rightResidual z (s : α)) := by
  rw [← h, map_mul, mul_assoc,
    C.denominator_mul_inverse, mul_one]

theorem rightDivides_localizes
    (z : α) (s : S)
    (h :
      CausalDivisibility.RightDivides
        (s : α) z) :
    C.sourceHom z *
        C.denominatorInverse s =
      C.sourceHom
        (R.rightResidual z (s : α)) :=
  C.exactRightDivision_localizes R z s
    ((R.exactRightDivision_iff_rightDivides
      z (s : α)).2 h)

/-- Multiplication by s always commutes with the source embedding. -/
theorem leftForward_compat
    (s : S) (x : α) :
    C.sourceHom ((s : α) * x) =
      (C.leftDenominatorPair s).forward
        (C.sourceHom x) := by
  simp [RightFractionCalculus.leftDenominatorPair]

/-- The residual/backward square commutes exactly on the left-divisible
domain. Outside that domain the residual remains an order-theoretic
approximation and no localization equality is claimed. -/
theorem leftBackward_compat_of_divides
    (s : S) (z : α)
    (h :
      CausalDivisibility.LeftDivides
        (s : α) z) :
    C.sourceHom
        (R.leftResidual (s : α) z) =
      (C.leftDenominatorPair s).backward
        (C.sourceHom z) := by
  exact (C.leftDivides_localizes R s z h).symm

theorem rightForward_compat
    (s : S) (x : α) :
    C.sourceHom (x * (s : α)) =
      (C.rightDenominatorPair s).forward
        (C.sourceHom x) := by
  simp [RightFractionCalculus.rightDenominatorPair]

theorem rightBackward_compat_of_divides
    (z : α) (s : S)
    (h :
      CausalDivisibility.RightDivides
        (s : α) z) :
    C.sourceHom
        (R.rightResidual z (s : α)) =
      (C.rightDenominatorPair s).backward
        (C.sourceHom z) := by
  exact (C.rightDivides_localizes R z s h).symm

end RightFractionCalculus

/-- The source embedding of a fraction calculus is faithful when localization
has not identified distinct source elements. -/
def RightFractionCalculus.SourceFaithful
    (C : RightFractionCalculus S) : Prop :=
  Function.Injective C.sourceHom

namespace RightFractionCalculus

variable
    (C : RightFractionCalculus S)
    (R : ResiduatedMultiplication α)

/-- Under a faithful source embedding, localization equality with inverse
transport characterizes exact left residual division. -/
theorem inverse_mul_source_eq_residual_iff_exactLeft
    (hfaith : C.SourceFaithful)
    (s : S) (z : α) :
    C.denominatorInverse s *
          C.sourceHom z =
        C.sourceHom
          (R.leftResidual (s : α) z) ↔
      R.ExactLeftDivision (s : α) z := by
  constructor
  · intro hloc
    unfold ResiduatedMultiplication.ExactLeftDivision
    apply hfaith
    rw [map_mul]
    calc
      C.sourceHom (s : α) *
          C.sourceHom
            (R.leftResidual (s : α) z)
          =
        C.sourceHom (s : α) *
          (C.denominatorInverse s *
            C.sourceHom z) := by
              rw [hloc]
      _ =
        (C.sourceHom (s : α) *
          C.denominatorInverse s) *
            C.sourceHom z := by
              rw [mul_assoc]
      _ = C.sourceHom z := by
        rw [C.denominator_mul_inverse, one_mul]
  · intro h
    exact C.exactLeftDivision_localizes R s z h

/-- Hence inverse transport agrees with the left residual exactly on the
left-divisible locus. -/
theorem inverse_mul_source_eq_residual_iff_leftDivides
    (hfaith : C.SourceFaithful)
    (s : S) (z : α) :
    C.denominatorInverse s *
          C.sourceHom z =
        C.sourceHom
          (R.leftResidual (s : α) z) ↔
      CausalDivisibility.LeftDivides
        (s : α) z := by
  rw [C.inverse_mul_source_eq_residual_iff_exactLeft
    R hfaith s z,
    R.exactLeftDivision_iff_leftDivides]

/-- Symmetric characterization for right residual division. -/
theorem source_mul_inverse_eq_residual_iff_exactRight
    (hfaith : C.SourceFaithful)
    (z : α) (s : S) :
    C.sourceHom z *
          C.denominatorInverse s =
        C.sourceHom
          (R.rightResidual z (s : α)) ↔
      R.ExactRightDivision z (s : α) := by
  constructor
  · intro hloc
    unfold ResiduatedMultiplication.ExactRightDivision
    apply hfaith
    rw [map_mul]
    calc
      C.sourceHom
          (R.rightResidual z (s : α)) *
          C.sourceHom (s : α)
          =
        (C.sourceHom z *
          C.denominatorInverse s) *
            C.sourceHom (s : α) := by
              rw [hloc]
      _ =
        C.sourceHom z *
          (C.denominatorInverse s *
            C.sourceHom (s : α)) := by
              rw [mul_assoc]
      _ = C.sourceHom z := by
        rw [C.inverse_mul_denominator, mul_one]
  · intro h
    exact C.exactRightDivision_localizes R z s h

theorem source_mul_inverse_eq_residual_iff_rightDivides
    (hfaith : C.SourceFaithful)
    (z : α) (s : S) :
    C.sourceHom z *
          C.denominatorInverse s =
        C.sourceHom
          (R.rightResidual z (s : α)) ↔
      CausalDivisibility.RightDivides
        (s : α) z := by
  rw [C.source_mul_inverse_eq_residual_iff_exactRight
    R hfaith z s,
    R.exactRightDivision_iff_rightDivides]

end RightFractionCalculus

/-- The same exact residual/localization comparison holds for a certified left
fraction calculus. -/
namespace LeftFractionCalculus

variable
    (C : LeftFractionCalculus S)
    (R : ResiduatedMultiplication α)

theorem exactLeftDivision_localizes
    (s : S) (z : α)
    (h :
      R.ExactLeftDivision (s : α) z) :
    C.denominatorInverse s *
        C.sourceHom z =
      C.sourceHom
        (R.leftResidual (s : α) z) := by
  rw [← h, map_mul, ← mul_assoc,
    C.inverse_mul_denominator, one_mul]

theorem exactRightDivision_localizes
    (z : α) (s : S)
    (h :
      R.ExactRightDivision z (s : α)) :
    C.sourceHom z *
        C.denominatorInverse s =
      C.sourceHom
        (R.rightResidual z (s : α)) := by
  rw [← h, map_mul, mul_assoc,
    C.denominator_mul_inverse, mul_one]

end LeftFractionCalculus
end CausalLocalization
end CausalGeometry
