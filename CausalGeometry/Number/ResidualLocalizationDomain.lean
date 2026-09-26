import CausalGeometry.Number.ResidualLocalization

namespace CausalGeometry

universe u

namespace CausalLocalization
namespace RightFractionCalculus

variable {α : Type u}
variable [Monoid α] [PartialOrder α]
variable {S : Submonoid α}

variable
    (C : RightFractionCalculus S)
    (R : ResiduatedMultiplication α)

/-- Exact source domain on which left residual restriction is represented by
inverse denominator transport in a faithful localization. -/
def LeftResidualLocalizationDomain
    (s : S) : Set α :=
  {z |
    CausalDivisibility.LeftDivides
      (s : α) z}

/-- Exact source domain on which right residual restriction is represented by
right inverse denominator transport. -/
def RightResidualLocalizationDomain
    (s : S) : Set α :=
  {z |
    CausalDivisibility.RightDivides
      (s : α) z}

@[simp] theorem mem_leftResidualLocalizationDomain
    (s : S) (z : α) :
    z ∈ C.LeftResidualLocalizationDomain R s ↔
      CausalDivisibility.LeftDivides
        (s : α) z :=
  Iff.rfl

@[simp] theorem mem_rightResidualLocalizationDomain
    (s : S) (z : α) :
    z ∈ C.RightResidualLocalizationDomain R s ↔
      CausalDivisibility.RightDivides
        (s : α) z :=
  Iff.rfl

/-- Faithfulness identifies the left localization-equality locus exactly with
the intrinsic source divisibility domain. -/
theorem mem_leftResidualLocalizationDomain_iff_inverse_transport
    (hfaith : C.SourceFaithful)
    (s : S) (z : α) :
    z ∈ C.LeftResidualLocalizationDomain R s ↔
      C.denominatorInverse s *
          C.sourceHom z =
        C.sourceHom
          (R.leftResidual (s : α) z) := by
  symm
  exact
    C.inverse_mul_source_eq_residual_iff_leftDivides
      R hfaith s z

/-- Symmetric right-domain characterization. -/
theorem mem_rightResidualLocalizationDomain_iff_inverse_transport
    (hfaith : C.SourceFaithful)
    (s : S) (z : α) :
    z ∈ C.RightResidualLocalizationDomain R s ↔
      C.sourceHom z *
          C.denominatorInverse s =
        C.sourceHom
          (R.rightResidual z (s : α)) := by
  symm
  exact
    C.source_mul_inverse_eq_residual_iff_rightDivides
      R hfaith z s

/-- On the exact left domain, the source residual and localized inverse
transport are the same map after source embedding. -/
theorem leftResidual_exact_on_domain
    (hfaith : C.SourceFaithful)
    (s : S)
    (z : C.LeftResidualLocalizationDomain R s) :
    C.sourceHom
        (R.leftResidual (s : α) z.1)
      =
    (C.leftDenominatorPair s).backward
      (C.sourceHom z.1) := by
  exact
    C.leftBackward_compat_of_divides
      R s z.1 z.2

/-- On the exact right domain, the source residual and localized inverse
transport agree symmetrically. -/
theorem rightResidual_exact_on_domain
    (hfaith : C.SourceFaithful)
    (s : S)
    (z : C.RightResidualLocalizationDomain R s) :
    C.sourceHom
        (R.rightResidual z.1 (s : α))
      =
    (C.rightDenominatorPair s).backward
      (C.sourceHom z.1) := by
  exact
    C.rightBackward_compat_of_divides
      R z.1 s z.2

/-- Outside the exact left domain, faithful localization equality is
impossible. -/
theorem inverse_transport_ne_leftResidual_of_not_mem
    (hfaith : C.SourceFaithful)
    (s : S) (z : α)
    (hz :
      z ∉ C.LeftResidualLocalizationDomain R s) :
    C.denominatorInverse s *
          C.sourceHom z
      ≠
    C.sourceHom
      (R.leftResidual (s : α) z) := by
  intro h
  exact hz
    ((C.mem_leftResidualLocalizationDomain_iff_inverse_transport
      R hfaith s z).2 h)

/-- Outside the exact right domain, the analogous equality is impossible. -/
theorem inverse_transport_ne_rightResidual_of_not_mem
    (hfaith : C.SourceFaithful)
    (s : S) (z : α)
    (hz :
      z ∉ C.RightResidualLocalizationDomain R s) :
    C.sourceHom z *
          C.denominatorInverse s
      ≠
    C.sourceHom
      (R.rightResidual z (s : α)) := by
  intro h
  exact hz
    ((C.mem_rightResidualLocalizationDomain_iff_inverse_transport
      R hfaith s z).2 h)

end RightFractionCalculus
end CausalLocalization
end CausalGeometry
