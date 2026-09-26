import CausalGeometry.Calculus.RelativeConnecting
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

namespace GradedLinearTransport

variable
    {K : Type u}
    {C : ℕ → Type v}
    {D : ℕ → Type w}
    [Field K]
    [∀ n, AddCommGroup (C n)]
    [∀ n, Module K (C n)]
    [∀ n, AddCommGroup (D n)]
    [∀ n, Module K (D n)]
    {A : GradedCausalCochainComplex K C}
    {B : GradedCausalCochainComplex K D}
    (F : GradedLinearTransport A B)
    (hF : F.Natural)

/-- Relative-to-source map on H0. -/
def relativeToSourceH0 :
    F.RelativeH0 hF →ₗ[K] A.H0 :=
  (F.relativeInclusion hF).h0Map
    (F.relativeInclusion_natural hF)

/-- Relative-to-source map on positive cohomology. -/
def relativeToSourceHSucc
    (n : ℕ) :
    F.RelativeHSucc hF n →ₗ[K]
      A.HSucc n :=
  (F.relativeInclusion hF).hSuccMap
    (F.relativeInclusion_natural hF) n

/-- Restriction after relative inclusion vanishes on H0. -/
theorem h0Map_comp_relativeToSource_zero :
    (F.h0Map hF).comp
        (F.relativeToSourceH0 hF)
      =
    0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change
    F.map 0 ((x : F.RelativeCochain 0) : C 0) = 0
  exact x.1.2

/-- Restriction after relative inclusion vanishes on every positive
cohomology group. -/
theorem hSuccMap_comp_relativeToSource_zero
    (n : ℕ) :
    (F.hSuccMap hF n).comp
        (F.relativeToSourceHSucc hF n)
      =
    0 := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ z =>
      change
        F.hSuccMap hF n
          ((F.relativeInclusion hF).hSuccMap
            (F.relativeInclusion_natural hF) n
            ((F.relativeComplex hF)
              .classOfClosedSucc n z))
          =
        0
      rw [
        (F.relativeInclusion hF)
          .hSuccMap_classOfClosed,
        F.hSuccMap_classOfClosed
      ]
      apply
        ((B.classOfClosedSucc_eq_zero_iff
          n
          (F.closedMapSucc hF n
            ((F.relativeInclusion hF)
              .closedMapSucc
                (F.relativeInclusion_natural hF)
                n z))).2)
      change
        F.map (n + 1)
          ((z :
            (F.relativeComplex hF).Closed (n + 1)) :
              F.RelativeCochain (n + 1))
          ∈
        B.ExactSucc n
      rw [z.1.2]
      exact (B.ExactSucc n).zero_mem

/-- The three consecutive positive-degree maps now form a cochain-level
candidate for the long exact sequence:

H_rel^(n+1) -> H_A^(n+1) -> H_B^(n+1) -> H_rel^(n+2).

Both consecutive composites are proved zero; exactness at the middle terms is
a stronger theorem and remains separate. -/
structure RelativeLongSequenceSegment
    (Sec : F.GradedLinearSection)
    (n : ℕ) where

  relativeToSource :
    F.RelativeHSucc hF n →ₗ[K]
      A.HSucc n :=
    F.relativeToSourceHSucc hF n

  sourceToTarget :
    A.HSucc n →ₗ[K]
      B.HSucc n :=
    F.hSuccMap hF n

  connecting :
    B.HSucc n →ₗ[K]
      F.RelativeHSucc hF (n + 1) :=
    F.connectingHSucc hF Sec n

  first_comp_zero :
    sourceToTarget.comp relativeToSource = 0 :=
      F.hSuccMap_comp_relativeToSource_zero hF n

  second_comp_zero :
    connecting.comp sourceToTarget = 0 :=
      F.connectingHSucc_comp_hSuccMap_zero hF Sec n

end GradedLinearTransport
end CausalGeometry
