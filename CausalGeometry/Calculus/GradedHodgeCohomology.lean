import CausalGeometry.Calculus.GradedCohomologyFunctoriality
import CausalGeometry.Calculus.PairedHodgeTransport
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

namespace PairedCochainTransport

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
    (P : PairedCochainTransport A B)
    (HA : GradedCausalHodgeData A)
    (HB : GradedCausalHodgeData B)

/-- Hodge/cohomology naturality square for Phi.

The left route first transports a harmonic representative and then takes its
target Hodge class.  The right route first takes the source Hodge class and
then applies the induced cohomology map.  The two routes agree because both are
represented by the same transported closed cochain. -/
theorem forward_hodge_cohomology_commutes
    (hD : P.forward.Natural)
    (hLap :
      ∀ n,
        (HB.laplacianSucc n).comp
            (P.forward.map (n + 1)) =
          (P.forward.map (n + 1)).comp
            (HA.laplacianSucc n))
    (n : ℕ)
    (RA : GradedCausalHodgeRepresentationSucc HA n)
    (RB : GradedCausalHodgeRepresentationSucc HB n)
    (x : HA.HarmonicSucc n) :
    RB.harmonicEquivHSucc
        (P.forwardHarmonicSuccMap HA HB hLap n x)
      =
    P.forwardHSuccMap hD n
        (RA.harmonicEquivHSucc x) := by
  change
    B.classOfClosedSucc n
        (RB.harmonicToClosed
          (P.forwardHarmonicSuccMap HA HB hLap n x))
      =
    B.classOfClosedSucc n
      (P.forward.closedMapSucc hD n
        (RA.harmonicToClosed x))
  apply congrArg (B.classOfClosedSucc n)
  apply Subtype.ext
  rfl

/-- Symmetric Hodge/cohomology naturality square for Psi. -/
theorem backward_hodge_cohomology_commutes
    (hD : P.backward.Natural)
    (hLap :
      ∀ n,
        (HA.laplacianSucc n).comp
            (P.backward.map (n + 1)) =
          (P.backward.map (n + 1)).comp
            (HB.laplacianSucc n))
    (n : ℕ)
    (RA : GradedCausalHodgeRepresentationSucc HA n)
    (RB : GradedCausalHodgeRepresentationSucc HB n)
    (x : HB.HarmonicSucc n) :
    RA.harmonicEquivHSucc
        (P.backwardHarmonicSuccMap HA HB hLap n x)
      =
    P.backwardHSuccMap hD n
        (RB.harmonicEquivHSucc x) := by
  change
    A.classOfClosedSucc n
        (RA.harmonicToClosed
          (P.backwardHarmonicSuccMap HA HB hLap n x))
      =
    A.classOfClosedSucc n
      (P.backward.closedMapSucc hD n
        (RB.harmonicToClosed x))
  apply congrArg (A.classOfClosedSucc n)
  apply Subtype.ext
  rfl

end PairedCochainTransport
end CausalGeometry
