import CausalGeometry.Calculus.GradedCohomologyTransport
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

namespace GradedLinearTransport

variable
    {K : Type u}
    {C : ℕ → Type v}
    [Field K]
    [∀ n, AddCommGroup (C n)]
    [∀ n, Module K (C n)]

/-- Identity transport induces the identity on every positive cohomology
group. -/
theorem hSuccMap_identity
    (A : GradedCausalCochainComplex K C)
    (n : ℕ) :
    (identity A).hSuccMap
        (identity_natural A) n
      =
    LinearMap.id := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ z =>
      rfl

/-- Identity transport also induces the identity on H0. -/
theorem h0Map_identity
    (A : GradedCausalCochainComplex K C) :
    (identity A).h0Map
        (identity_natural A)
      =
    LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

variable
    {D : ℕ → Type w}
    [∀ n, AddCommGroup (D n)]
    [∀ n, Module K (D n)]
    {A : GradedCausalCochainComplex K C}
    {B : GradedCausalCochainComplex K D}

/-- Cohomology transport is functorial under composition. -/
theorem hSuccMap_comp
    {E : ℕ → Type*}
    [∀ n, AddCommGroup (E n)]
    [∀ n, Module K (E n)]
    {Z : GradedCausalCochainComplex K E}
    (F : GradedLinearTransport A B)
    (G : GradedLinearTransport B Z)
    (hF : F.Natural)
    (hG : G.Natural)
    (n : ℕ) :
    (F.comp G).hSuccMap
        (comp_natural hF hG) n
      =
    (G.hSuccMap hG n).comp
      (F.hSuccMap hF n) := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ z =>
      rfl

theorem h0Map_comp
    {E : ℕ → Type*}
    [∀ n, AddCommGroup (E n)]
    [∀ n, Module K (E n)]
    {Z : GradedCausalCochainComplex K E}
    (F : GradedLinearTransport A B)
    (G : GradedLinearTransport B Z)
    (hF : F.Natural)
    (hG : G.Natural) :
    (F.comp G).h0Map
        (comp_natural hF hG)
      =
    (G.h0Map hG).comp
      (F.h0Map hF) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

end GradedLinearTransport

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

theorem sourceHSuccRoundTrip_eq_induced
    (hF : P.forward.Natural)
    (hB : P.backward.Natural)
    (n : ℕ) :
    P.sourceHSuccRoundTrip hF hB n
      =
    P.sourceRoundTrip.hSuccMap
      (P.sourceRoundTrip_natural hF hB) n := by
  symm
  exact
    GradedLinearTransport.hSuccMap_comp
      P.forward P.backward hF hB n

theorem targetHSuccRoundTrip_eq_induced
    (hF : P.forward.Natural)
    (hB : P.backward.Natural)
    (n : ℕ) :
    P.targetHSuccRoundTrip hF hB n
      =
    P.targetRoundTrip.hSuccMap
      (P.targetRoundTrip_natural hF hB) n := by
  symm
  exact
    GradedLinearTransport.hSuccMap_comp
      P.backward P.forward hB hF n

end PairedCochainTransport
end CausalGeometry
