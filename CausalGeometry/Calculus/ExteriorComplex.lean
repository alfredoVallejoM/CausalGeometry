import CausalGeometry.Calculus.ExteriorTwoForm
import Mathlib.Tactic

namespace CausalGeometry

universe u v w
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalExteriorComplex

variable {K : Type w} [AddCommGroup K]

/-- A one-form evaluated on the remaining direction k after executing i then
j agrees with its value after executing j then i.  The only geometric input is
flatness of the concurrency diamond (i,j). -/
theorem oneForm_value_after_two_swap
    (ω : CausalOneForm S K)
    {C : Configuration S}
    {ι : Type*}
    (Q : CausalCubeFrame S C ι)
    (i j k : ι)
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k) :
    let dij :=
      Q.diamondAfter i j k
        hij.symm hik.symm hjk
    let dji :=
      Q.diamondAfter j i k
        hij hjk.symm hik
    ω.value dij.afterE
        (CausalOneForm.afterE_F dij) =
      ω.value dji.afterE
        (CausalOneForm.afterE_F dji) := by
  dsimp
  let dij :=
    Q.diamondAfter i j k
      hij.symm hik.symm hjk
  let dji :=
    Q.diamondAfter j i k
      hij hjk.symm hik
  have hcfg :
      dij.afterE = dji.afterE := by
    change
      (Q.diamond hij).afterEF =
        (Q.diamond hij).afterFE
    exact
      ConcurrencyDiamond.endpoint_eq
        (Q.diamond hij)
  cases hcfg
  apply congrArg (ω.value dij.afterE)
  apply EventDirection.ext
  rfl

/-- Cubical d^2=0 in degrees 1 -> 2 -> 3.

Every one-form has closed exterior derivative. The proof is a cancellation of
the six first-order face variations after identifying pairwise-concurrent
double endpoints. -/
theorem exteriorDerivative_closed
    (ω : CausalOneForm S K) :
    (CausalTwoForm.ofExteriorDerivative ω).Closed := by
  intro C ι Q i j k hij hik hjk
  have hk :=
    oneForm_value_after_two_swap
      ω Q i j k hij hik hjk
  have hj :=
    oneForm_value_after_two_swap
      ω Q i k j hik hij hjk.symm
  have hi :=
    oneForm_value_after_two_swap
      ω Q j k i hjk hij.symm hik.symm
  unfold CausalTwoForm.exteriorDerivative
    CausalTwoForm.variationAlong
    CausalTwoForm.ofExteriorDerivative
    CausalOneForm.exteriorDerivative
    CausalOneForm.variationEF
    CausalOneForm.variationFE
  rw [hk, hj, hi]
  abel

/-- The exterior derivative therefore maps arbitrary one-forms into closed
two-forms. -/
def exteriorDerivativeClosed
    (ω : CausalOneForm S K) :
    {η : CausalTwoForm S K // η.Closed} :=
  ⟨CausalTwoForm.ofExteriorDerivative ω,
    exteriorDerivative_closed ω⟩

/-- Exact one-forms provide the previous degree of the same complex. -/
theorem exact_exteriorDerivative_zero
    (F : Configuration S → K)
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    (CausalTwoForm.ofExteriorDerivative
      (CausalOneForm.exact F)).value d = 0 :=
  CausalTwoForm.ofExteriorDerivative_exact_value
    F d

end CausalExteriorComplex
end CausalGeometry
