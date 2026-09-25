import CausalGeometry.Calculus.EventDirection
import CausalGeometry.Calculus.IteratedDifference
import Mathlib.Tactic

namespace CausalGeometry

universe u v w
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

/-- Scalar causal one-form: a value for every enabled primitive-event
direction at every derived configuration. -/
structure CausalOneForm
    (S : EventSystem Event Label)
    (K : Type w) where
  value :
    ∀ (C : Configuration S),
      EventDirection S C → K

namespace CausalOneForm

variable {K : Type w}

@[ext] theorem ext
    {ω η : CausalOneForm S K}
    (h :
      ∀ (C : Configuration S)
        (d : EventDirection S C),
        ω.value C d = η.value C d) :
    ω = η := by
  cases ω with
  | mk ω =>
      cases η with
      | mk η =>
          congr
          funext C d
          exact h C d


/-- Base e direction of one concurrency diamond. -/
def baseE
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    EventDirection S C where
  event := e
  enabled := d.concurrent.1

/-- Base f direction. -/
def baseF
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    EventDirection S C where
  event := f
  enabled := d.concurrent.2.1

/-- Direction f after executing e. -/
def afterE_F
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    EventDirection S d.afterE where
  event := f
  enabled :=
    S.concurrent_enabled_after_left
      d.concurrent

/-- Direction e after executing f. -/
def afterF_E
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    EventDirection S d.afterF where
  event := e
  enabled :=
    S.concurrent_enabled_after_right
      d.concurrent

/-- Directional variation of a one-form component f along concurrent
direction e. -/
def variationEF
    [AddGroup K]
    (ω : CausalOneForm S K)
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) : K :=
  ω.value d.afterE (afterE_F d) -
    ω.value C (baseF d)

/-- Opposite component variation. -/
def variationFE
    [AddGroup K]
    (ω : CausalOneForm S K)
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) : K :=
  ω.value d.afterF (afterF_E d) -
    ω.value C (baseE d)

/-- Discrete exterior derivative of a causal one-form on a concurrency
diamond. -/
def exteriorDerivative
    [AddGroup K]
    (ω : CausalOneForm S K)
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) : K :=
  variationEF ω d -
    variationFE ω d

/-- Reversing the oriented concurrency square negates the exterior
derivative. -/
theorem exteriorDerivative_symm
    [AddCommGroup K]
    (ω : CausalOneForm S K)
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    exteriorDerivative ω d.symm =
      - exteriorDerivative ω d := by
  unfold exteriorDerivative variationEF variationFE
  change
    (ω.value d.afterF (afterF_E d) -
        ω.value C (baseE d)) -
      (ω.value d.afterE (afterE_F d) -
        ω.value C (baseF d))
      =
    - ((ω.value d.afterE (afterE_F d) -
          ω.value C (baseF d)) -
        (ω.value d.afterF (afterF_E d) -
          ω.value C (baseE d)))
  abel

/-- A one-form is closed when its exterior derivative vanishes on every
genuine concurrency diamond. -/
def Closed
    [Zero K] [Sub K]
    (ω : CausalOneForm S K) : Prop :=
  ∀ {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f),
      exteriorDerivative ω d = 0

/-- Exact one-form generated from a scalar configuration observable. -/
def exact
    [AddGroup K]
    (F : Configuration S → K) :
    CausalOneForm S K where
  value := fun C d =>
    causalDifference F C
      d.event d.enabled

@[simp] theorem exact_value
    [AddGroup K]
    (F : Configuration S → K)
    (C : Configuration S)
    (d : EventDirection S C) :
    (exact F).value C d =
      causalDifference F C
        d.event d.enabled :=
  rfl

/-- Mixed first variation of an exact one-form is the square variation of its
potential. -/
theorem exact_variationEF
    [AddCommGroup K]
    (F : Configuration S → K)
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    variationEF (exact F) d =
      causalSquareVariation F d := by
  unfold variationEF exact
    causalDifference causalSquareVariation
  change
    (F d.afterEF - F d.afterE) -
        (F d.afterF - F C) =
      F d.afterEF - F d.afterE -
        F d.afterF + F C
  abel

theorem exact_variationFE
    [AddCommGroup K]
    (F : Configuration S → K)
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    variationFE (exact F) d =
      causalSquareVariation F d.symm := by
  unfold variationFE exact
    causalDifference causalSquareVariation
  change
    (F d.afterFE - F d.afterF) -
        (F d.afterE - F C) =
      F d.afterFE - F d.afterF -
        F d.afterE + F C
  abel

/-- Discrete d^2=0: every exact causal one-form is closed. -/
theorem exact_closed
    [AddCommGroup K]
    (F : Configuration S → K) :
    (exact F).Closed := by
  intro C e f d
  unfold Closed exteriorDerivative
  rw [exact_variationEF, exact_variationFE]
  rw [causalSquareVariation_symm]
  exact sub_self _

end CausalOneForm

/-- Antisymmetric causal two-form evaluated on genuine concurrency
diamonds. -/
structure CausalTwoForm
    (S : EventSystem Event Label)
    (K : Type w)
    [Neg K] where
  value :
    ∀ {C : Configuration S}
      {e f : Event},
      ConcurrencyDiamond C e f → K

  skew :
    ∀ {C : Configuration S}
      {e f : Event}
      (d : ConcurrencyDiamond C e f),
      value d.symm = - value d

namespace CausalTwoForm

variable {K : Type w} [AddCommGroup K]

@[ext] theorem ext
    {ω η : CausalTwoForm S K}
    (h :
      ∀ {C : Configuration S}
        {e f : Event}
        (d : ConcurrencyDiamond C e f),
        ω.value d = η.value d) :
    ω = η := by
  cases ω with
  | mk ω hω =>
      cases η with
      | mk η hη =>
          congr
          funext C e f d
          exact h d

/-- Exterior derivative packages canonically as an antisymmetric two-form. -/
def ofExteriorDerivative
    (ω : CausalOneForm S K) :
    CausalTwoForm S K where
  value := fun d =>
    CausalOneForm.exteriorDerivative ω d
  skew := fun d =>
    CausalOneForm.exteriorDerivative_symm
      ω d

/-- Exterior derivative of an exact potential is the zero two-form pointwise. -/
@[simp] theorem ofExteriorDerivative_exact_value
    (F : Configuration S → K)
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    (ofExteriorDerivative
      (CausalOneForm.exact F)).value d = 0 :=
  CausalOneForm.exact_closed F d

end CausalTwoForm
end CausalGeometry
