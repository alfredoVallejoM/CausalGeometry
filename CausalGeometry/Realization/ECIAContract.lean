import CausalGeometry.Number.Basic
import CausalGeometry.Realization.At

namespace CausalGeometry

universe u v w

/-- Source-side description of the target carrier expected from an ECIA
structural-number implementation. CausalGeometry does not import ECIA; the
downstream adapter supplies this target. -/
structure ECIAStructuralTarget (A : Type u) where
  Target : Type v
  admissible : Target → Prop

/-- Contract for consuming causal numbers as ECIA structural numbers.

The only primitive bridge law here is soundness of admissibility. Preservation
of shadows, dagger, composition, cyclic structure or further ECIA operations
must be supplied as separate comparison theorems rather than optional fields
hidden inside the causal number. -/
structure ECIARealization
    (A : Type u)
    (sourceAdmissible : CausalNumber A → Prop)
    (T : ECIAStructuralTarget.{u, v} A) where
  realize : CausalNumber A → T.Target
  sound :
    ∀ X, sourceAdmissible X → T.admissible (realize X)

namespace ECIARealization

def asAnyRealization
    {A : Type u}
    {sourceAdmissible : CausalNumber A → Prop}
    {T : ECIAStructuralTarget.{u, v} A}
    (R : ECIARealization A sourceAdmissible T) :
    AnyRealization (CausalNumber A) where
  Target := T.Target
  map := R.realize

/-- The ECIA image of one fixed causal number is an object of the general
CA-19 realization-at-source interface. -/
def at
    {A : Type u}
    {sourceAdmissible : CausalNumber A → Prop}
    {T : ECIAStructuralTarget.{u, v} A}
    (R : ECIARealization A sourceAdmissible T)
    (X : CausalNumber A) :
    RealizationAt X :=
  RealizationAt.of R.asAnyRealization X

end ECIARealization

/-- A preservation theorem for one observable transported through the ECIA
adapter. Distinct observables obtain distinct proofs, preventing accidental
collapse of provenance, arithmetic shadow, dagger and cyclic data. -/
structure ECIAObservableCompatibility
    {A : Type u}
    {sourceAdmissible : CausalNumber A → Prop}
    {T : ECIAStructuralTarget.{u, v} A}
    (R : ECIARealization A sourceAdmissible T)
    {Γ : Type w}
    (sourceObservable : CausalNumber A → Γ)
    (targetObservable : T.Target → Γ) : Prop where
  commutes :
    ∀ X, targetObservable (R.realize X) = sourceObservable X

end CausalGeometry
