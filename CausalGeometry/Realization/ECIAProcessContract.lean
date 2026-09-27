import CausalGeometry.Cyclic.DiaryShadow
import CausalGeometry.Process.Dagger
import CausalGeometry.Realization.ECIAContract

namespace CausalGeometry

universe u v w x

namespace ECIARealization

variable {A : Type u}
variable {sourceAdmissible : CausalNumber A → Prop}
variable {T : ECIAStructuralTarget.{u, v} A}

/-- Pointwise preservation of one witnessed causal composite.

This is deliberately a predicate attached to a concrete gluing witness rather
than a field of ECIARealization. -/
def PreservesComposite
    (R : ECIARealization A sourceAdmissible T)
    (targetCompose : T.Target → T.Target → T.Target)
    {X Y : CausalNumber A}
    (G : DiaryCompositionData X Y) : Prop :=
  R.realize G.result =
    targetCompose (R.realize X) (R.realize Y)

/-- Pointwise preservation of one witnessed causal composite up to an
explicit target equivalence.

This is the contract for categorical ECIA targets whose composition is
preserved by a specified isomorphism/equivalence rather than by literal
equality. The downstream target supplies the equivalence notion. -/
def PreservesCompositeUpTo
    (R : ECIARealization A sourceAdmissible T)
    (targetCompose : T.Target → T.Target → T.Target)
    (targetEquivalent : T.Target → T.Target → Prop)
    {X Y : CausalNumber A}
    (G : DiaryCompositionData X Y) : Prop :=
  targetEquivalent
    (R.realize G.result)
    (targetCompose (R.realize X) (R.realize Y))

/-- Strict preservation is a special case of preservation up to any reflexive
target equivalence. -/
theorem preservesCompositeUpTo_of_strict
    (R : ECIARealization A sourceAdmissible T)
    (targetCompose : T.Target → T.Target → T.Target)
    (targetEquivalent : T.Target → T.Target → Prop)
    (hrefl : ∀ Z, targetEquivalent Z Z)
    {X Y : CausalNumber A}
    (G : DiaryCompositionData X Y)
    (hstrict : R.PreservesComposite targetCompose G) :
    R.PreservesCompositeUpTo
      targetCompose targetEquivalent G := by
  unfold PreservesCompositeUpTo
  rw [hstrict]
  exact hrefl _

/-- Pointwise preservation of one genuine event-level dagger witness. -/
def PreservesDagger
    (R : ECIARealization A sourceAdmissible T)
    (targetDagger : T.Target → T.Target)
    {X : CausalNumber A}
    (D : DiaryDaggerData X) : Prop :=
  R.realize D.dagger = targetDagger (R.realize X)

/-- Preservation of a selected cyclic-shadow observable. -/
def PreservesCyclicShadow
    (R : ECIARealization A sourceAdmissible T)
    (S : DiaryCyclicShadow.{u, w} A)
    (targetShadow : T.Target → S.Cycle) : Prop :=
  ∀ X, targetShadow (R.realize X) = S.close X

/-- Preservation of any additional typed observable remains pointwise and
separate from composition/dagger/cyclicity. -/
def PreservesObservable
    (R : ECIARealization A sourceAdmissible T)
    {Γ : Type x}
    (sourceObservable : CausalNumber A → Γ)
    (targetObservable : T.Target → Γ) : Prop :=
  ∀ X, targetObservable (R.realize X) = sourceObservable X

end ECIARealization
end CausalGeometry
