import CausalGeometry.Number.IrreduciblePrimitiveBridge
import CausalGeometry.Realization.ECIAContract

namespace CausalGeometry

universe u v w x

namespace ECIARealization

open CausalPrime
open PrimitiveConjugacy

variable {A : Type u}
variable {sourceAdmissible : CausalNumber A → Prop}
variable {T : ECIAStructuralTarget.{u, v} A}

/-- Forward-only ECIA contract connecting source compositional irreducibility
to target cyclic primitiveness.

The source factor carrier and the target cyclic carrier are explicit.  ECIA
does not get an irreducible-to-primitive theorem merely from preserving a
numerical primitive-count shadow: it must provide a monoid realization and the
reflection hypotheses required by CausalPrimitiveBridge. -/
structure PreservesIrreducibleToPrimitive
    (R : ECIARealization A sourceAdmissible T)
    (M : Type w)
    [Monoid M]
    (Γ : Type x)
    [Group Γ]
    (sourceFactor : CausalNumber A → M)
    (targetCyclic : T.Target → Γ)
    (φ : M →* Γ) : Prop where

  comparison :
    ∀ X : CausalNumber A,
      targetCyclic (R.realize X) =
        φ (sourceFactor X)

  bridge :
    CausalPrimitiveBridge
      .IrreducibleToPrimitiveHypotheses φ

namespace PreservesIrreducibleToPrimitive

variable
    {R : ECIARealization A sourceAdmissible T}
    {M : Type w}
    [Monoid M]
    {Γ : Type x}
    [Group Γ]
    {sourceFactor : CausalNumber A → M}
    {targetCyclic : T.Target → Γ}
    {φ : M →* Γ}
    (h :
      R.PreservesIrreducibleToPrimitive
        M Γ sourceFactor targetCyclic φ)

/-- A proved source atom yields a target primitive cyclic element only through
the explicit forward bridge. -/
theorem targetPrimitive_of_sourceIrreducible
    (X : CausalNumber A)
    (hX : Irreducible (sourceFactor X)) :
    IsPrimitive
      (targetCyclic (R.realize X)) := by

  rw [h.comparison X]

  exact
    CausalPrimitiveBridge
      .irreducible_implies_primitive
        h.bridge hX

end PreservesIrreducibleToPrimitive

/-- Reverse-only ECIA contract connecting target cyclic primitiveness back to
source compositional irreducibility.

It is deliberately independent of the forward contract. -/
structure PreservesPrimitiveToIrreducible
    (R : ECIARealization A sourceAdmissible T)
    (M : Type w)
    [Monoid M]
    (Γ : Type x)
    [Group Γ]
    (sourceFactor : CausalNumber A → M)
    (targetCyclic : T.Target → Γ)
    (φ : M →* Γ) : Prop where

  comparison :
    ∀ X : CausalNumber A,
      targetCyclic (R.realize X) =
        φ (sourceFactor X)

  bridge :
    CausalPrimitiveBridge
      .PrimitiveToIrreducibleHypotheses φ

namespace PreservesPrimitiveToIrreducible

variable
    {R : ECIARealization A sourceAdmissible T}
    {M : Type w}
    [Monoid M]
    {Γ : Type x}
    [Group Γ]
    {sourceFactor : CausalNumber A → M}
    {targetCyclic : T.Target → Γ}
    {φ : M →* Γ}
    (h :
      R.PreservesPrimitiveToIrreducible
        M Γ sourceFactor targetCyclic φ)

/-- A target primitive class reflects to source irreducibility only through
the explicit reverse bridge. -/
theorem sourceIrreducible_of_targetPrimitive
    (X : CausalNumber A)
    (hX :
      IsPrimitive
        (targetCyclic (R.realize X))) :
    Irreducible (sourceFactor X) := by

  rw [h.comparison X] at hX

  exact
    CausalPrimitiveBridge
      .primitive_implies_irreducible
        h.bridge hX

end PreservesPrimitiveToIrreducible

/-- Bidirectional ECIA contract.

This package is strictly stronger than either directional contract and is the
minimum source-side evidence needed before ECIA may state that its primitive
cyclic classes identify source compositional atoms on a named realization
domain. -/
structure PreservesIrreduciblePrimitiveEquivalence
    (R : ECIARealization A sourceAdmissible T)
    (M : Type w)
    [Monoid M]
    (Γ : Type x)
    [Group Γ]
    (sourceFactor : CausalNumber A → M)
    (targetCyclic : T.Target → Γ)
    (φ : M →* Γ) : Prop where

  comparison :
    ∀ X : CausalNumber A,
      targetCyclic (R.realize X) =
        φ (sourceFactor X)

  bridge :
    CausalPrimitiveBridge
      .IrreduciblePrimitiveEquivalenceHypotheses φ

namespace PreservesIrreduciblePrimitiveEquivalence

variable
    {R : ECIARealization A sourceAdmissible T}
    {M : Type w}
    [Monoid M]
    {Γ : Type x}
    [Group Γ]
    {sourceFactor : CausalNumber A → M}
    {targetCyclic : T.Target → Γ}
    {φ : M →* Γ}
    (h :
      R.PreservesIrreduciblePrimitiveEquivalence
        M Γ sourceFactor targetCyclic φ)

/-- Exact atom/primitive comparison on the named ECIA realization. -/
theorem sourceIrreducible_iff_targetPrimitive
    (X : CausalNumber A) :
    Irreducible (sourceFactor X) ↔
      IsPrimitive
        (targetCyclic (R.realize X)) := by

  rw [h.comparison X]

  exact
    CausalPrimitiveBridge
      .irreducible_iff_primitive
        h.bridge
        (sourceFactor X)

end PreservesIrreduciblePrimitiveEquivalence
end ECIARealization
end CausalGeometry
