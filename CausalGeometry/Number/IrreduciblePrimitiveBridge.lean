import CausalGeometry.Number.Prime
import CausalGeometry.Cyclic.PrimitiveConjugacy

namespace CausalGeometry

universe u v

namespace CausalPrimitiveBridge

open CausalDivisibility
open CausalPrime
open PrimitiveConjugacy

variable
    {α : Type u}
    {Γ : Type v}
    [Monoid α]
    [Group Γ]

/-- Sufficient hypotheses for transporting compositional irreducibility
forward to cyclic/group primitiveness.

These hypotheses are intentionally stronger than merely asking for a monoid
homomorphism.  They state the two reflection properties that are actually
needed:

* target identity may only come from a causal unit;
* every proper-power witness in the target lifts to a genuine nontrivial
  source factorization. -/
structure IrreducibleToPrimitiveHypotheses
    (φ : α →* Γ) : Prop where

  sourceUnit_of_image_eq_one :
    ∀ x : α,
      φ x = 1 →
      IsCausalUnit x

  nontrivialFactorization_of_properPower :
    ∀ x : α,
      IsProperPower (φ x) →
      ∃ a b : α,
        NontrivialFactorization x a b

/-- Under the exact reflection hypotheses above, source irreducibility implies
target cyclic primitiveness. -/
theorem irreducible_implies_primitive
    {φ : α →* Γ}
    (H : IrreducibleToPrimitiveHypotheses φ)
    {x : α}
    (hx : Irreducible x) :
    IsPrimitive (φ x) := by

  constructor

  · intro hφ
    exact hx.1
      (H.sourceUnit_of_image_eq_one x hφ)

  · intro hpow
    rcases
        H.nontrivialFactorization_of_properPower
          x hpow with
      ⟨a, b, hab⟩

    exact
      (no_nontrivial_factorization hx)
        ⟨a, b, hab⟩

/-- Sufficient hypotheses for reflecting target cyclic primitiveness back to
compositional irreducibility.

Again these are not automatic for an arbitrary realization:

* every causal unit must collapse to the target identity;
* every nontrivial source factorization must become a proper power. -/
structure PrimitiveToIrreducibleHypotheses
    (φ : α →* Γ) : Prop where

  image_eq_one_of_sourceUnit :
    ∀ x : α,
      IsCausalUnit x →
      φ x = 1

  properPower_of_nontrivialFactorization :
    ∀ x a b : α,
      NontrivialFactorization x a b →
      IsProperPower (φ x)

/-- Under the reverse reflection hypotheses, target cyclic primitiveness
forces source compositional irreducibility. -/
theorem primitive_implies_irreducible
    {φ : α →* Γ}
    (H : PrimitiveToIrreducibleHypotheses φ)
    {x : α}
    (hx : IsPrimitive (φ x)) :
    Irreducible x := by

  constructor

  · intro hunit
    exact hx.1
      (H.image_eq_one_of_sourceUnit x hunit)

  · intro a b hab

    by_cases ha : IsCausalUnit a

    · exact Or.inl ha

    · by_cases hb : IsCausalUnit b

      · exact Or.inr hb

      · exfalso
        apply hx.2
        exact
          H.properPower_of_nontrivialFactorization
            x a b
            ⟨hab, ha, hb⟩

/-- Bidirectional bridge package.  This is the exact kind of additional
information required before ECIA may identify compositional atoms with
primitive cyclic classes. -/
structure IrreduciblePrimitiveEquivalenceHypotheses
    (φ : α →* Γ) : Prop where

  forward :
    IrreducibleToPrimitiveHypotheses φ

  reverse :
    PrimitiveToIrreducibleHypotheses φ

/-- With both reflection packages, irreducibility and cyclic primitiveness are
equivalent along the chosen realization. -/
theorem irreducible_iff_primitive
    {φ : α →* Γ}
    (H : IrreduciblePrimitiveEquivalenceHypotheses φ)
    (x : α) :
    Irreducible x ↔
      IsPrimitive (φ x) := by

  constructor

  · exact
      irreducible_implies_primitive
        H.forward

  · exact
      primitive_implies_irreducible
        H.reverse

end CausalPrimitiveBridge
end CausalGeometry
