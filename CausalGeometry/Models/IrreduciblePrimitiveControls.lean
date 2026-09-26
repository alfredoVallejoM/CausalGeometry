import CausalGeometry.Models.CausalLengthAtomic
import CausalGeometry.Number.IrreduciblePrimitiveBridge
import Mathlib.Tactic

namespace CausalGeometry
namespace Models
namespace IrreduciblePrimitiveControls

open CausalDivisibility
open CausalPrime
open PrimitiveConjugacy

abbrev CausalLength :=
  CausalLengthAtomic.CausalLength

/-- Two independent causal composition directions. -/
abbrev CausalBiLength :=
  CausalLength × CausalLength

/-- Primitive step in the first causal direction. -/
def leftAtom : CausalBiLength :=
  (CausalLengthAtomic.atom, 1)

/-- Primitive step in the second causal direction. -/
def rightAtom : CausalBiLength :=
  (1, CausalLengthAtomic.atom)

/-- A pair is a causal unit exactly when both coordinates are causal units. -/
theorem isCausalUnit_iff_coordinates
    (x : CausalBiLength) :
    IsCausalUnit x ↔
      IsCausalUnit x.1 ∧
      IsCausalUnit x.2 := by

  constructor

  · rintro ⟨y, hxy, hyx⟩

    constructor

    · refine ⟨y.1, ?_, ?_⟩
      · simpa using congrArg Prod.fst hxy
      · simpa using congrArg Prod.fst hyx

    · refine ⟨y.2, ?_, ?_⟩
      · simpa using congrArg Prod.snd hxy
      · simpa using congrArg Prod.snd hyx

  · rintro
      ⟨⟨y₁, hxy₁, hyx₁⟩,
       ⟨y₂, hxy₂, hyx₂⟩⟩

    refine ⟨(y₁, y₂), ?_, ?_⟩

    · apply Prod.ext
      · simpa using hxy₁
      · simpa using hxy₂

    · apply Prod.ext
      · simpa using hyx₁
      · simpa using hyx₂

/-- Concrete coordinate form of the causal-unit criterion. -/
theorem isCausalUnit_iff_lengths_zero
    (x : CausalBiLength) :
    IsCausalUnit x ↔
      x.1.toAdd = 0 ∧
      x.2.toAdd = 0 := by

  rw [isCausalUnit_iff_coordinates]

  constructor

  · rintro ⟨hx, hy⟩
    exact
      ⟨(CausalLengthAtomic.isCausalUnit_iff_toAdd_zero x.1).1 hx,
       (CausalLengthAtomic.isCausalUnit_iff_toAdd_zero x.2).1 hy⟩

  · rintro ⟨hx, hy⟩
    exact
      ⟨(CausalLengthAtomic.isCausalUnit_iff_toAdd_zero x.1).2 hx,
       (CausalLengthAtomic.isCausalUnit_iff_toAdd_zero x.2).2 hy⟩

theorem leftAtom_not_unit :
    ¬ IsCausalUnit leftAtom := by
  rw [isCausalUnit_iff_lengths_zero]
  norm_num [leftAtom, CausalLengthAtomic.atom]

theorem rightAtom_not_unit :
    ¬ IsCausalUnit rightAtom := by
  rw [isCausalUnit_iff_lengths_zero]
  norm_num [rightAtom, CausalLengthAtomic.atom]

/-- The first coordinate step is compositionally irreducible even in the
two-direction causal monoid. -/
theorem leftAtom_irreducible :
    Irreducible leftAtom := by

  constructor

  · exact leftAtom_not_unit

  · intro a b hab

    have hleft :=
      congrArg
        (fun z : CausalBiLength =>
          z.1.toAdd)
        hab

    have hright :=
      congrArg
        (fun z : CausalBiLength =>
          z.2.toAdd)
        hab

    simp [leftAtom,
      CausalLengthAtomic.atom] at
      hleft hright

    have hcases :
        (a.1.toAdd = 0 ∧
          a.2.toAdd = 0) ∨
        (b.1.toAdd = 0 ∧
          b.2.toAdd = 0) := by
      omega

    rcases hcases with ha | hb

    · exact Or.inl
        ((isCausalUnit_iff_lengths_zero a).2
          ha)

    · exact Or.inr
        ((isCausalUnit_iff_lengths_zero b).2
          hb)

/-- Signed cyclic exponent used by the control realization.

The first causal direction contributes +2 and the second contributes -1.
This asymmetry is deliberate: one honest monoid homomorphism witnesses both
directions of independence. -/
def cyclicExponent
    (x : CausalBiLength) : ℤ :=
  2 * (x.1.toAdd : ℤ) -
    (x.2.toAdd : ℤ)

/-- Monoidal cyclic realization into the infinite cyclic group. -/
def cyclicRealization :
    CausalBiLength →*
      Multiplicative ℤ where

  toFun :=
    fun x =>
      Multiplicative.ofAdd
        (cyclicExponent x)

  map_one' := by
    rw [Multiplicative.ext_iff]
    simp [cyclicExponent]

  map_mul' := by
    intro x y
    rw [Multiplicative.ext_iff]
    simp [cyclicExponent]
    ring

/-- Canonical primitive generator of the infinite cyclic target. -/
def cyclicGenerator :
    Multiplicative ℤ :=
  Multiplicative.ofAdd 1

/-- The infinite-cyclic generator is primitive in the proper-power sense. -/
theorem cyclicGenerator_isPrimitive :
    IsPrimitive cyclicGenerator := by

  constructor

  · intro h
    have h' :=
      congrArg Multiplicative.toAdd h
    norm_num [cyclicGenerator] at h'

  · rintro ⟨δ, n, hn, hpow⟩

    have hadd :=
      congrArg Multiplicative.toAdd hpow

    simp [cyclicGenerator,
      nsmul_eq_mul] at hadd

    have hdvd :
        (n : ℤ) ∣ (1 : ℤ) := by
      refine ⟨δ.toAdd, ?_⟩
      exact hadd.symm

    have hnnonneg :
        (0 : ℤ) ≤ (n : ℤ) := by
      exact_mod_cast Nat.zero_le n

    have hnOneInt :
        (n : ℤ) = 1 :=
      Int.eq_one_of_dvd_one
        hnnonneg hdvd

    have hnOne :
        n = 1 := by
      exact_mod_cast hnOneInt

    omega

/-- The irreducible left causal atom is sent to the square of the primitive
cyclic generator. -/
theorem cyclicRealization_leftAtom :
    cyclicRealization leftAtom =
      cyclicGenerator ^ 2 := by
  rw [Multiplicative.ext_iff]
  norm_num [
    cyclicRealization,
    cyclicExponent,
    leftAtom,
    cyclicGenerator,
    CausalLengthAtomic.atom,
    nsmul_eq_mul
  ]

/-- A compositionally irreducible causal atom may realize as a cyclic proper
power. -/
theorem irreducible_but_image_not_primitive :
    Irreducible leftAtom ∧
      ¬ IsPrimitive
        (cyclicRealization leftAtom) := by

  constructor

  · exact leftAtom_irreducible

  · intro hprim
    apply hprim.2
    refine
      ⟨cyclicGenerator, 2, by norm_num, ?_⟩
    exact
      cyclicRealization_leftAtom.symm

/-- Composite of the two independent source atoms. -/
def mixedComposite :
    CausalBiLength :=
  leftAtom * rightAtom

/-- The mixed source element is genuinely reducible. -/
theorem mixedComposite_not_irreducible :
    ¬ Irreducible mixedComposite := by

  intro h

  apply
    no_nontrivial_factorization h

  exact
    ⟨leftAtom,
     rightAtom,
     rfl,
     leftAtom_not_unit,
     rightAtom_not_unit⟩

/-- The same monoidal realization sends that reducible source composite to the
primitive cyclic generator: 2 + (-1) = 1. -/
theorem cyclicRealization_mixedComposite :
    cyclicRealization mixedComposite =
      cyclicGenerator := by

  rw [Multiplicative.ext_iff]

  norm_num [
    cyclicRealization,
    cyclicExponent,
    mixedComposite,
    leftAtom,
    rightAtom,
    cyclicGenerator,
    CausalLengthAtomic.atom
  ]

/-- Reverse separation: a reducible source element can have primitive cyclic
image under the same monoid homomorphism. -/
theorem image_primitive_but_source_reducible :
    IsPrimitive
        (cyclicRealization mixedComposite)
      ∧
    ¬ Irreducible mixedComposite := by

  constructor

  · rw [cyclicRealization_mixedComposite]
    exact cyclicGenerator_isPrimitive

  · exact mixedComposite_not_irreducible

/-- Combined mutation discriminator.

Neither implication between compositional irreducibility and cyclic
primitiveness is valid for an arbitrary monoidal realization.  ECIA must
therefore supply a named bridge satisfying the reflection hypotheses from
IrreduciblePrimitiveBridge before identifying the two notions. -/
theorem no_automatic_irreducible_primitive_bridge :
    (Irreducible leftAtom ∧
      ¬ IsPrimitive
        (cyclicRealization leftAtom))
    ∧
    (IsPrimitive
        (cyclicRealization mixedComposite)
      ∧
      ¬ Irreducible mixedComposite) :=
  ⟨irreducible_but_image_not_primitive,
    image_primitive_but_source_reducible⟩

end IrreduciblePrimitiveControls
end Models
end CausalGeometry
