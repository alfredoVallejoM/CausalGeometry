import CausalGeometry.Models.CausalLengthAtomic
import CausalGeometry.Number.IrreduciblePrimitiveBridge
import Mathlib.Tactic

namespace CausalGeometry
namespace Models
namespace CausalLengthPrimitiveBridge

open CausalDivisibility
open CausalPrime
open PrimitiveConjugacy

abbrev CausalLength :=
  CausalLengthAtomic.CausalLength

/-- Embed nonnegative causal lengths into the infinite cyclic group.

Source multiplication is addition of lengths; target multiplication is
addition of integer exponents through `Multiplicative`. -/
def exponentEmbedding :
    CausalLength →*
      Multiplicative ℤ where

  toFun :=
    fun x =>
      Multiplicative.ofAdd
        (Int.ofNat x.toAdd)

  map_one' := by
    apply Multiplicative.toAdd_injective
    simp

  map_mul' := by
    intro x y
    apply Multiplicative.toAdd_injective
    simp

/-- The embedding reflects the target identity back to a causal unit. -/
theorem sourceUnit_of_image_eq_one
    (x : CausalLength)
    (h : exponentEmbedding x = 1) :
    IsCausalUnit x := by

  have hz :=
    congrArg Multiplicative.toAdd h

  simp [exponentEmbedding] at hz

  exact
    (CausalLengthAtomic
      .isCausalUnit_iff_toAdd_zero x).2
      (Int.ofNat_eq_zero.mp hz)

/-- Every causal unit maps to the target identity. -/
theorem image_eq_one_of_sourceUnit
    (x : CausalLength)
    (h : IsCausalUnit x) :
    exponentEmbedding x = 1 := by

  have hz :=
    (CausalLengthAtomic
      .isCausalUnit_iff_toAdd_zero x).1 h

  apply Multiplicative.toAdd_injective

  simp [exponentEmbedding, hz]

/-- A proper-power image of a non-unit causal length must have source length at
least two. -/
theorem length_two_le_of_nonunit_properPower
    (x : CausalLength)
    (hx : ¬ IsCausalUnit x)
    (hpow :
      IsProperPower
        (exponentEmbedding x)) :
    2 ≤ x.toAdd := by

  have hxne :
      x.toAdd ≠ 0 := by
    intro hz
    exact hx
      ((CausalLengthAtomic
        .isCausalUnit_iff_toAdd_zero x).2 hz)

  have hxpos :
      0 < x.toAdd := Nat.pos_of_ne_zero hxne

  rcases hpow with
    ⟨δ, n, hn, hδ⟩

  have hadd :=
    congrArg Multiplicative.toAdd hδ

  simp [exponentEmbedding, nsmul_eq_mul] at hadd

  by_contra htwo

  have hxone :
      x.toAdd = 1 := by
    omega

  have hdvd :
      (n : ℤ) ∣ (1 : ℤ) := by
    refine ⟨δ.toAdd, ?_⟩
    simpa [hxone] using hadd.symm

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

/-- A proper-power target witness of a non-unit causal length lifts to a
genuine nontrivial source factorization. -/
theorem nontrivialFactorization_of_properPower
    (x : CausalLength)
    (hx : ¬ IsCausalUnit x)
    (hpow :
      IsProperPower
        (exponentEmbedding x)) :
    ∃ a b : CausalLength,
      NontrivialFactorization x a b := by

  have htwo :=
    length_two_le_of_nonunit_properPower
      x hx hpow

  let tail : CausalLength :=
    Multiplicative.ofAdd
      (x.toAdd - 1)

  have htailPos :
      0 < tail.toAdd := by
    dsimp [tail]
    omega

  have hfactor :
      CausalLengthAtomic.atom * tail = x := by
    rw [Multiplicative.ext_iff]
    simp [CausalLengthAtomic.atom, tail]
    omega

  refine
    ⟨CausalLengthAtomic.atom,
      tail,
      hfactor,
      CausalLengthAtomic.atom_irreducible.1,
      ?_⟩

  intro hunit

  have hz :=
    (CausalLengthAtomic
      .isCausalUnit_iff_toAdd_zero tail).1
      hunit

  exact (Nat.ne_of_gt htailPos) hz

/-- The forward reflection package is therefore inhabited. -/
def forward :
    CausalPrimitiveBridge
      .IrreducibleToPrimitiveHypotheses
        exponentEmbedding where

  sourceUnit_of_image_eq_one :=
    sourceUnit_of_image_eq_one

  nontrivialFactorization_of_properPower :=
    nontrivialFactorization_of_properPower

/-- Every nontrivial source factorization has total causal length at least
two. -/
theorem length_two_le_of_nontrivialFactorization
    (x a b : CausalLength)
    (h :
      NontrivialFactorization x a b) :
    2 ≤ x.toAdd := by

  have ha :
      a.toAdd ≠ 0 := by
    intro hz
    exact h.2.1
      ((CausalLengthAtomic
        .isCausalUnit_iff_toAdd_zero a).2 hz)

  have hb :
      b.toAdd ≠ 0 := by
    intro hz
    exact h.2.2
      ((CausalLengthAtomic
        .isCausalUnit_iff_toAdd_zero b).2 hz)

  have heq :=
    congrArg Multiplicative.toAdd
      h.1

  simp at heq

  have hapos :
      0 < a.toAdd :=
    Nat.pos_of_ne_zero ha

  have hbpos :
      0 < b.toAdd :=
    Nat.pos_of_ne_zero hb

  omega

/-- Every nontrivial source factorization forces a proper power in the target
cyclic group. -/
theorem properPower_of_nontrivialFactorization
    (x a b : CausalLength)
    (h :
      NontrivialFactorization x a b) :
    IsProperPower
      (exponentEmbedding x) := by

  have htwo :=
    length_two_le_of_nontrivialFactorization
      x a b h

  refine
    ⟨Multiplicative.ofAdd (1 : ℤ),
      x.toAdd,
      htwo,
      ?_⟩

  apply Multiplicative.toAdd_injective

  simp [exponentEmbedding, nsmul_eq_mul]

/-- The reverse reflection package is inhabited as well. -/
def reverse :
    CausalPrimitiveBridge
      .PrimitiveToIrreducibleHypotheses
        exponentEmbedding where

  image_eq_one_of_sourceUnit :=
    image_eq_one_of_sourceUnit

  properPower_of_nontrivialFactorization :=
    properPower_of_nontrivialFactorization

/-- Complete positive bridge on the causal-length model. -/
def bridge :
    CausalPrimitiveBridge
      .IrreduciblePrimitiveEquivalenceHypotheses
        exponentEmbedding where

  forward := forward
  reverse := reverse

/-- In the causal-length model, compositional irreducibility is exactly
primitiveness of the corresponding nonnegative exponent in the infinite
cyclic group. -/
theorem irreducible_iff_primitive
    (x : CausalLength) :
    Irreducible x ↔
      IsPrimitive
        (exponentEmbedding x) :=
  CausalPrimitiveBridge
    .irreducible_iff_primitive
      bridge x

/-- The one-step causal atom realizes as a primitive cyclic element. -/
theorem atom_maps_to_primitive :
    IsPrimitive
      (exponentEmbedding
        CausalLengthAtomic.atom) :=
  (irreducible_iff_primitive
    CausalLengthAtomic.atom).1
      CausalLengthAtomic.atom_irreducible

end CausalLengthPrimitiveBridge
end Models
end CausalGeometry
