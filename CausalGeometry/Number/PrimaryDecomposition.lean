import CausalGeometry.Number.ArithmeticShadow
import CausalGeometry.Number.NatShadow
import CausalGeometry.Number.Prime
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace CausalGeometry

open scoped BigOperators

universe u

namespace CausalPrimary

open CausalPrime

variable {α : Type u} [CommMonoid α]

/-- Finite primary decomposition at the causal level.  The bases remain causal
objects; no classical prime labels occur in this structure. -/
structure Decomposition (x : α) where
  count : ℕ
  base : Fin count → α
  exponent : Fin count → ℕ
  exponent_pos : ∀ i, 0 < exponent i
  atomic : ∀ i, Irreducible (base i)
  reconstruct : (∏ i, base i ^ exponent i) = x

namespace Decomposition

variable {x : α} (D : Decomposition x)

def channel (i : Fin D.count) : α :=
  D.base i ^ D.exponent i

theorem product_channels :
    (∏ i, D.channel i) = x := by
  simpa [channel] using D.reconstruct

/-- Arithmetic realization of the causal primary bases.  Distinct causal
channels must map to distinct classical primes. -/
structure PrimeRealization (S : NatShadow α) where
  prime : Fin D.count → Nat.Primes
  prime_injective : Function.Injective prime
  base_shadow : ∀ i, S (D.base i) = (prime i).1

namespace PrimeRealization

variable {S : NatShadow α} (R : D.PrimeRealization S)

@[simp] theorem channel_shadow (i : Fin D.count) :
    S (D.channel i) =
      (R.prime i).1 ^ D.exponent i := by
  simp [Decomposition.channel, NatShadow.pow, R.base_shadow]

/-- The multiplicative classical shadow is reconstructed from the realized
primary channels. -/
theorem shadow_eq_prime_product :
    S x =
      ∏ i, (R.prime i).1 ^ D.exponent i := by
  rw [← D.product_channels]
  change S (∏ i, D.channel i) = _
  rw [← map_prod (S.toMonoidHom) (fun i => D.channel i) Finset.univ]
  simp [R.channel_shadow]

/-- Distinct realized primary channels are pairwise coprime after taking their
positive powers. -/
theorem pairwise_coprime_channels :
    Pairwise
      (Nat.Coprime on
        fun i : Fin D.count =>
          (R.prime i).1 ^ D.exponent i) := by
  intro i j hij
  apply Nat.Coprime.pow
  apply (Nat.coprime_primes (R.prime i).2 (R.prime j).2).mpr
  intro hp
  apply hij
  apply R.prime_injective
  exact Subtype.ext hp

/-- Classical CRT realization of independent causal primary channels. -/
noncomputable def crtEquiv :
    ZMod (S x) ≃+*
      (∀ i : Fin D.count,
        ZMod ((R.prime i).1 ^ D.exponent i)) := by
  rw [R.shadow_eq_prime_product]
  exact ZMod.prodEquivPi
    (fun i : Fin D.count =>
      (R.prime i).1 ^ D.exponent i)
    R.pairwise_coprime_channels

/-- Prime profile derived from the realized causal primary decomposition. -/
def primeProfile : PrimeProfile :=
  ⟨∑ i : Fin D.count,
      Finsupp.single (R.prime i) (D.exponent i)⟩

@[simp] theorem primeProfile_exponents :
    R.primeProfile.exponents =
      ∑ i : Fin D.count,
        Finsupp.single (R.prime i) (D.exponent i) := rfl

end PrimeRealization
end Decomposition
end CausalPrimary
end CausalGeometry
