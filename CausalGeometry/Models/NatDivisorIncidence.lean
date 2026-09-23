import CausalGeometry.Number.Incidence
import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Interval.Finset.Defs

namespace CausalGeometry

namespace NatDivisorIncidence

/-- Divisors of n as a finite type.  Their order below is divisibility, not
the usual numerical order. -/
def Divisor (n : ℕ) :=
  {d : ℕ // d ∈ n.divisors}

instance (n : ℕ) : DecidableEq (Divisor n) :=
  inferInstance

instance (n : ℕ) : LE (Divisor n) where
  le a b := a.1 ∣ b.1

instance (n : ℕ) : PartialOrder (Divisor n) where
  le_refl a := dvd_refl a.1
  le_trans a b c hab hbc := dvd_trans hab hbc
  le_antisymm a b hab hba :=
    Subtype.ext (Nat.dvd_antisymm hab hba)

instance (n : ℕ) : DecidableLE (Divisor n) :=
  fun a b => inferInstance

instance (n : ℕ) : DecidableLT (Divisor n) :=
  fun a b => inferInstance

instance (n : ℕ) : Fintype (Divisor n) :=
  Finset.fintypeCoeSort n.divisors

instance (n : ℕ) : LocallyFiniteOrder (Divisor n) :=
  Fintype.toLocallyFiniteOrder

instance (n : ℕ) [NeZero n] : OrderBot (Divisor n) where
  bot := ⟨1, Nat.one_mem_divisors.mpr (NeZero.ne n)⟩
  bot_le a := one_dvd a.1

instance (n : ℕ) [NeZero n] : OrderTop (Divisor n) where
  top := ⟨n, Nat.mem_divisors_self n (NeZero.ne n)⟩
  le_top a := Nat.dvd_of_mem_divisors a.2

@[simp] theorem bot_val (n : ℕ) [NeZero n] :
    ((⊥ : Divisor n) : ℕ) = 1 :=
  rfl

@[simp] theorem top_val (n : ℕ) [NeZero n] :
    ((⊤ : Divisor n) : ℕ) = n :=
  rfl

/-- The divisor poset is a concrete antisymmetric presentation of causal left
divisibility in the natural-number multiplication model. -/
def presentation (n : ℕ) :
    CausalIncidence.LeftDivisorPresentation ℕ (Divisor n) where
  realize := fun d => d.1
  realize_injective := Subtype.coe_injective
  le_iff_leftDivides := by
    intro a b
    constructor
    · intro hab
      rcases hab with ⟨c, hc⟩
      exact ⟨c, hc.symm⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, hc.symm⟩

/-- Mobius coefficient in the finite divisor poset of n. -/
def mobius (n : ℕ) :
    IncidenceAlgebra ℤ (Divisor n) :=
  (presentation n).mobius

/-- Incidence inversion on all divisors of a nonzero natural n. -/
theorem inversion
    (n : ℕ) [NeZero n]
    (f g : Divisor n → ℤ)
    (h : ∀ x, g x = ∑ y ∈ Finset.Iic x, f y)
    (x : Divisor n) :
    f x =
      ∑ y ∈ Finset.Iic x,
        mobius n y x * g y := by
  exact (presentation n).moebius_inversion f g h x

/-- The divisor-poset Mobius function is the inverse of incidence zeta. -/
theorem mobius_inverse_zeta
    (n : ℕ) :
    (presentation n).mobius * (presentation n).zeta = 1 := by
  exact (presentation n).mobius_mul_zeta

end NatDivisorIncidence
end CausalGeometry
