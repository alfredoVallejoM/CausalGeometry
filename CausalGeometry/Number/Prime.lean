import CausalGeometry.Number.Divisibility

namespace CausalGeometry

universe u

namespace CausalPrime

open CausalDivisibility

variable {α : Type u} [Monoid α]

/-- Compositional irreducibility.  This is deliberately distinct from cyclic
primitivity and from primality of a classical arithmetic shadow. -/
def Irreducible (p : α) : Prop :=
  ¬ IsCausalUnit p ∧
    ∀ a b, a * b = p → IsCausalUnit a ∨ IsCausalUnit b

theorem not_unit {p : α} (hp : Irreducible p) :
    ¬ IsCausalUnit p :=
  hp.1

/-- A factorization is nontrivial when neither factor is a causal unit. -/
def NontrivialFactorization (x a b : α) : Prop :=
  a * b = x ∧ ¬ IsCausalUnit a ∧ ¬ IsCausalUnit b

theorem no_nontrivial_factorization {p : α} (hp : Irreducible p) :
    ¬ ∃ a b, NontrivialFactorization p a b := by
  rintro ⟨a, b, hab, ha, hb⟩
  rcases hp.2 a b hab with hua | hub
  · exact ha hua
  · exact hb hub

end CausalPrime
end CausalGeometry
