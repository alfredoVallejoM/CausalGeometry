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

theorem irreducible_iff_no_nontrivial_factorization (p : α) :
    Irreducible p ↔
      ¬ ∃ a b, NontrivialFactorization p a b := by
  constructor
  · intro hp h
    rcases h with ⟨a, b, hab, ha, hb⟩
    exact (hp.2 a b hab) |>.elim ha hb
  · intro h
    constructor
    · intro hpunit
      apply h
      exact ⟨1, p, by simp, by
        intro hone
        exact hpunit (by
          rcases hone with ⟨u, hu, uh⟩
          exact ⟨u * p, by simp [mul_assoc, uh], by simpa [mul_assoc] using congrArg (fun z => z * p) hu⟩), hpunit⟩
    · intro a b hab
      by_contra hn
      push_neg at hn
      exact h ⟨a, b, hab, hn.1, hn.2⟩

end CausalPrime
end CausalGeometry
