namespace CausalGeometry

universe u v

/-- Abstract primitive-cycle decomposition.  This is intentionally independent
of compositional primality and of arithmetic primes. -/
structure PrimitiveOrbitSystem where
  Cycle : Type u
  Primitive : Type v
  iterate : Primitive → ℕ → Cycle
  root : Cycle → Primitive
  period : Cycle → ℕ
  period_pos : ∀ c, 0 < period c
  root_iterate : ∀ p n, root (iterate p n) = p
  reconstruct : ∀ c, iterate (root c) (period c) = c

namespace PrimitiveOrbitSystem

variable (P : PrimitiveOrbitSystem)

def IsPrimitiveCycle (c : P.Cycle) : Prop :=
  P.period c = 1

theorem root_reconstruct (c : P.Cycle) :
    P.root (P.iterate (P.root c) (P.period c)) = P.root c := by
  rw [P.reconstruct]

/-- Primitive data is stable under iteration by construction. -/
theorem root_of_iterate (p : P.Primitive) (n : ℕ) :
    P.root (P.iterate p n) = p :=
  P.root_iterate p n

end PrimitiveOrbitSystem
end CausalGeometry
