import CausalGeometry.Completion.InverseTower
import Mathlib.Data.Fintype.Card

namespace CausalGeometry

universe u

/-- An inverse tower with certified finite levels. -/
structure FiniteInverseTower extends InverseTower where
  finite : ∀ n, Fintype (Obj n)

namespace FiniteInverseTower

variable (T : FiniteInverseTower)

def card (n : ℕ) : ℕ :=
  @Fintype.card (T.Obj n) (T.finite n)

/-- A primary tower with residue cardinal q.  Level n represents depth n+1,
so the expected cardinality is q^(n+1). -/
structure Primary where
  q : ℕ
  q_ge_two : 2 ≤ q
  card_law : ∀ n, T.card n = q ^ (n + 1)

namespace Primary

variable {T : FiniteInverseTower} (P : T.Primary)

theorem card_zero : T.card 0 = P.q := by
  simpa using P.card_law 0

theorem card_succ (n : ℕ) :
    T.card (n + 1) = P.q ^ (n + 2) := by
  simpa [Nat.add_assoc] using P.card_law (n + 1)

end Primary
end FiniteInverseTower
end CausalGeometry
