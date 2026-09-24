import CausalGeometry.Completion.InverseTower
import CausalGeometry.Completion.FinitePrimaryTower
import CausalGeometry.Completion.LocalProjectiveLine
import Mathlib.RingTheory.LocalRing.Basic

namespace CausalGeometry

universe u

/-- A tower of finite commutative local rings with surjective reduction maps.

The level family and its typeclass structure are parameters rather than hidden
fields, so concrete DVR quotients can instantiate the interface directly. -/
structure FiniteLocalRingTower
    (A : ℕ → Type u)
    [∀ n, CommRing (A n)]
    [∀ n, IsLocalRing (A n)]
    [∀ n, Fintype (A n)] where
  drop : ∀ n, A (n + 1) →+* A n
  drop_surjective :
    ∀ n, Function.Surjective (drop n)

namespace FiniteLocalRingTower

variable
    {A : ℕ → Type u}
    [∀ n, CommRing (A n)]
    [∀ n, IsLocalRing (A n)]
    [∀ n, Fintype (A n)]
    (T : FiniteLocalRingTower A)

/-- Forget ring structure and retain the causal restriction tower. -/
def toInverseTower : InverseTower where
  Obj := A
  drop := fun n => T.drop n

/-- The same tower with certified finite levels. -/
def toFiniteInverseTower : FiniteInverseTower where
  Obj := A
  drop := fun n => T.drop n
  finite := fun _ => inferInstance

@[simp] theorem toInverseTower_drop
    (n : ℕ) (x : A (n + 1)) :
    T.toInverseTower.drop n x = T.drop n x := rfl

/-- Projective-line tower induced functorially by reduction of local rings. -/
def projectiveLineTower : InverseTower where
  Obj n := LocalProjectivePair.Line (A n)
  drop n := LocalProjectivePair.map (T.drop n)

/-- A compatible local-ring history restricts levelwise exactly through the
ring homomorphisms supplied by the tower. -/
def CompatibleRingHistory :=
  T.toInverseTower.CompatibleHistory

end FiniteLocalRingTower

/-- Prime-power residue data for a finite local-ring tower.

The cardinal law is stated on the actual local rings and can therefore be
consumed by DVR and Bruhat--Tits realizations without changing the underlying
inverse-tower theory. -/
structure PrimePowerLocalRingTower
    (A : ℕ → Type u)
    [∀ n, CommRing (A n)]
    [∀ n, IsLocalRing (A n)]
    [∀ n, Fintype (A n)]
    extends FiniteLocalRingTower A where
  p : ℕ
  f : ℕ
  p_prime : p.Prime
  f_pos : 0 < f
  card_law :
    ∀ n, Fintype.card (A n) =
      p ^ (f * (n + 1))

namespace PrimePowerLocalRingTower

variable
    {A : ℕ → Type u}
    [∀ n, CommRing (A n)]
    [∀ n, IsLocalRing (A n)]
    [∀ n, Fintype (A n)]
    (T : PrimePowerLocalRingTower A)

def q : ℕ :=
  T.p ^ T.f

theorem q_ge_two :
    2 ≤ T.q := by
  have hp : 2 ≤ T.p := T.p_prime.two_le
  have hf : T.f ≠ 0 := Nat.ne_of_gt T.f_pos
  have hp_pow : T.p ≤ T.p ^ T.f :=
    Nat.le_pow hf
  exact hp.trans hp_pow

theorem card_law_q (n : ℕ) :
    Fintype.card (A n) =
      T.q ^ (n + 1) := by
  rw [T.card_law n]
  simp [q, pow_mul]

/-- Recover the abstract prime-power primary tower used by the existing
completion API. -/
def toPrimePowerPrimary :
    (T.toFiniteInverseTower).PrimePowerPrimary where
  q := T.q
  q_ge_two := T.q_ge_two
  card_law := T.card_law_q
  p := T.p
  f := T.f
  p_prime := T.p_prime
  f_pos := T.f_pos
  q_eq := rfl

end PrimePowerLocalRingTower
end CausalGeometry
