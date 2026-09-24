import CausalGeometry.Completion.FiniteLocalRingTower

namespace CausalGeometry

universe u

/-- A certified Bruhat--Tits branching profile for a prime-power local-ring
tower.

The local-ring and prime-power cardinal laws do not by themselves imply these
projective-line cardinalities.  They are explicit theorem obligations for the
DVR/local-field realization.

Level n represents P¹(A_n).  The expected sphere cardinality is
(q + 1) * q^n, and each reduction fiber from level n+1 to level n has q
elements. -/
structure BruhatTitsBranchingContract
    {A : ℕ → Type u}
    [∀ n, CommRing (A n)]
    [∀ n, IsLocalRing (A n)]
    [∀ n, Fintype (A n)]
    (T : PrimePowerLocalRingTower A) where

  projective_card :
    ∀ n,
      Nat.card (LocalProjectivePair.Line (A n)) =
        (T.q + 1) * T.q ^ n

  reduction_fiber_card :
    ∀ n (y : LocalProjectivePair.Line (A n)),
      Nat.card
        {x : LocalProjectivePair.Line (A (n + 1)) //
          LocalProjectivePair.map (T.drop n) x = y} =
        T.q

namespace BruhatTitsBranchingContract

variable
    {A : ℕ → Type u}
    [∀ n, CommRing (A n)]
    [∀ n, IsLocalRing (A n)]
    [∀ n, Fintype (A n)]
    {T : PrimePowerLocalRingTower A}
    (B : BruhatTitsBranchingContract T)

theorem projective_card_zero :
    Nat.card (LocalProjectivePair.Line (A 0)) =
      T.q + 1 := by
  simpa using B.projective_card 0

theorem projective_card_succ (n : ℕ) :
    Nat.card (LocalProjectivePair.Line (A (n + 1))) =
      T.q *
        Nat.card (LocalProjectivePair.Line (A n)) := by
  rw [B.projective_card (n + 1), B.projective_card n]
  simp [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- The projective reduction tower is the sphere tower predicted by a rooted
(q+1)-regular Bruhat--Tits tree once the branching contract is certified. -/
def sphereTower : InverseTower :=
  T.projectiveLineTower

@[simp] theorem sphereTower_drop
    (n : ℕ)
    (x : LocalProjectivePair.Line (A (n + 1))) :
    B.sphereTower.drop n x =
      LocalProjectivePair.map (T.drop n) x := rfl

end BruhatTitsBranchingContract

/-- External Bruhat--Tits target presented as a depth-indexed inverse tower.

CausalGeometry does not define the target tree by fiat.  A consumer supplies
its sphere types and parent maps, then proves a levelwise equivalence with the
projective restriction tower. -/
structure BruhatTitsTarget where
  Sphere : ℕ → Type u
  parent : ∀ n, Sphere (n + 1) → Sphere n

namespace BruhatTitsTarget

def toInverseTower (B : BruhatTitsTarget.{u}) : InverseTower where
  Obj := B.Sphere
  drop := B.parent

end BruhatTitsTarget

/-- Typed comparison between a local projective tower and an independently
constructed Bruhat--Tits target. -/
structure BruhatTitsComparison
    {A : ℕ → Type u}
    [∀ n, CommRing (A n)]
    [∀ n, IsLocalRing (A n)]
    [∀ n, Fintype (A n)]
    (T : FiniteLocalRingTower A)
    (B : BruhatTitsTarget.{u}) where
  levelEquiv :
    ∀ n,
      LocalProjectivePair.Line (A n) ≃ B.Sphere n

  parent_compat :
    ∀ n (x : LocalProjectivePair.Line (A (n + 1))),
      levelEquiv n
        (LocalProjectivePair.map (T.drop n) x) =
      B.parent n (levelEquiv (n + 1) x)

namespace BruhatTitsComparison

variable
    {A : ℕ → Type u}
    [∀ n, CommRing (A n)]
    [∀ n, IsLocalRing (A n)]
    [∀ n, Fintype (A n)]
    {T : FiniteLocalRingTower A}
    {B : BruhatTitsTarget.{u}}
    (C : BruhatTitsComparison T B)

/-- A coherent projective history maps to a coherent ray in the external
Bruhat--Tits target. -/
def mapHistory
    (h : T.projectiveLineTower.CompatibleHistory) :
    B.toInverseTower.CompatibleHistory where
  at n := C.levelEquiv n (h.at n)
  compatible := by
    intro n
    rw [← C.parent_compat]
    exact congrArg (C.levelEquiv n) (h.compatible n)

/-- Levelwise equivalences make the comparison injective on completed rays. -/
theorem mapHistory_injective :
    Function.Injective C.mapHistory := by
  intro x y hxy
  apply InverseTower.CompatibleHistory.eq_of_at_eq
  intro n
  apply (C.levelEquiv n).injective
  exact congrArg
    (fun h : B.toInverseTower.CompatibleHistory => h.at n)
    hxy

end BruhatTitsComparison
end CausalGeometry
