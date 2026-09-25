import CausalGeometry.Completion.BruhatTitsContract
import CausalGeometry.Completion.LocalProjectiveCharts
import CausalGeometry.Completion.LocalProjectiveFibers
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Tactic

namespace CausalGeometry

universe u

/-- Finite-level DVR residue contract for a prime-power local-ring tower.

The tower already knows |A_n| = q^(n+1).  The genuinely valuation-theoretic
input needed for Bruhat--Tits branching is:
* the non-unit/maximal-ideal part has q^n elements;
* every reduction fiber has q elements.

These two statements are enough to derive the projective sphere and branching
laws for arbitrary residue cardinal q=p^f. -/
structure DVRResidueTowerContract
    {A : ℕ → Type u}
    [∀ n, CommRing (A n)]
    [∀ n, IsLocalRing (A n)]
    [∀ n, Fintype (A n)]
    (T : PrimePowerLocalRingTower A) where

  nonunit_card :
    ∀ n,
      Nat.card
          (LocalProjectivePair.Nonunit
            (A n)) =
        T.q ^ n

  reduction_fiber_card :
    ∀ n (y : A n),
      Nat.card
          {x : A (n + 1) //
            T.drop n x = y} =
        T.q

namespace DVRResidueTowerContract

variable
    {A : ℕ → Type u}
    [∀ n, CommRing (A n)]
    [∀ n, IsLocalRing (A n)]
    [∀ n, Fintype (A n)]
    {T : PrimePowerLocalRingTower A}
    (D : DVRResidueTowerContract T)

/-- The unit group at level n has cardinal q^(n+1)-q^n. -/
theorem unit_natCard (n : ℕ) :
    Nat.card (A n)ˣ =
      T.q ^ (n + 1) - T.q ^ n := by
  have hpartition :=
    LocalProjectivePair.natCard_nonunit
      (R := A n)
  rw [D.nonunit_card n,
    T.card_law_q n] at hpartition
  omega

/-- More familiar DVR form |A_n^×|=(q-1)q^n. -/
theorem unit_natCard_factorized (n : ℕ) :
    Nat.card (A n)ˣ =
      (T.q - 1) * T.q ^ n := by
  rw [D.unit_natCard n]
  rw [pow_succ]
  have hq : 1 ≤ T.q :=
    (T.q_ge_two).trans' (by decide)
  omega

/-- Projective sphere cardinal follows from the two local charts. -/
theorem projective_card (n : ℕ) :
    Nat.card
        (LocalProjectivePair.Line (A n)) =
      (T.q + 1) * T.q ^ n := by
  calc
    Nat.card
        (LocalProjectivePair.Line (A n))
        =
      Fintype.card (A n) +
        Nat.card
          (LocalProjectivePair.Nonunit
            (A n)) :=
      LocalProjectivePair.natCard_line
    _ =
      T.q ^ (n + 1) +
        T.q ^ n := by
      rw [T.card_law_q n,
        D.nonunit_card n]
    _ =
      (T.q + 1) * T.q ^ n := by
      rw [pow_succ]
      ring

/-- Reduction maps in the tower are local homomorphisms because they are
surjective between local rings. -/
noncomputable instance dropIsLocalHom (n : ℕ) :
    IsLocalHom (T.drop n) :=
  IsLocalHom.of_surjective
    (T.drop n)
    (T.drop_surjective n)

/-- Projectivization preserves each reduction-fiber cardinal. -/
theorem projective_reduction_fiber_card
    (n : ℕ)
    (y : LocalProjectivePair.Line (A n)) :
    Nat.card
        {x : LocalProjectivePair.Line
            (A (n + 1)) //
          LocalProjectivePair.map
            (T.drop n) x = y} =
      T.q := by
  rw [Nat.card_congr
    (LocalProjectivePair.projectiveFiberEquivRingFiber
      (T.drop n) y)]
  exact
    D.reduction_fiber_card n
      (LocalProjectivePair.chartValue
        ((LocalProjectivePair.chartEquiv
          (R := A n)).symm y))

/-- Any certified finite DVR residue tower therefore produces the full
Bruhat--Tits branching contract, uniformly for q=p^f. -/
noncomputable def toBruhatTitsBranchingContract :
    BruhatTitsBranchingContract T where
  projective_card :=
    D.projective_card
  reduction_fiber_card :=
    D.projective_reduction_fiber_card

end DVRResidueTowerContract
end CausalGeometry
