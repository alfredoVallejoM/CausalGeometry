import CausalGeometry.Completion.BruhatTitsContract
import CausalGeometry.Completion.DVRResidueTower
import CausalGeometry.Completion.LocalProjectiveFibers
import CausalGeometry.Completion.ZModProjectiveLine
import CausalGeometry.Completion.ZModReductionFiber
import Mathlib.RingTheory.LocalRing.RingHom.Basic

namespace CausalGeometry

namespace zmodPrimeLocalTower

variable (p : ℕ) [Fact p.Prime]

/-- Every modular reduction in the prime-power tower is a local ring hom. -/
noncomputable instance dropIsLocalHom (n : ℕ) :
    IsLocalHom (drop p n) :=
  IsLocalHom.of_surjective
    (drop p n)
    (drop_surjective p n)

/-- A projective reduction fiber is canonically equivalent to one ordinary
modular-reduction fiber selected by the target point's chart coordinate. -/
noncomputable def projectiveFiberEquivReductionFiber
    (n : ℕ)
    (q : LocalProjectivePair.Line
      (ZMod (p ^ (n + 1)))) :
    {x : LocalProjectivePair.Line
        (ZMod (p ^ (n + 2))) //
      LocalProjectivePair.map (drop p n) x = q} ≃
      {x : ZMod (p ^ (n + 2)) //
        drop p n x =
          LocalProjectivePair.chartValue
            ((LocalProjectivePair.chartEquiv
              (R := ZMod (p ^ (n + 1)))).symm q)} :=
  LocalProjectivePair.projectiveFiberEquivRingFiber
    (drop p n) q

/-- Every point of P¹(Z/p^(n+1)Z) has exactly p lifts one level deeper. -/
theorem projective_drop_fiber_natCard
    (n : ℕ)
    (q : LocalProjectivePair.Line
      (ZMod (p ^ (n + 1)))) :
    Nat.card
        {x : LocalProjectivePair.Line
            (ZMod (p ^ (n + 2))) //
          LocalProjectivePair.map (drop p n) x = q} =
      p := by
  rw [Nat.card_congr
    (projectiveFiberEquivReductionFiber p n q)]
  exact drop_fiber_natCard p n
    (LocalProjectivePair.chartValue
      ((LocalProjectivePair.chartEquiv
        (R := ZMod (p ^ (n + 1)))).symm q))

/-- The p-adic ZMod tower satisfies the generic finite DVR residue laws. -/
noncomputable def dvrResidueContract :
    DVRResidueTowerContract
      (primePowerTower p) where
  nonunit_card := by
    intro n
    rw [primePowerTower_q]
    exact nonunit_natCard p n
  reduction_fiber_card := by
    intro n y
    rw [primePowerTower_q]
    exact drop_fiber_natCard p n y

/-- The standard p-adic local-ring tower satisfies the full finite
Bruhat--Tits branching contract as a specialization of the generic q=p^f DVR
theorem. -/
noncomputable def bruhatTitsBranchingContract :
    BruhatTitsBranchingContract
      (primePowerTower p) :=
  (dvrResidueContract p).toBruhatTitsBranchingContract

end zmodPrimeLocalTower
end CausalGeometry
