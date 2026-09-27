import CausalGeometry.Completion.PrimePowerTower
import Mathlib.Tactic

namespace CausalGeometry
namespace Models
namespace PrimePowerTowerControls

/-- A minimal finite inverse tower with residue cardinal four.

Only the certified finite cardinal law is used by the PrimePowerPrimary layer;
the reduction map is the canonical remainder map. -/
def binaryQuadraticTower :
    FiniteInverseTower where
  Obj := fun n =>
    Fin (4 ^ (n + 1))

  drop := fun n x =>
    ⟨x.val % (4 ^ (n + 1)), by
      apply Nat.mod_lt
      positivity⟩

  finite := fun _ =>
    inferInstance

/-- The tower is primary with q=4. -/
def binaryQuadraticPrimary :
    binaryQuadraticTower.PrimePowerPrimary where
  q := 4
  q_ge_two := by
    norm_num
  card_law := by
    intro n
    simp [
      FiniteInverseTower.card,
      binaryQuadraticTower
    ]
  p := 2
  f := 2
  p_prime := Nat.prime_two
  f_pos := by
    norm_num
  q_eq := by
    norm_num

theorem binaryQuadratic_q :
    binaryQuadraticPrimary.toPrimary.q = 4 := by
  rfl

theorem binaryQuadratic_p :
    binaryQuadraticPrimary.p = 2 := by
  rfl

theorem binaryQuadratic_f :
    binaryQuadraticPrimary.f = 2 := by
  rfl

theorem binaryQuadratic_primePower :
    binaryQuadraticPrimary.toPrimary.q =
      binaryQuadraticPrimary.p ^
        binaryQuadraticPrimary.f :=
  binaryQuadraticPrimary.q_eq

/-- Nontrivial depth regression: level one has 4^2 = 16 states. -/
theorem binaryQuadratic_level_one_card :
    binaryQuadraticTower.card 1 = 16 := by
  rw [binaryQuadraticPrimary.card_law_primePower]
  norm_num

/-- Stable source consumer for the p=2,f=2,q=4 finite-field provenance. -/
def Consumer : Prop :=
  binaryQuadraticPrimary.p = 2 ∧
    binaryQuadraticPrimary.f = 2 ∧
    binaryQuadraticPrimary.toPrimary.q = 4 ∧
    binaryQuadraticPrimary.toPrimary.q =
      binaryQuadraticPrimary.p ^
        binaryQuadraticPrimary.f ∧
    binaryQuadraticTower.card 1 = 16

theorem consumer : Consumer :=
  ⟨binaryQuadratic_p,
    binaryQuadratic_f,
    binaryQuadratic_q,
    binaryQuadratic_primePower,
    binaryQuadratic_level_one_card⟩

end PrimePowerTowerControls
end Models
end CausalGeometry
