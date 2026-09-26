import CausalGeometry.Number.MathlibOreBridge
import Mathlib.Algebra.Group.End
import Mathlib.Tactic

namespace CausalGeometry
namespace Models
namespace OreWithoutReversibility

/-- Full endofunction monoid of the natural numbers. -/
abbrev NatEnd :=
  Function.End ℕ

/-- The unilateral shift. -/
def shift : NatEnd :=
  Nat.succ

/-- Denominators are exactly nonnegative powers of the shift. -/
def shiftPowers :
    Submonoid NatEnd :=
  Submonoid.powers shift

@[simp] theorem shift_pow_apply
    (k n : ℕ) :
    (shift ^ k) n = n + k := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [pow_succ]
      change
        (shift ^ k) (shift n) =
          n + (k + 1)
      rw [ih]
      simp [shift]
      omega

/-- Extend an arbitrary function backwards across k applications of shift.

Values below k are irrelevant because they are never observed after
precomposition with shift^k. -/
def backExtend
    (f : NatEnd)
    (k : ℕ) :
    NatEnd :=
  fun n =>
    if h : k ≤ n
    then f (n - k)
    else 0

/-- Back-extension is a genuine right division by shift^k at the level of raw
endofunctions. -/
theorem backExtend_mul_shiftPow
    (f : NatEnd)
    (k : ℕ) :
    backExtend f k * shift ^ k = f := by
  funext n
  change
    backExtend f k ((shift ^ k) n) =
      f n
  rw [shift_pow_apply]
  simp [backExtend]

/-- Every selected denominator is literally one power of shift. -/
theorem shiftPowers_exists_pow
    (s : shiftPowers) :
    ∃ k : ℕ,
      shift ^ k = (s : NatEnd) := by
  simpa [shiftPowers, Submonoid.mem_powers_iff]
    using s.property

/-- Raw left Ore condition holds.

For a/s, choose denominator witness 1 and extend the numerator backwards
through the shift power represented by s. -/
theorem leftOreCondition :
    CausalLocalization.LeftOreCondition
      shiftPowers := by
  intro f s
  rcases shiftPowers_exists_pow s with
    ⟨k, hk⟩
  refine ⟨{
    numerator := backExtend f k
    denominator := 1
    cross := ?_
  }⟩
  change
    f =
      backExtend f k * (s : NatEnd)
  rw [← hk]
  exact
    (backExtend_mul_shiftPow f k).symm

/-- First test function: constantly zero. -/
def sourceA : NatEnd :=
  fun _ => 0

/-- Second test function: differs from sourceA only at zero. -/
def sourceB : NatEnd
  | 0 => 1
  | _ + 1 => 0

theorem sourceA_ne_sourceB :
    sourceA ≠ sourceB := by
  intro h
  have h0 := congrFun h 0
  norm_num [sourceA, sourceB] at h0

/-- The selected denominator shift itself. -/
def shiftDenominator :
    shiftPowers :=
  ⟨shift, Submonoid.mem_powers shift⟩

/-- Right multiplication by shift forgets the value at zero, so the two test
functions become equal. -/
theorem source_mul_shift_eq :
    sourceA * (shiftDenominator : NatEnd)
      =
    sourceB * (shiftDenominator : NatEnd) := by
  funext n
  simp [sourceA, sourceB,
    shiftDenominator, shift,
    Function.comp_def]

/-- Left multiplication by any selected denominator never equalizes the two
test functions: a power of shift preserves their one-unit output difference at
input zero. -/
theorem no_selected_left_equalizer
    (t : shiftPowers) :
    (t : NatEnd) * sourceA
      ≠
    (t : NatEnd) * sourceB := by
  rcases shiftPowers_exists_pow t with
    ⟨k, hk⟩
  intro h
  have h0 := congrFun h 0
  rw [← hk] at h0
  change
    (shift ^ k) (sourceA 0) =
      (shift ^ k) (sourceB 0)
    at h0
  simp [sourceA, sourceB,
    shift_pow_apply] at h0

/-- The extra reversibility/cancellation law required by mathlib OreSet fails
for the same denominator system. -/
theorem reversibility_fails :
    ¬
    (∀ (a b : NatEnd)
      (s : shiftPowers),
      a * (s : NatEnd) =
          b * (s : NatEnd) →
      ∃ t : shiftPowers,
        (t : NatEnd) * a =
          (t : NatEnd) * b) := by
  intro h
  rcases
      h sourceA sourceB shiftDenominator
        source_mul_shift_eq with
    ⟨t, ht⟩
  exact no_selected_left_equalizer t ht

/-- Therefore raw left Ore does not imply a certified OreSet.

This is the mutation control needed by CA22: any theorem that silently turns
LeftOreCondition into OreSet would contradict this concrete model. -/
theorem no_mathlibOreSet :
    ¬ Nonempty
      (OreLocalization.OreSet
        shiftPowers) := by
  rintro ⟨inst⟩
  letI : OreLocalization.OreSet
      shiftPowers := inst
  rcases
      OreLocalization.ore_right_cancel
        sourceA sourceB
        shiftDenominator
        source_mul_shift_eq with
    ⟨t, ht⟩
  exact no_selected_left_equalizer t ht

/-- One packaged discriminator: the raw Ore hypothesis is true while the
certified localization hypothesis is false. -/
theorem rawOre_not_certified :
    CausalLocalization.LeftOreCondition
        shiftPowers
      ∧
    ¬ CausalLocalization.MathlibLeftOreCertified
        shiftPowers :=
  ⟨leftOreCondition, no_mathlibOreSet⟩

end OreWithoutReversibility
end Models
end CausalGeometry
