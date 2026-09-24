import CausalGeometry.Completion.FiniteLocalRingTower
import CausalGeometry.Completion.ZModPrimeTower
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.LocalRing.RingHom.Basic

namespace CausalGeometry

namespace zmodPrimeLocalTower

variable (p : ℕ) [Fact p.Prime]

/-- Every modulus p^(n+1) is nonzero for prime p. -/
instance levelNeZero (n : ℕ) :
    NeZero (p ^ (n + 1)) :=
  ⟨pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero⟩

/-- Z/p^(n+1)Z is local because it is a nontrivial surjective image of the
local ring of p-adic integers. -/
instance levelIsLocalRing (n : ℕ) :
    IsLocalRing (ZMod (p ^ (n + 1))) := by
  let f : ℤ_[p] →+* ZMod (p ^ (n + 1)) :=
    PadicInt.toZModPow (n + 1)
  exact IsLocalRing.of_surjective f
    (ZMod.ringHom_surjective f)

/-- Ring-hom reduction from depth n+1 to depth n. -/
def drop (n : ℕ) :
    ZMod (p ^ (n + 2)) →+*
      ZMod (p ^ (n + 1)) :=
  ZMod.castHom
    (pow_dvd_pow p (Nat.le_succ (n + 1)))
    (ZMod (p ^ (n + 1)))

@[simp] theorem drop_apply
    (n : ℕ)
    (x : ZMod (p ^ (n + 2))) :
    drop p n x = ZMod.cast x := rfl

theorem drop_surjective (n : ℕ) :
    Function.Surjective (drop p n) :=
  ZMod.ringHom_surjective (drop p n)

/-- Concrete finite local-ring tower underlying the standard p-adic
restriction tower. -/
def localTower :
    FiniteLocalRingTower
      (fun n => ZMod (p ^ (n + 1))) where
  drop := drop p
  drop_surjective := drop_surjective p

/-- Prime-power enhancement. Here residue degree f=1 and q=p. -/
def primePowerTower :
    PrimePowerLocalRingTower
      (fun n => ZMod (p ^ (n + 1))) where
  drop := drop p
  drop_surjective := drop_surjective p
  p := p
  f := 1
  p_prime := Fact.out
  f_pos := by decide
  card_law := by
    intro n
    simp [ZMod.card]

@[simp] theorem primePowerTower_q :
    (primePowerTower p).q = p := by
  simp [PrimePowerLocalRingTower.q, primePowerTower]

/-- The ring-hom tower forgets to exactly the same restriction operation as the
existing ZMod primary inverse tower. -/
@[simp] theorem inverseTower_drop_agrees
    (n : ℕ)
    (x : ZMod (p ^ (n + 2))) :
    (localTower p).toInverseTower.drop n x =
      (zmodPrimeTower p).drop n x := rfl

/-- Thus every compatible history for the local-ring tower can be read
levelwise as the already established p-adic residue history. -/
def toZModHistory
    (h : (localTower p).toInverseTower.CompatibleHistory) :
    (zmodPrimeTower p).CompatibleHistory where
  at := h.at
  compatible := h.compatible

/-- Conversely every existing ZMod primary history is a local-ring tower
history. -/
def ofZModHistory
    (h : (zmodPrimeTower p).CompatibleHistory) :
    (localTower p).toInverseTower.CompatibleHistory where
  at := h.at
  compatible := h.compatible

@[simp] theorem toZModHistory_ofZModHistory
    (h : (zmodPrimeTower p).CompatibleHistory) :
    toZModHistory p (ofZModHistory p h) = h := by
  apply InverseTower.CompatibleHistory.eq_of_at_eq
  intro n
  rfl

@[simp] theorem ofZModHistory_toZModHistory
    (h : (localTower p).toInverseTower.CompatibleHistory) :
    ofZModHistory p (toZModHistory p h) = h := by
  apply InverseTower.CompatibleHistory.eq_of_at_eq
  intro n
  rfl

/-- The two compatible-history types are therefore equivalent, and the
previous p-adic reconstruction theorem applies unchanged. -/
def compatibleHistoryEquiv :
    (localTower p).toInverseTower.CompatibleHistory ≃
      (zmodPrimeTower p).CompatibleHistory where
  toFun := toZModHistory p
  invFun := ofZModHistory p
  left_inv := ofZModHistory_toZModHistory p
  right_inv := toZModHistory_ofZModHistory p

/-- Concrete local-ring histories are exactly p-adic integers by composition
with the already proved ZMod inverse-limit equivalence. -/
noncomputable def compatibleHistoryEquivPadicInt :
    (localTower p).toInverseTower.CompatibleHistory ≃
      ℤ_[p] :=
  (compatibleHistoryEquiv p).trans
    (zmodPrimeTower.compatibleHistoryEquivPadicInt p)

end zmodPrimeLocalTower
end CausalGeometry
