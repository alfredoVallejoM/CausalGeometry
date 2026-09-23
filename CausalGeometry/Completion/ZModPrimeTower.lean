import CausalGeometry.Completion.InverseTower
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.SetTheory.Cardinal.Finite

namespace CausalGeometry

/-- The primary inverse tower of residue rings
\(\mathbb Z/p^{n+1}\mathbb Z\). -/
def zmodPrimeTower (p : ℕ) : InverseTower where
  Obj n := ZMod (p ^ (n + 1))
  drop n := fun x => ZMod.cast x

@[simp] theorem zmodPrimeTower_natCard (p n : ℕ) :
    Nat.card ((zmodPrimeTower p).Obj n) = p ^ (n + 1) := by
  simp [zmodPrimeTower, Nat.card_zmod]

namespace zmodPrimeTower

variable (p : ℕ) [Fact p.Prime]

/-- Every p-adic integer determines a coherent history through the finite
primary restriction tower. -/
def ofPadicInt (x : ℤ_[p]) :
    (zmodPrimeTower p).CompatibleHistory where
  at n := PadicInt.toZModPow (n + 1) x
  compatible n := by
    exact PadicInt.cast_toZModPow (n + 1) (n + 2)
      (Nat.le_succ (n + 1)) x

@[simp] theorem ofPadicInt_at (x : ℤ_[p]) (n : ℕ) :
    (ofPadicInt p x).at n = PadicInt.toZModPow (n + 1) x := rfl

/-- The full family of finite restrictions separates p-adic integers. -/
theorem ofPadicInt_injective :
    Function.Injective (ofPadicInt p) := by
  intro x y hxy
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  cases n with
  | zero =>
      simp
  | succ n =>
      have hlevel := congrArg
        (fun h : (zmodPrimeTower p).CompatibleHistory => h.at n) hxy
      simpa [ofPadicInt] using hlevel

end zmodPrimeTower
end CausalGeometry
