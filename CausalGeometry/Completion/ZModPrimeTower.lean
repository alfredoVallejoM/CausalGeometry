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

/-- Integer representatives of a compatible primary history. Level n+1
uses the canonical representative of the residue at tower level n; level
zero is the unique residue modulo one. -/
def historyIntSeq
    (h : (zmodPrimeTower p).CompatibleHistory) : ℕ → ℤ
  | 0 => 0
  | n + 1 => (h.at n).val

private theorem history_step_dvd
    (h : (zmodPrimeTower p).CompatibleHistory) (n : ℕ) :
    (p : ℤ) ^ (n + 1) ∣
      historyIntSeq p h (n + 2) - historyIntSeq p h (n + 1) := by
  letI : NeZero (p ^ (n + 1)) :=
    ⟨pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero⟩
  letI : NeZero (p ^ (n + 2)) :=
    ⟨pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero⟩
  have hc := h.compatible n
  change ZMod.cast (h.at (n + 1)) = h.at n at hc
  rw [← ZMod.natCast_zmod_val (h.at (n + 1)),
    ZMod.cast_natCast (pow_dvd_pow p (Nat.le_succ (n + 1)))] at hc
  rw [← ZMod.natCast_zmod_val (h.at n)] at hc
  have hz :
      (((h.at n).val : ℤ) : ZMod (p ^ (n + 1))) =
        (((h.at (n + 1)).val : ℤ) : ZMod (p ^ (n + 1))) := by
    simpa only [Int.cast_natCast] using hc.symm
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hz

/-- Successive integer representatives are congruent modulo the previous
primary depth. -/
theorem historyIntSeq_pow_dvd_sub
    (h : (zmodPrimeTower p).CompatibleHistory) :
    ∀ i, (p : ℤ) ^ i ∣
      historyIntSeq p h (i + 1) - historyIntSeq p h i := by
  intro i
  cases i with
  | zero =>
      simp [historyIntSeq]
  | succ n =>
      simpa [historyIntSeq] using history_step_dvd p h n

/-- Reconstruct a p-adic integer from a coherent causal restriction history. -/
noncomputable def toPadicInt
    (h : (zmodPrimeTower p).CompatibleHistory) : ℤ_[p] :=
  PadicInt.ofIntSeq (historyIntSeq p h)
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
      (historyIntSeq p h) p (historyIntSeq_pow_dvd_sub p h))

/-- Reconstruction has exactly the prescribed finite restrictions. -/
theorem toZModPow_toPadicInt
    (h : (zmodPrimeTower p).CompatibleHistory) (n : ℕ) :
    PadicInt.toZModPow (n + 1) (toPadicInt p h) = h.at n := by
  letI : NeZero (p ^ (n + 1)) :=
    ⟨pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero⟩
  have hs :=
    PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub
      (historyIntSeq p h) p (historyIntSeq_pow_dvd_sub p h) (n + 1)
  simpa [toPadicInt, historyIntSeq, ZMod.natCast_zmod_val] using hs

/-- Every coherent finite-restriction history comes from a p-adic integer. -/
theorem ofPadicInt_toPadicInt
    (h : (zmodPrimeTower p).CompatibleHistory) :
    ofPadicInt p (toPadicInt p h) = h := by
  apply InverseTower.CompatibleHistory.ext
  funext n
  exact toZModPow_toPadicInt p h n

/-- Reconstructing a p-adic integer from its full restriction history returns
the original p-adic integer. -/
theorem toPadicInt_ofPadicInt (x : ℤ_[p]) :
    toPadicInt p (ofPadicInt p x) = x := by
  apply ofPadicInt_injective p
  exact ofPadicInt_toPadicInt p (ofPadicInt p x)

/-- Causal coherent histories through the primary ZMod tower are exactly the
p-adic integers. -/
noncomputable def compatibleHistoryEquivPadicInt :
    (zmodPrimeTower p).CompatibleHistory ≃ ℤ_[p] where
  toFun := toPadicInt p
  invFun := ofPadicInt p
  left_inv := ofPadicInt_toPadicInt p
  right_inv := toPadicInt_ofPadicInt p

end zmodPrimeTower
end CausalGeometry
