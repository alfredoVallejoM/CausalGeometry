import CausalGeometry.Completion.FinitePrimaryTower
import CausalGeometry.Completion.SharedDepth
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

/-- The same residue tower packaged with its finite-level structure. -/
def finiteTower : FiniteInverseTower where
  Obj n := ZMod (p ^ (n + 1))
  drop n := fun x => ZMod.cast x
  finite n := by
    letI : NeZero (p ^ (n + 1)) :=
      ⟨pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero⟩
    infer_instance

/-- A prime residue tower is a primary finite tower with residue cardinal p. -/
def primaryTower : (finiteTower p).Primary where
  q := p
  q_ge_two := (Fact.out : Nat.Prime p).two_le
  card_law := by
    intro n
    letI : NeZero (p ^ (n + 1)) :=
      ⟨pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero⟩
    simp [finiteTower, FiniteInverseTower.card, ZMod.card]

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
  apply InverseTower.CompatibleHistory.eq_of_at_eq
  intro n
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

/-- Agreement of p-adic histories at depth n is exactly equality modulo
p^(n+1), hence exactly a p-adic norm bound. -/
theorem agreeAt_ofPadicInt_iff_norm_sub_le
    (x y : ℤ_[p]) (n : ℕ) :
    (zmodPrimeTower p).AgreeAt
        (ofPadicInt p x) (ofPadicInt p y) n ↔
      ‖x - y‖ ≤
        (p : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
  change
    PadicInt.toZModPow (n + 1) x =
        PadicInt.toZModPow (n + 1) y ↔ _
  constructor
  · intro hxy
    apply
      (PadicInt.norm_le_pow_iff_mem_span_pow
        (x - y) (n + 1)).2
    rw [← PadicInt.ker_toZModPow (p := p) (n + 1)]
    rw [RingHom.mem_ker, map_sub, hxy, sub_self]
  · intro hnorm
    have hmem :
        x - y ∈
          (Ideal.span {(p : ℤ_[p]) ^ (n + 1)} :
            Ideal ℤ_[p]) :=
      (PadicInt.norm_le_pow_iff_mem_span_pow
        (x - y) (n + 1)).1 hnorm
    rw [← PadicInt.ker_toZModPow (p := p) (n + 1)] at hmem
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hmem
    exact hmem

/-- Agreement through all restrictions up to n is the same p-adic norm
condition because compatible histories are nested. -/
theorem agreeThrough_ofPadicInt_iff_norm_sub_le
    (x y : ℤ_[p]) (n : ℕ) :
    (zmodPrimeTower p).AgreeThrough
        (ofPadicInt p x) (ofPadicInt p y) n ↔
      ‖x - y‖ ≤
        (p : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
  rw [InverseTower.agreeThrough_iff_agreeAt]
  exact agreeAt_ofPadicInt_iff_norm_sub_le p x y n

/-- The metric ball description is therefore the numerical realization of
causal shared restriction depth. -/
theorem agreeThrough_ofPadicInt_iff_dist_le
    (x y : ℤ_[p]) (n : ℕ) :
    (zmodPrimeTower p).AgreeThrough
        (ofPadicInt p x) (ofPadicInt p y) n ↔
      dist x y ≤
        (p : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
  simpa [dist_eq_norm] using
    agreeThrough_ofPadicInt_iff_norm_sub_le p x y n

end zmodPrimeTower
end CausalGeometry
