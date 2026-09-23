import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing

namespace CausalGeometry

namespace CausalCRT

/-- Two independent coprime restriction channels reconstruct the combined
residue ring. -/
def twoChannel {m n : ℕ} (h : m.Coprime n) :
    ZMod (m * n) ≃+* ZMod m × ZMod n :=
  ZMod.chineseRemainder h

/-- Finite independent coprime channels.  Later causal primary decomposition
theorems will map into this native arithmetic equivalence. -/
def finiteChannels {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (h : Pairwise (Nat.Coprime on a)) :
    ZMod (∏ i, a i) ≃+* (∀ i, ZMod (a i)) :=
  ZMod.prodEquivPi a h

end CausalCRT
end CausalGeometry
