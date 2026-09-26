import CausalGeometry.Calculus.CubicalCup
import Mathlib.Algebra.BigOperators.Field
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

open EventSystem
open scoped BigOperators

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalEventCube

/-- Canonical inclusion of the left p-block into p+q coordinates. -/
def leftBlockIndex
    (p q : ℕ)
    (i : Fin p) :
    Fin (p + q) :=
  ⟨i.val, by omega⟩

/-- Canonical inclusion of the right q-block into p+q coordinates. -/
def rightBlockIndex
    (p q : ℕ)
    (j : Fin q) :
    Fin (p + q) :=
  ⟨p + j.val, by omega⟩

/-- Reorder the primitive-event coordinates of a causal cube.

The base configuration is unchanged.  Only the ordered coordinate presentation
of the pairwise-concurrent frame is changed. -/
def permute
    {n : ℕ}
    (Q : CausalEventCube S n)
    (σ : Equiv.Perm (Fin n)) :
    CausalEventCube S n :=
  ⟨Q.base,
    Q.frame.reindex σ σ.injective⟩

@[simp] theorem permute_base
    {n : ℕ}
    (Q : CausalEventCube S n)
    (σ : Equiv.Perm (Fin n)) :
    (Q.permute σ).base = Q.base :=
  rfl

@[simp] theorem permute_event
    {n : ℕ}
    (Q : CausalEventCube S n)
    (σ : Equiv.Perm (Fin n))
    (i : Fin n) :
    (Q.permute σ).frame.event i =
      Q.frame.event (σ i) :=
  rfl

end CausalEventCube

namespace CausalCubicalCochain

/-- Predicate selecting the standard (p,q)-shuffle permutations:
the relative order inside the first p chosen coordinates and inside the last q
chosen coordinates is preserved. -/
def IsCubicalShuffle
    (p q : ℕ)
    (σ : Equiv.Perm (Fin (p + q))) : Prop :=
  StrictMono
      (fun i : Fin p =>
        σ (CausalEventCube.leftBlockIndex p q i))
    ∧
  StrictMono
      (fun j : Fin q =>
        σ (CausalEventCube.rightBlockIndex p q j))

/-- Finite type of (p,q)-shuffles. -/
abbrev CubicalShuffle
    (p q : ℕ) :=
  {σ : Equiv.Perm (Fin (p + q)) //
    IsCubicalShuffle p q σ}

noncomputable instance cubicalShuffleFintype
    (p q : ℕ) :
    Fintype (CubicalShuffle p q) :=
  Fintype.ofFinite _

/-- The identity permutation is always a shuffle. -/
def identityShuffle
    (p q : ℕ) :
    CubicalShuffle p q :=
  ⟨Equiv.refl _, by
    constructor
    · intro i j hij
      simpa [CausalEventCube.leftBlockIndex]
        using hij
    · intro i j hij
      simpa [CausalEventCube.rightBlockIndex]
        using hij⟩

/-- Inversion pairs of one finite coordinate permutation. -/
def inversionPairs
    {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    Finset (Fin n × Fin n) :=
  (Finset.univ.product Finset.univ).filter
    (fun ij =>
      ij.1 < ij.2 ∧
        σ ij.2 < σ ij.1)

/-- Number of inversions of one coordinate permutation. -/
def inversionCount
    {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    ℕ :=
  (inversionPairs σ).card

/-- Canonical orientation/Koszul sign of a shuffle in the coefficient
field.

The earlier inversion count remains available as a combinatorial statistic,
but orientation-sensitive theorems now use the canonical permutation sign
from mathlib so the cup, face and exterior layers share one sign source. -/
def shuffleSign
    {K : Type w}
    [Field K]
    {p q : ℕ}
    (σ : CubicalShuffle p q) :
    K :=
  (((Equiv.Perm.sign σ.1 : ℤˣ) : ℤ) : K)

variable {K : Type w} [Field K]

/-- One signed Serre-diagonal summand.

After permuting Q by a (p,q)-shuffle, the ordered front/back product is the
corresponding face pair in the cubical diagonal. -/
def shuffleCupTerm
    (p q : ℕ)
    (α : CausalCubicalCochain S K p)
    (β : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q))
    (σ : CubicalShuffle p q) :
    K :=
  shuffleSign (K := K) σ *
    orderedCup p q α β
      (Q.permute σ.1)

/-- Full cubical Serre/Alexander--Whitney cup product.

Unlike orderedCup, this sums over every (p,q)-shuffle.  This is the correct
candidate for a graded product compatible with the cubical differential. -/
noncomputable def serreCup
    (p q : ℕ)
    (α : CausalCubicalCochain S K p)
    (β : CausalCubicalCochain S K q) :
    CausalCubicalCochain S K (p + q) :=
  fun Q =>
    ∑ σ : CubicalShuffle p q,
      shuffleCupTerm p q α β Q σ

@[simp] theorem serreCup_apply
    (p q : ℕ)
    (α : CausalCubicalCochain S K p)
    (β : CausalCubicalCochain S K q)
    (Q : CausalEventCube S (p + q)) :
    serreCup p q α β Q =
      ∑ σ : CubicalShuffle p q,
        shuffleCupTerm p q α β Q σ :=
  rfl

theorem serreCup_add_left
    (p q : ℕ)
    (α γ : CausalCubicalCochain S K p)
    (β : CausalCubicalCochain S K q) :
    serreCup p q (α + γ) β =
      serreCup p q α β +
        serreCup p q γ β := by
  funext Q
  simp [serreCup, shuffleCupTerm,
    orderedCup_apply, add_mul,
    Finset.sum_add_distrib]

theorem serreCup_add_right
    (p q : ℕ)
    (α : CausalCubicalCochain S K p)
    (β γ : CausalCubicalCochain S K q) :
    serreCup p q α (β + γ) =
      serreCup p q α β +
        serreCup p q α γ := by
  funext Q
  simp [serreCup, shuffleCupTerm,
    orderedCup_apply, mul_add,
    Finset.sum_add_distrib]

theorem serreCup_smul_left
    (p q : ℕ)
    (a : K)
    (α : CausalCubicalCochain S K p)
    (β : CausalCubicalCochain S K q) :
    serreCup p q (a • α) β =
      a • serreCup p q α β := by
  funext Q
  simp [serreCup, shuffleCupTerm,
    orderedCup_apply, mul_assoc,
    mul_comm, mul_left_comm,
    Finset.mul_sum]

theorem serreCup_smul_right
    (p q : ℕ)
    (a : K)
    (α : CausalCubicalCochain S K p)
    (β : CausalCubicalCochain S K q) :
    serreCup p q α (a • β) =
      a • serreCup p q α β := by
  funext Q
  simp [serreCup, shuffleCupTerm,
    orderedCup_apply, mul_assoc,
    mul_comm, mul_left_comm,
    Finset.mul_sum]

/-- Graded sign appearing in the Leibniz rule. -/
def gradedSign
    (p : ℕ) : K :=
  (-1 : K) ^ p

/-- Explicit all-degree Leibniz defect for the Serre cup.

It is kept as data until the full shuffle/face cancellation theorem is proved.
The intended closure theorem is that this cochain is identically zero. -/
noncomputable def serreLeibnizDefect
    (p q : ℕ)
    (α : CausalCubicalCochain S K p)
    (β : CausalCubicalCochain S K q) :
    CausalCubicalCochain S K (p + q + 1) :=
  differential (S := S) (K := K) (p + q)
      (serreCup p q α β)
    -
  (by
    simpa [Nat.add_assoc] using
      serreCup (p + 1) q
        (differential (S := S) (K := K) p α)
        β)
    -
  (gradedSign (K := K) p) •
    (by
      simpa [Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        serreCup p (q + 1)
          α
          (differential
            (S := S) (K := K) q β))

/-- Named theorem target for the future complete graded DGA closure. -/
def SerreCupLeibniz
    (p q : ℕ)
    (α : CausalCubicalCochain S K p)
    (β : CausalCubicalCochain S K q) : Prop :=
  serreLeibnizDefect p q α β = 0

end CausalCubicalCochain
end CausalGeometry
