import CausalGeometry.Completion.PadicLatticeRay
import CausalGeometry.Completion.LatticeGraph
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic

namespace CausalGeometry

namespace PadicLattice

variable (p : ℕ) [Fact p.Prime]

/-- The diagonal parameterization of L_n is injective. -/
theorem diagonalMap_injective
    (n : ℕ) :
    Function.Injective (diagonalMap p n) := by
  intro x y hxy
  apply Prod.ext
  · have hfst :=
      congrArg Prod.fst hxy
    have hpK :
        (p : K p) ≠ 0 := by
      exact_mod_cast
        (Fact.out : Nat.Prime p).ne_zero
    have hpow :
        (p : K p) ^ n ≠ 0 :=
      pow_ne_zero n hpK
    have hcoeff :
        algebraMap (O p) (K p) x.1 =
          algebraMap (O p) (K p) y.1 := by
      exact mul_left_cancel₀ hpow hfst
    exact Subtype.coe_injective hcoeff
  · have hsnd :=
      congrArg Prod.snd hxy
    exact Subtype.coe_injective hsnd

/-- Canonical parameter equivalence Z_p^2 ≃ L_n. -/
noncomputable def parameterEquiv
    (n : ℕ) :
    (O p × O p) ≃ₗ[O p]
      (diagonalLattice p n).carrier :=
  LinearEquiv.ofInjective
    (diagonalMap p n)
    (diagonalMap_injective p n)

/-- Residue of the first lattice parameter. -/
def firstResidue :
    (O p × O p) →+ ZMod p where
  toFun := fun x =>
    residue p x.1
  map_zero' := by simp [residue]
  map_add' := by
    intro x y
    simp [residue]

/-- Residue observable on L_n: recover the unique parameter and reduce its
first coordinate modulo p. -/
noncomputable def latticeResidue
    (n : ℕ) :
    (diagonalLattice p n).carrier →+
      ZMod p :=
  (firstResidue p).comp
    (parameterEquiv p n).symm.toLinearMap.toAddMonoidHom

@[simp] theorem latticeResidue_parameter
    (n : ℕ)
    (x : O p × O p) :
    latticeResidue p n
        (parameterEquiv p n x) =
      residue p x.1 := by
  simp [latticeResidue, firstResidue]

/-- The lattice residue map is onto. -/
theorem latticeResidue_surjective
    (n : ℕ) :
    Function.Surjective
      (latticeResidue p n) := by
  intro z
  rcases residue_surjective p z with
    ⟨a, ha⟩
  refine
    ⟨parameterEquiv p n (a, 0), ?_⟩
  simpa using ha

/-- Parameter identity expressing one deeper lattice inside the previous one. -/
theorem diagonalMap_succ_as_current
    (n : ℕ)
    (x : O p × O p) :
    diagonalMap p (n + 1) x =
      diagonalMap p n
        ((p : O p) * x.1, x.2) := by
  ext
  · simp [diagonalMap, pow_succ,
      mul_assoc, mul_left_comm,
      mul_comm]
  · simp [diagonalMap]

/-- Membership in L_(n+1), viewed as a submodule of L_n, is exactly zero first
residue. -/
theorem mem_next_iff_latticeResidue_eq_zero
    (n : ℕ)
    (x : (diagonalLattice p n).carrier) :
    x ∈
        (diagonalLattice p (n + 1)).carrier.submoduleOf
          (diagonalLattice p n).carrier
      ↔
    latticeResidue p n x = 0 := by
  let a : O p × O p :=
    (parameterEquiv p n).symm x
  have hparam :
      parameterEquiv p n a = x :=
    (parameterEquiv p n).apply_symm_apply x
  have hambient :
      diagonalMap p n a = x.1 := by
    exact congrArg Subtype.val hparam
  constructor
  · intro hx
    change
      x.1 ∈
        (diagonalLattice p (n + 1)).carrier at hx
    rcases hx with ⟨y, hy⟩
    have hdiag :
        diagonalMap p n
            ((p : O p) * y.1, y.2) =
          diagonalMap p n a := by
      rw [← diagonalMap_succ_as_current p n y]
      exact hy.trans hambient.symm
    have hpar :
        ((p : O p) * y.1, y.2) = a :=
      diagonalMap_injective p n hdiag
    have ha :
        a.1 = (p : O p) * y.1 := by
      exact congrArg Prod.fst hpar.symm
    rw [latticeResidue, firstResidue]
    simp only [AddMonoidHom.comp_apply]
    rw [show
      (parameterEquiv p n).symm x = a by rfl]
    rw [ha]
    have hpker :
        residue p (p : O p) = 0 := by
      rw [← RingHom.mem_ker]
      rw [residue_kernel p]
      exact Ideal.mem_span_singleton_self _
    simp [map_mul, hpker]
  · intro hz
    change
      x.1 ∈
        (diagonalLattice p (n + 1)).carrier
    have ha0 :
        residue p a.1 = 0 := by
      simpa [latticeResidue, firstResidue, a]
        using hz
    have hmem :
        a.1 ∈
          Ideal.span ({(p : O p)} : Set (O p)) := by
      rw [← residue_kernel p]
      exact ha0
    rcases
        Ideal.mem_span_singleton'.mp hmem with
      ⟨c, hc⟩
    refine ⟨(c, a.2), ?_⟩
    rw [diagonalMap_succ_as_current]
    have hc' :
        (p : O p) * c = a.1 := by
      simpa [mul_comm] using hc
    rw [hc']
    exact hambient

/-- Kernel of the lattice residue is exactly the next diagonal lattice. -/
theorem latticeResidue_ker
    (n : ℕ) :
    (latticeResidue p n).ker =
      ((diagonalLattice p (n + 1)).carrier.submoduleOf
        (diagonalLattice p n).carrier).toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker]
  exact
    (mem_next_iff_latticeResidue_eq_zero
      p n x).symm

/-- One diagonal lattice quotient is canonically a residue-field-sized
quotient: |L_n/L_(n+1)|=p. -/
theorem diagonalQuotient_natCard
    (n : ℕ) :
    Nat.card
        ((diagonalLattice p n).carrier ⧸
          (diagonalLattice p (n + 1)).carrier.submoduleOf
            (diagonalLattice p n).carrier) =
      p := by
  let f :=
    latticeResidue p n
  have hker :=
    latticeResidue_ker p n
  change
    Nat.card
      ((diagonalLattice p n).carrier ⧸
        ((diagonalLattice p (n + 1)).carrier.submoduleOf
          (diagonalLattice p n).carrier).toAddSubgroup) =
      p
  rw [← hker]
  rw [Nat.card_congr
    (QuotientAddGroup.quotientKerEquivRange f).toEquiv]
  have hrange :
      f.range = ⊤ :=
    AddMonoidHom.range_eq_top.mpr
      (latticeResidue_surjective p n)
  rw [hrange]
  simpa using residue_natCard p

/-- Every inclusion step of the diagonal ray is an actual p-index lattice edge. -/
def diagonalIndexStep
    (n : ℕ) :
    RankTwoLattice.IndexStep p
      (diagonalLattice p n)
      (diagonalLattice p (n + 1)) where
  le :=
    diagonalLattice_succ_le p n
  quotient_card :=
    diagonalQuotient_natCard p n

/-- Consecutive diagonal lattices determine adjacent homothety classes in the
p-index lattice graph. -/
theorem diagonalClassAdjacent
    (n : ℕ) :
    RankTwoLattice.ClassAdjacent
      (O := O p) (K := K p) p
      (RankTwoLattice.classOf
        (diagonalLattice p n))
      (RankTwoLattice.classOf
        (diagonalLattice p (n + 1))) := by
  exact
    ⟨diagonalLattice p n,
      diagonalLattice p (n + 1),
      rfl, rfl,
      Or.inl (diagonalIndexStep p n)⟩

end PadicLattice
end CausalGeometry
