import CausalGeometry.Completion.LocalProjectiveField
import CausalGeometry.Completion.PadicRootChildResidual
import Mathlib.FieldTheory.Finiteness

namespace CausalGeometry

namespace PadicRootChild

open PadicLattice

variable (p : ℕ) [Fact p.Prime]

namespace Child

variable (C : Child p)

/-- The residual subspace of every index-p child is one-dimensional over F_p. -/
theorem residualSubspace_finrank :
    Module.finrank (F p) C.residualSubspace = 1 := by
  letI : Module.Finite (F p) C.residualSubspace :=
    Module.Finite.of_injective
      C.residualSubspace.subtype
      C.residualSubspace.subtype_injective
  have hcard :=
    Module.natCard_eq_pow_finrank
      (K := F p)
      (V := C.residualSubspace)
  have hpow :
      p ^ Module.finrank (F p) C.residualSubspace =
        p ^ 1 := by
    rw [pow_one]
    rw [← C.residualSubspace_natCard]
    simpa [F, Nat.card_zmod] using hcard.symm
  exact
    Nat.pow_right_injective
      (Fact.out : Nat.Prime p).two_le
      hpow

/-- Canonical projective point represented by the residual line M/pL_0. -/
noncomputable def residualProjective :
    Projectivization (F p) (F p × F p) :=
  (Projectivization.equivSubmodule
    (K := F p) (V := F p × F p)).symm
      ⟨C.residualSubspace,
        C.residualSubspace_finrank⟩

/-- The same residual line in the local-projective quotient used by the
restriction-tower implementation. -/
noncomputable def residualPoint :
    LocalProjectivePair.Line (F p) :=
  (LocalProjectivePair.lineEquivProjectivization
    (F := F p)).symm
      C.residualProjective

/-- The residual point recovers exactly the residual subspace of the child. -/
theorem lineSubmodule_residualPoint :
    LocalProjectivePair.lineSubmodule
        (C.residualPoint) =
      C.residualSubspace := by
  unfold residualPoint residualProjective
  rw [LocalProjectivePair.lineSubmodule]
  simp

/-- The residual-point construction is injective on children.

Two children with the same projective residual line have the same preimage
under standard reduction, hence the same ambient lattice carrier. -/
theorem residualPoint_injective :
    Function.Injective
      (fun C : Child p => C.residualPoint) := by
  intro C D hpoint
  have hsub :
      C.residualSubspace =
        D.residualSubspace := by
    rw [← C.lineSubmodule_residualPoint,
      ← D.lineSubmodule_residualPoint,
      hpoint]
  apply Child.ext
  apply RankTwoLattice.ext
  ext x
  let xRoot : (Root p).carrier :=
    ⟨x, C.step.le ‹x ∈ C.lattice.carrier›⟩
  constructor
  · intro hxC
    have hxRoot :
        x ∈ (Root p).carrier :=
      C.step.le hxC
    let y : (Root p).carrier := ⟨x, hxRoot⟩
    have hred :
        standardReduction p y ∈
          C.residualAddSubgroup := by
      exact C.standardReduction_mem_residual
        (x := y)
        hxC
    have hsubAdd :
        C.residualAddSubgroup =
          D.residualAddSubgroup := by
      rw [← C.residualSubspace_toAddSubgroup,
        ← D.residualSubspace_toAddSubgroup,
        hsub]
    rw [hsubAdd] at hred
    exact
      D.mem_inside_of_standardReduction_mem
        (x := y) hred
  · intro hxD
    have hxRoot :
        x ∈ (Root p).carrier :=
      D.step.le hxD
    let y : (Root p).carrier := ⟨x, hxRoot⟩
    have hred :
        standardReduction p y ∈
          D.residualAddSubgroup := by
      exact D.standardReduction_mem_residual
        (x := y)
        hxD
    have hsubAdd :
        D.residualAddSubgroup =
          C.residualAddSubgroup := by
      rw [← D.residualSubspace_toAddSubgroup,
        ← C.residualSubspace_toAddSubgroup,
        hsub]
    rw [hsubAdd] at hred
    exact
      C.mem_inside_of_standardReduction_mem
        (x := y) hred

end Child
end PadicRootChild
end CausalGeometry
