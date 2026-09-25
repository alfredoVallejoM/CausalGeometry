import CausalGeometry.Completion.PadicRootChildReduction
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic

namespace CausalGeometry

namespace PadicRootChild

open PadicLattice

variable (p : ℕ) [Fact p.Prime]

namespace Child

variable (C : Child p)

/-- The image M/pL0 inside L0/pL0. -/
def quotientSubmodule :
    Submodule (O p)
      ((Root p).carrier ⧸ pRoot p) :=
  C.inside.map
    (Submodule.mkQ (pRoot p))

/-- Third-isomorphism cardinal calculation:
|M/pL0| * |L0/M| = |L0/pL0|. -/
theorem quotientSubmodule_natCard :
    Nat.card C.quotientSubmodule = p := by
  have h :=
    Submodule.card_quotient_mul_card_quotient
      C.inside (pRoot p)
      (pRoot_le_child p C)
  have hstep :
      Nat.card
          ((Root p).carrier ⧸
            C.inside) =
        p := by
    simpa [inside, Root] using
      C.step.quotient_card
  have hroot :
      Nat.card
          ((Root p).carrier ⧸
            pRoot p) =
        p ^ 2 :=
    rootModP_natCard p
  change
    Nat.card C.quotientSubmodule *
        Nat.card
          ((Root p).carrier ⧸ C.inside) =
      Nat.card
        ((Root p).carrier ⧸ pRoot p) at h
  rw [hstep, hroot, pow_two] at h
  exact Nat.mul_right_cancel h

/-- Residual additive subgroup inside F_p^2. -/
noncomputable def residualAddSubgroup :
    AddSubgroup (F p × F p) :=
  C.quotientSubmodule.toAddSubgroup.map
    (rootModPAddEquiv p).toAddMonoidHom

/-- The quotient submodule and its residual image are additively equivalent. -/
noncomputable def quotientEquivResidual :
    C.quotientSubmodule ≃+
      C.residualAddSubgroup :=
  (rootModPAddEquiv p).subgroupMap
    C.quotientSubmodule.toAddSubgroup

/-- The residual subgroup has exactly p elements. -/
theorem residualAddSubgroup_natCard :
    Nat.card C.residualAddSubgroup = p := by
  rw [← Nat.card_congr
    C.quotientEquivResidual.toEquiv]
  exact C.quotientSubmodule_natCard

/-- Since F_p is the prime field, every additive subgroup is canonically an
F_p-subspace. -/
noncomputable def residualSubspace :
    Submodule (F p) (F p × F p) :=
  (AddSubgroup.toZModSubmodule p)
    C.residualAddSubgroup

@[simp] theorem residualSubspace_toAddSubgroup :
    C.residualSubspace.toAddSubgroup =
      C.residualAddSubgroup := by
  exact
    AddSubgroup.toZModSubmodule_symm p
      C.residualAddSubgroup

theorem residualSubspace_natCard :
    Nat.card C.residualSubspace = p := by
  change
    Nat.card C.residualAddSubgroup = p
  exact C.residualAddSubgroup_natCard

/-- A child vector reduces into its residual subspace. -/
theorem standardReduction_mem_residual
    {x : (Root p).carrier}
    (hx : x ∈ C.inside) :
    standardReduction p x ∈
      C.residualAddSubgroup := by
  change
    standardReduction p x ∈
      C.quotientSubmodule.toAddSubgroup.map
        (rootModPAddEquiv p).toAddMonoidHom
  refine
    ⟨Submodule.Quotient.mk x, ?_, ?_⟩
  · change
      Submodule.Quotient.mk x ∈
        C.inside.map
          (Submodule.mkQ (pRoot p))
    exact
      ⟨x, hx, rfl⟩
  · exact
      rootModPAddEquiv_mk p x

/-- Conversely, residual membership reconstructs child membership. -/
theorem mem_inside_of_standardReduction_mem
    {x : (Root p).carrier}
    (hx :
      standardReduction p x ∈
        C.residualAddSubgroup) :
    x ∈ C.inside := by
  change
    standardReduction p x ∈
      C.quotientSubmodule.toAddSubgroup.map
        (rootModPAddEquiv p).toAddMonoidHom at hx
  rcases hx with
    ⟨q, hq, hqx⟩
  change
    q ∈
      C.inside.map
        (Submodule.mkQ (pRoot p)) at hq
  rcases hq with
    ⟨y, hy, hyq⟩
  have hqmk :
      q =
        Submodule.Quotient.mk x := by
    apply (rootModPAddEquiv p).injective
    calc
      rootModPAddEquiv p q
          =
        standardReduction p x := hqx
      _ =
        rootModPAddEquiv p
          (Submodule.Quotient.mk x) :=
        (rootModPAddEquiv_mk p x).symm
  have hmk :
      Submodule.Quotient.mk y =
        (Submodule.Quotient.mk x :
          (Root p).carrier ⧸ pRoot p) := by
    exact hyq.trans hqmk
  have hdiff :
      y - x ∈ pRoot p :=
    (Submodule.Quotient.eq (pRoot p)).mp
      hmk
  have hdiffChild :
      y - x ∈ C.inside :=
    (pRoot_le_child p C) hdiff
  have hx' :
      y - (y - x) ∈ C.inside :=
    C.inside.sub_mem hy hdiffChild
  simpa using hx'

/-- Exact reconstruction theorem: an index-p child is the preimage of its
residual line under L0 -> F_p^2. -/
theorem mem_inside_iff_reduction_mem
    (x : (Root p).carrier) :
    x ∈ C.inside ↔
      standardReduction p x ∈
        C.residualAddSubgroup := by
  constructor
  · exact C.standardReduction_mem_residual
  · exact C.mem_inside_of_standardReduction_mem

/-- Submodule-level reconstruction from residual data. -/
theorem inside_eq_comap_residual :
    C.inside.toAddSubgroup =
      C.residualAddSubgroup.comap
        (standardReduction p) := by
  ext x
  exact C.mem_inside_iff_reduction_mem x

end Child
end PadicRootChild
end CausalGeometry
