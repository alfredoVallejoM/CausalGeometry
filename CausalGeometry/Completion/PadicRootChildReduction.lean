import CausalGeometry.Completion.PadicProjectiveNeighbor
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Module.NatInt
import Mathlib.Tactic

namespace CausalGeometry

namespace PadicRootChild

open PadicLattice
open PadicProjectiveNeighbor

variable (p : ℕ) [Fact p.Prime]

abbrev O := PadicLattice.O p
abbrev K := PadicLattice.K p
abbrev F := ZMod p
abbrev Root :=
  PadicLattice.diagonalLattice p 0

/-- An oriented index-p child of the standard lattice. -/
structure Child where
  lattice : RankTwoLattice (O p) (K p)
  step :
    RankTwoLattice.IndexStep p
      (Root p) lattice

namespace Child

variable (C : Child p)

/-- The child as an O-submodule of the standard lattice. -/
def inside :
    Submodule (O p) (Root p).carrier :=
  C.lattice.carrier.submoduleOf
    (Root p).carrier

@[simp] theorem mem_inside
    (x : (Root p).carrier) :
    x ∈ C.inside ↔
      x.1 ∈ C.lattice.carrier :=
  Iff.rfl

/-- Every quotient element of an index-p child is killed by p. -/
theorem quotient_p_nsmul_eq_zero
    (x : (Root p).carrier) :
    p •
        (Submodule.Quotient.mk x :
          (Root p).carrier ⧸ C.inside) =
      0 := by
  have hcard :
      Nat.card
          ((Root p).carrier ⧸
            C.inside) =
        p := by
    simpa [inside, Root] using
      C.step.quotient_card
  have h :=
    card_nsmul_eq_zero'
      (x :=
        (Submodule.Quotient.mk x :
          (Root p).carrier ⧸ C.inside))
  simpa [hcard] using h

/-- Fundamental local-index fact: p L0 is contained in every index-p child. -/
theorem p_smul_mem
    (x : (Root p).carrier) :
    (p : O p) • x ∈ C.inside := by
  have h :=
    C.quotient_p_nsmul_eq_zero x
  rw [
    ← Nat.cast_smul_eq_nsmul (O p),
    ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero
  ] at h
  exact h

end Child

/-- Coordinatewise reduction O^2 -> F_p^2. -/
def residuePlane :
    (O p × O p) →+ (F p × F p) where
  toFun := fun x =>
    (PadicLattice.residue p x.1,
      PadicLattice.residue p x.2)
  map_zero' := by simp
  map_add' := by
    intro x y
    ext <;> simp

theorem residuePlane_surjective :
    Function.Surjective
      (residuePlane p) := by
  intro z
  rcases
      PadicLattice.residue_surjective p z.1 with
    ⟨a, ha⟩
  rcases
      PadicLattice.residue_surjective p z.2 with
    ⟨b, hb⟩
  exact ⟨(a, b), by
    ext <;> assumption⟩

/-- Standard reduction L0 -> F_p^2 through the canonical parameterization
L0 ≃ O^2. -/
noncomputable def standardReduction :
    (Root p).carrier →+
      (F p × F p) :=
  (residuePlane p).comp
    (PadicLattice.parameterEquiv p 0).symm
      .toLinearMap.toAddMonoidHom

@[simp] theorem standardReduction_parameter
    (x : O p × O p) :
    standardReduction p
        (PadicLattice.parameterEquiv p 0 x) =
      residuePlane p x := by
  simp [standardReduction]

theorem standardReduction_surjective :
    Function.Surjective
      (standardReduction p) := by
  intro z
  rcases residuePlane_surjective p z with
    ⟨x, hx⟩
  exact
    ⟨PadicLattice.parameterEquiv p 0 x,
      by simpa using hx⟩

/-- p times the standard lattice, internalized as a submodule of L0. -/
def pRoot :
    Submodule (O p) (Root p).carrier :=
  LinearMap.range
    (LinearMap.lsmul
      (O p) (Root p).carrier
      (p : O p))

@[simp] theorem mem_pRoot_iff
    (x : (Root p).carrier) :
    x ∈ pRoot p ↔
      ∃ y : (Root p).carrier,
        (p : O p) • y = x :=
  Iff.rfl

/-- pL0 is exactly the kernel of coordinatewise residue. -/
theorem standardReduction_ker :
    (standardReduction p).ker =
      (pRoot p).toAddSubgroup := by
  ext x
  constructor
  · intro hx
    rw [AddMonoidHom.mem_ker] at hx
    let a : O p × O p :=
      (PadicLattice.parameterEquiv p 0).symm x
    have ha :
        residuePlane p a = 0 := by
      simpa [a, standardReduction] using hx
    have ha1 :
        PadicLattice.residue p a.1 = 0 := by
      exact congrArg Prod.fst ha
    have ha2 :
        PadicLattice.residue p a.2 = 0 := by
      exact congrArg Prod.snd ha
    have hmem1 :
        a.1 ∈ Ideal.span
          ({(p : O p)} : Set (O p)) := by
      rw [← PadicLattice.residue_kernel p]
      exact ha1
    have hmem2 :
        a.2 ∈ Ideal.span
          ({(p : O p)} : Set (O p)) := by
      rw [← PadicLattice.residue_kernel p]
      exact ha2
    rcases Ideal.mem_span_singleton'.mp hmem1 with
      ⟨b₁, hb₁⟩
    rcases Ideal.mem_span_singleton'.mp hmem2 with
      ⟨b₂, hb₂⟩
    let y : (Root p).carrier :=
      PadicLattice.parameterEquiv p 0 (b₁, b₂)
    apply (mem_pRoot_iff p x).2
    refine ⟨y, ?_⟩
    apply Subtype.ext
    have hxparam :
        PadicLattice.parameterEquiv p 0 a = x :=
      (PadicLattice.parameterEquiv p 0).apply_symm_apply x
    rw [← hxparam]
    change
      ((p : O p) •
        PadicLattice.parameterEquiv p 0 (b₁, b₂)).1 =
      (PadicLattice.parameterEquiv p 0 a).1
    rw [← map_smul]
    apply congrArg Subtype.val
    apply
      (PadicLattice.parameterEquiv p 0).injective
    apply Prod.ext
    · change (p : O p) * b₁ = a.1
      simpa [mul_comm] using hb₁
    · change (p : O p) * b₂ = a.2
      simpa [mul_comm] using hb₂
  · intro hx
    rcases (mem_pRoot_iff p x).1 hx with
      ⟨y, rfl⟩
    rw [AddMonoidHom.mem_ker]
    let a : O p × O p :=
      (PadicLattice.parameterEquiv p 0).symm y
    have hy :
        PadicLattice.parameterEquiv p 0 a = y :=
      (PadicLattice.parameterEquiv p 0).apply_symm_apply y
    change
      standardReduction p
        ((p : O p) • y) = 0
    rw [← hy, ← map_smul]
    simp [standardReduction,
      residuePlane,
      PadicProjectiveNeighbor.residue_p_zero p]

/-- L0/pL0 is canonically the two-dimensional residue plane. -/
noncomputable def rootModPAddEquiv :
    ((Root p).carrier ⧸ pRoot p) ≃+
      (F p × F p) := by
  let f := standardReduction p
  have hker :
      f.ker =
        (pRoot p).toAddSubgroup := by
    simpa [f] using
      standardReduction_ker p
  let e₁ :
      ((Root p).carrier ⧸
        (pRoot p).toAddSubgroup) ≃+
        ((Root p).carrier ⧸ f.ker) :=
    QuotientAddGroup.congr
      (pRoot p).toAddSubgroup
      f.ker
      (AddEquiv.refl _)
      (by
        rw [← hker]
        simp)
  let e₂ :
      ((Root p).carrier ⧸ f.ker) ≃+
        (F p × F p) :=
    QuotientAddGroup.quotientKerEquivOfSurjective
      f (standardReduction_surjective p)
  exact e₁.trans e₂

@[simp] theorem rootModPAddEquiv_mk
    (x : (Root p).carrier) :
    rootModPAddEquiv p
        (Submodule.Quotient.mk x) =
      standardReduction p x := by
  unfold rootModPAddEquiv
  rfl

/-- The standard mod-p plane has p^2 elements. -/
theorem rootModP_natCard :
    Nat.card
        ((Root p).carrier ⧸ pRoot p) =
      p ^ 2 := by
  rw [Nat.card_congr
    (rootModPAddEquiv p).toEquiv]
  simp [Nat.card_prod,
    Nat.card_zmod, pow_two]

/-- Every index-p child contains pL0. -/
theorem pRoot_le_child
    (C : Child p) :
    pRoot p ≤ C.inside := by
  intro x hx
  rcases (mem_pRoot_iff p x).1 hx with
    ⟨y, rfl⟩
  exact C.p_smul_mem y

end PadicRootChild
end CausalGeometry
