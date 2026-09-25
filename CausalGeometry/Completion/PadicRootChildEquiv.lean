import CausalGeometry.Completion.LocalProjectiveFieldCharts
import CausalGeometry.Completion.PadicProjectiveNeighbor
import CausalGeometry.Completion.PadicRootChildProjective

namespace CausalGeometry

namespace PadicRootChild

open PadicLattice
open PadicProjectiveNeighbor

variable (p : ℕ) [Fact p.Prime]

/-- Projective point q packaged as the corresponding concrete index-p child
of the standard lattice. -/
noncomputable def projectiveChild
    (q : P1 p) :
    Child p where
  lattice :=
    PadicProjectiveNeighbor.lattice p q
  step :=
    PadicProjectiveNeighbor.indexStep p q

namespace projectiveChild

/-- The standard functional vanishes exactly when reduction lies on the
projective line q. -/
theorem standardFunctional_eq_zero_iff
    (q : P1 p)
    (x : (Root p).carrier) :
    PadicProjectiveNeighbor.standardFunctional p q x = 0 ↔
      standardReduction p x ∈
        LocalProjectivePair.lineSubmodule q := by
  let y : O p × O p :=
    (PadicLattice.parameterEquiv p 0).symm x
  have hy :
      PadicLattice.parameterEquiv p 0 y = x :=
    (PadicLattice.parameterEquiv p 0).apply_symm_apply x
  have hfun :
      PadicProjectiveNeighbor.standardFunctional p q x =
        PadicProjectiveNeighbor.functional p q y := by
    rw [← hy]
    exact
      PadicProjectiveNeighbor.standardFunctional_parameter
        p q y
  have hred :
      standardReduction p x =
        PadicRootChild.residuePlane p y := by
    rw [← hy]
    exact standardReduction_parameter p y
  rw [hfun, hred]
  have hline :=
    LocalProjectivePair.mem_lineSubmodule_iff_chart
      q (PadicRootChild.residuePlane p y)
  cases hq :
      PadicProjectiveNeighbor.chart p q with
  | inl t =>
      have hchart :
          (LocalProjectivePair.chartEquiv
            (R := F p)).symm q =
            Sum.inl t := by
        simpa [PadicProjectiveNeighbor.chart]
          using hq
      rw [hchart] at hline
      rw [hline]
      unfold
        PadicProjectiveNeighbor.functional
      rw [hq]
      change
        PadicLattice.residue p y.2 -
              t * PadicLattice.residue p y.1 =
            0 ↔
          PadicLattice.residue p y.2 =
            t * PadicLattice.residue p y.1
      exact sub_eq_zero
  | inr u =>
      have hchart :
          (LocalProjectivePair.chartEquiv
            (R := F p)).symm q =
            Sum.inr u := by
        simpa [PadicProjectiveNeighbor.chart]
          using hq
      rw [hchart] at hline
      rw [hline]
      unfold
        PadicProjectiveNeighbor.functional
      rw [hq]
      change
        PadicLattice.residue p y.1 -
              u.1 * PadicLattice.residue p y.2 =
            0 ↔
          PadicLattice.residue p y.1 =
            u.1 * PadicLattice.residue p y.2
      exact sub_eq_zero

/-- The concrete projective neighbor is exactly the preimage of its residual
projective line under L0 -> F_p^2. -/
theorem mem_inside_iff_reduction_mem_line
    (q : P1 p)
    (x : (Root p).carrier) :
    x ∈ (projectiveChild p q).inside ↔
      standardReduction p x ∈
        LocalProjectivePair.lineSubmodule q := by
  have hker :=
    PadicProjectiveNeighbor.standardFunctional_ker
      p q
  constructor
  · intro hx
    have hzero :
        PadicProjectiveNeighbor.standardFunctional
          p q x = 0 := by
      rw [← AddMonoidHom.mem_ker]
      rw [hker]
      exact hx
    exact
      (standardFunctional_eq_zero_iff
        p q x).1 hzero
  · intro hline
    have hzero :=
      (standardFunctional_eq_zero_iff
        p q x).2 hline
    rw [← AddMonoidHom.mem_ker] at hzero
    rw [hker] at hzero
    exact hzero

/-- Projective-child construction is injective already at the lattice
representative level. -/
theorem injective :
    Function.Injective
      (projectiveChild p) := by
  intro q r h
  have hlattice :
      PadicProjectiveNeighbor.lattice p q =
        PadicProjectiveNeighbor.lattice p r :=
    congrArg Child.lattice h
  exact
    PadicProjectiveNeighbor.lattice_injective
      p hlattice

end projectiveChild

namespace Child

variable (C : Child p)

/-- Reconstructing a child from its canonical residual projective point gives
exactly the original child. -/
theorem projectiveChild_residualPoint :
    projectiveChild p C.residualPoint = C := by
  let D : Child p :=
    projectiveChild p C.residualPoint
  have hinside :
      D.inside = C.inside := by
    ext x
    constructor
    · intro hx
      have hred :
          standardReduction p x ∈
            LocalProjectivePair.lineSubmodule
              C.residualPoint :=
        (projectiveChild.mem_inside_iff_reduction_mem_line
          p C.residualPoint x).1 hx
      rw [C.lineSubmodule_residualPoint] at hred
      have hredAdd :
          standardReduction p x ∈
            C.residualAddSubgroup := by
        change
          standardReduction p x ∈
            C.residualSubspace.toAddSubgroup
        simpa using hred
      exact
        C.mem_inside_of_standardReduction_mem
          (x := x) hredAdd
    · intro hx
      have hredAdd :
          standardReduction p x ∈
            C.residualAddSubgroup :=
        C.standardReduction_mem_residual
          (x := x) hx
      have hred :
          standardReduction p x ∈
            LocalProjectivePair.lineSubmodule
              C.residualPoint := by
        rw [C.lineSubmodule_residualPoint]
        change
          standardReduction p x ∈
            C.residualSubspace.toAddSubgroup
        simpa using hredAdd
      exact
        (projectiveChild.mem_inside_iff_reduction_mem_line
          p C.residualPoint x).2 hred
  have hcarrier :
      D.lattice.carrier =
        C.lattice.carrier := by
    ext x
    constructor
    · intro hx
      have hxRoot :
          x ∈ (Root p).carrier :=
        D.step.le hx
      let y : (Root p).carrier :=
        ⟨x, hxRoot⟩
      have hyD : y ∈ D.inside := hx
      rw [hinside] at hyD
      exact hyD
    · intro hx
      have hxRoot :
          x ∈ (Root p).carrier :=
        C.step.le hx
      let y : (Root p).carrier :=
        ⟨x, hxRoot⟩
      have hyC : y ∈ C.inside := hx
      rw [← hinside] at hyC
      exact hyC
  have hlattice :
      D.lattice = C.lattice :=
    RankTwoLattice.ext hcarrier
  cases C with
  | mk L hL =>
      cases D with
      | mk M hM =>
          dsimp at hlattice
          subst M
          rfl

end Child

/-- The residual/projective classifier is also a right inverse: a projective
point reconstructed as a child has the same residual point. -/
theorem residualPoint_projectiveChild
    (q : P1 p) :
    (projectiveChild p q).residualPoint = q := by
  apply projectiveChild.injective p
  rw [
    (projectiveChild p q).projectiveChild_residualPoint
  ]

/-- Complete root-star classification: index-p children of the standard
p-adic lattice are exactly projective residue lines. -/
noncomputable def childEquivProjective :
    Child p ≃ P1 p where
  toFun := fun C => C.residualPoint
  invFun := projectiveChild p
  left_inv := by
    intro C
    exact C.projectiveChild_residualPoint
  right_inv := by
    intro q
    exact residualPoint_projectiveChild p q

/-- There are exactly p+1 index-p children of the standard lattice. -/
theorem child_natCard :
    Nat.card (Child p) = p + 1 := by
  rw [Nat.card_congr
    (childEquivProjective p)]
  simpa [P1] using
    zmodPrimeLocalTower.projectiveLine_natCard
      p 0

/-- Every root child is one of the previously constructed projective
neighbors; there are no missing index-p children. -/
theorem every_child_is_projective
    (C : Child p) :
    ∃! q : P1 p,
      projectiveChild p q = C := by
  refine ⟨C.residualPoint,
    C.projectiveChild_residualPoint,
    ?_⟩
  intro q hq
  apply projectiveChild.injective p
  rw [hq, C.projectiveChild_residualPoint]


/-- Homothety class carried by a root child. -/
def childClass
    (C : Child p) :
    RankTwoLattice.HomothetyClass
      (O := O p) (K := K p) :=
  RankTwoLattice.classOf C.lattice

/-- No index-p child of the root lies in the root homothety class. -/
theorem childClass_ne_root
    (C : Child p) :
    childClass p C ≠
      RankTwoLattice.classOf
        (Root p) := by
  rw [← C.projectiveChild_residualPoint]
  exact
    PadicProjectiveNeighbor.neighborClass_ne_root
      p C.residualPoint

/-- Distinct root children remain distinct after passage to homothety classes. -/
theorem childClass_injective :
    Function.Injective
      (childClass p) := by
  intro C D h
  have hC :
      PadicProjectiveNeighbor.lattice
          p C.residualPoint =
        C.lattice := by
    exact congrArg Child.lattice
      C.projectiveChild_residualPoint
  have hD :
      PadicProjectiveNeighbor.lattice
          p D.residualPoint =
        D.lattice := by
    exact congrArg Child.lattice
      D.projectiveChild_residualPoint
  have hq :
      C.residualPoint =
        D.residualPoint := by
    apply
      PadicProjectiveNeighbor.neighborClass_injective
        p
    rw [hC, hD]
    exact h
  exact
    Child.residualPoint_injective
      (p := p) hq

/-- Every root child class is p-adjacent to the root class. -/
theorem childClass_adjacent_root
    (C : Child p) :
    RankTwoLattice.ClassAdjacent
      (O := O p) (K := K p) p
      (RankTwoLattice.classOf
        (Root p))
      (childClass p C) := by
  exact
    ⟨Root p, C.lattice,
      rfl, rfl, Or.inl C.step⟩

/-- The set of root child homothety classes has exactly p+1 elements. -/
theorem childClass_range_natCard :
    Nat.card
        (Set.range (childClass p)) =
      p + 1 := by
  rw [← Nat.card_congr
    (Equiv.ofInjective
      (childClass p)
      (childClass_injective p))]
  exact child_natCard p

end PadicRootChild
end CausalGeometry
