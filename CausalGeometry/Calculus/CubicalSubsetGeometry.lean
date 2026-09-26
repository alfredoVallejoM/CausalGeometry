import CausalGeometry.Calculus.EventCube
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace CausalGeometry

universe u v

open EventSystem
open Set

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalEventCube

/-- A fixed-cardinality subset of the ordered axes of an n-cube. -/
abbrev AxisSubset (n p : ℕ) :=
  Set.powersetCard (Fin n) p

/-- Events selected by one finite set of cube axes. -/
def selectedEventSet
    {n : ℕ}
    (Q : CausalEventCube S n)
    (A : Finset (Fin n)) :
    Set Event :=
  Q.frame.event '' (A : Set (Fin n))

/-- Configuration obtained by adjoining simultaneously all events selected by A.

Because all axes of a causal cube are enabled at the same base and pairwise
independent, no execution order is required to define this configuration. -/
def afterAxes
    {n : ℕ}
    (Q : CausalEventCube S n)
    (A : Finset (Fin n)) :
    Configuration S where

  carrier :=
    Q.base.carrier ∪
      Q.selectedEventSet A

  downClosed := by
    intro e f he hfe
    rcases he with heBase | heSel
    · exact Or.inl
        (Q.base.downClosed heBase hfe)
    · rcases heSel with
        ⟨i, hiA, rfl⟩
      exact Or.inl
        ((Q.frame.enabled i).2.1 f hfe)

  conflictFree := by
    intro e f he hf
    rcases he with heBase | heSel
    · rcases hf with hfBase | hfSel
      · exact Q.base.conflictFree
          heBase hfBase
      · rcases hfSel with
          ⟨j, hjA, rfl⟩
        intro hconf
        exact
          (Q.frame.enabled j).2.2 e heBase
            (S.conflict_symm hconf)
    · rcases heSel with
        ⟨i, hiA, rfl⟩
      rcases hf with hfBase | hfSel
      · exact
          (Q.frame.enabled i).2.2 f hfBase
      · rcases hfSel with
          ⟨j, hjA, rfl⟩
        by_cases hij : i = j
        · subst j
          exact S.conflict_irrefl _
        · exact (Q.frame.independent hij).2.2

@[simp] theorem mem_afterAxes_iff
    {n : ℕ}
    (Q : CausalEventCube S n)
    (A : Finset (Fin n))
    (e : Event) :
    e ∈ Q.afterAxes A ↔
      e ∈ Q.base ∨
        ∃ i ∈ A, Q.frame.event i = e := by
  rfl

/-- An unselected cube axis remains enabled after all selected axes have been
adjoined simultaneously. -/
theorem enabled_afterAxes_of_not_mem
    {n : ℕ}
    (Q : CausalEventCube S n)
    (A : Finset (Fin n))
    (j : Fin n)
    (hj : j ∉ A) :
    S.Enabled (Q.afterAxes A)
      (Q.frame.event j) := by
  refine ⟨?_, ?_, ?_⟩

  · intro hmem
    rcases hmem with hbase | hsel
    · exact (Q.frame.enabled j).1 hbase
    · rcases hsel with
        ⟨i, hiA, hij⟩
      have hieq :
          i = j :=
        Q.frame.injective hij
      subst i
      exact hj hiA

  · intro f hpred
    exact Or.inl
      ((Q.frame.enabled j).2.1 f hpred)

  · intro f hf
    rcases hf with hfBase | hfSel
    · exact
        (Q.frame.enabled j).2.2 f hfBase
    · rcases hfSel with
        ⟨i, hiA, rfl⟩
      have hji : j ≠ i := by
        intro h
        subst i
        exact hj hiA
      exact
        (Q.frame.independent hji).2.2

/-- The selected-axis cube, with the original base and axes enumerated in the
ambient increasing order. -/
noncomputable def selectedCube
    {n p : ℕ}
    (Q : CausalEventCube S n)
    (A : AxisSubset n p) :
    CausalEventCube S p :=
  ⟨Q.base,
    Q.frame.reindex
      (fun i =>
        (Set.powersetCard.orderIsoOfFin A i).1)
      (by
        intro i j hij
        apply
          (Set.powersetCard.orderIsoOfFin A).injective
        apply Subtype.ext
        exact hij)⟩

@[simp] theorem selectedCube_base
    {n p : ℕ}
    (Q : CausalEventCube S n)
    (A : AxisSubset n p) :
    (Q.selectedCube A).base = Q.base :=
  rfl

@[simp] theorem selectedCube_event
    {n p : ℕ}
    (Q : CausalEventCube S n)
    (A : AxisSubset n p)
    (i : Fin p) :
    (Q.selectedCube A).frame.event i =
      Q.frame.event
        (Set.powersetCard.orderIsoOfFin A i).1 :=
  rfl

/-- Complementary q-axis subset in an ambient (p+q)-cube. -/
def complementAxes
    {p q : ℕ}
    (A : AxisSubset (p + q) p) :
    AxisSubset (p + q) q :=
  ⟨A.valᶜ, by
    simp [Finset.card_compl,
      Fintype.card_fin, A.prop]
    omega⟩

@[simp] theorem complementAxes_val
    {p q : ℕ}
    (A : AxisSubset (p + q) p) :
    (A.complementAxes : Finset (Fin (p + q))) =
      A.valᶜ :=
  rfl

/-- The complementary cube after all selected A-events have occurred.

The base is Q.afterAxes A.  Every complementary event remains enabled there,
and the inherited frame stays pairwise independent. -/
noncomputable def complementCube
    {p q : ℕ}
    (Q : CausalEventCube S (p + q))
    (A : AxisSubset (p + q) p) :
    CausalEventCube S q :=

  let B := A.complementAxes

  ⟨Q.afterAxes A.val,
    { event := fun j =>
        Q.frame.event
          (Set.powersetCard.orderIsoOfFin B j).1

      enabled := by
        intro j
        let k :=
          (Set.powersetCard.orderIsoOfFin B j).1
        have hkB :
            k ∈ B.val :=
          (Set.powersetCard.orderIsoOfFin B j).2
        have hkA : k ∉ A.val := by
          simpa [B, complementAxes] using hkB
        exact
          Q.enabled_afterAxes_of_not_mem
            A.val k hkA

      injective := by
        intro i j hij
        apply
          (Set.powersetCard.orderIsoOfFin B).injective
        apply Subtype.ext
        exact Q.frame.injective hij

      independent := by
        intro i j hij
        apply Q.frame.independent
        intro hidx
        apply hij
        apply
          (Set.powersetCard.orderIsoOfFin B).injective
        apply Subtype.ext
        exact hidx }⟩

@[simp] theorem complementCube_base
    {p q : ℕ}
    (Q : CausalEventCube S (p + q))
    (A : AxisSubset (p + q) p) :
    (Q.complementCube A).base =
      Q.afterAxes A.val :=
  rfl

end CausalEventCube
end CausalGeometry
