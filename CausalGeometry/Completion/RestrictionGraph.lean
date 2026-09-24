import CausalGeometry.Completion.FinitePrimaryTower

namespace CausalGeometry

universe u

namespace InverseTower

variable (T : InverseTower)

/-- One directed edge in the restriction graph from depth n+1 to depth n. -/
def RestrictionEdge
    (n : ℕ)
    (x : T.Obj (n + 1))
    (y : T.Obj n) : Prop :=
  T.drop n x = y

/-- Every deeper state has a canonical parent one restriction level above. -/
def restrictionParent
    (n : ℕ)
    (x : T.Obj (n + 1)) :
    T.Obj n :=
  T.drop n x

@[simp] theorem restrictionEdge_parent
    (n : ℕ)
    (x : T.Obj (n + 1)) :
    T.RestrictionEdge n x (T.restrictionParent n x) := rfl

/-- The parent of a restriction-graph vertex is unique. -/
theorem restrictionParent_unique
    (n : ℕ)
    (x : T.Obj (n + 1))
    {y : T.Obj n}
    (h : T.RestrictionEdge n x y) :
    y = T.restrictionParent n x := by
  exact h.symm

/-- A completed causal history is an infinite ray through the restriction
graph: every adjacent pair is connected by a restriction edge. -/
theorem CompatibleHistory.edge
    (h : T.CompatibleHistory)
    (n : ℕ) :
    T.RestrictionEdge n (h.at (n + 1)) (h.at n) :=
  h.compatible n

end InverseTower

namespace FiniteInverseTower

variable (T : FiniteInverseTower)

/-- The vertices at graph depth n are exactly the finite states at tower level n. -/
abbrev RestrictionVertices (n : ℕ) :=
  T.Obj n

theorem restrictionVertices_card (n : ℕ) :
    @Fintype.card (T.RestrictionVertices n) (T.finite n) =
      T.card n := rfl

namespace Primary

variable {T : FiniteInverseTower}
variable (P : T.Primary)

/-- A primary restriction graph has q^(n+1) vertices at depth n. -/
theorem restrictionVertices_card_primary (n : ℕ) :
    @Fintype.card (T.RestrictionVertices n) (T.finite n) =
      P.q ^ (n + 1) := by
  exact P.card_law n

end Primary
end FiniteInverseTower
end CausalGeometry
