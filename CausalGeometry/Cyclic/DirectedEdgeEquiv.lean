import CausalGeometry.Cyclic.DirectedEdge

namespace CausalGeometry

universe u₁ u₂

/-- Isomorphism of arbitrary directed-edge systems.

Unlike FiniteDirectedEdgeEquiv, no finiteness is assumed. This is the correct
comparison notion for universal trees such as Bruhat--Tits before passage to a
finite arithmetic quotient. -/
structure DirectedEdgeEquiv
    {V₁ E₁ : Type u₁}
    {V₂ E₂ : Type u₂}
    (G₁ : DirectedEdgeSystem V₁ E₁)
    (G₂ : DirectedEdgeSystem V₂ E₂) where
  vertexEquiv : V₁ ≃ V₂
  edgeEquiv : E₁ ≃ E₂

  source_compat :
    ∀ e,
      vertexEquiv (G₁.source e) =
        G₂.source (edgeEquiv e)

  target_compat :
    ∀ e,
      vertexEquiv (G₁.target e) =
        G₂.target (edgeEquiv e)

  reverse_compat :
    ∀ e,
      edgeEquiv (G₁.reverse e) =
        G₂.reverse (edgeEquiv e)

namespace DirectedEdgeEquiv

variable
    {V₁ E₁ : Type u₁}
    {V₂ E₂ : Type u₂}
    {G₁ : DirectedEdgeSystem V₁ E₁}
    {G₂ : DirectedEdgeSystem V₂ E₂}
    (E : DirectedEdgeEquiv G₁ G₂)

theorem nonbacktracking_iff
    (e f : E₁) :
    G₁.Nonbacktracking e f ↔
      G₂.Nonbacktracking
        (E.edgeEquiv e)
        (E.edgeEquiv f) := by
  constructor
  · intro h
    constructor
    · rw [← E.target_compat e,
        ← E.source_compat f]
      exact congrArg E.vertexEquiv h.1
    · intro hrev
      apply h.2
      apply E.edgeEquiv.injective
      rw [E.reverse_compat]
      exact hrev
  · intro h
    constructor
    · apply E.vertexEquiv.injective
      rw [E.target_compat e,
        E.source_compat f]
      exact h.1
    · intro hrev
      apply h.2
      rw [← E.reverse_compat, hrev]

/-- Outgoing stars correspond under a directed-edge isomorphism. -/
def outgoingEquiv
    (v : V₁) :
    G₁.Outgoing v ≃
      G₂.Outgoing (E.vertexEquiv v) where
  toFun := fun e =>
    ⟨E.edgeEquiv e.1, by
      rw [← E.source_compat e.1,
        e.2]⟩
  invFun := fun e => by
    let a := E.edgeEquiv.symm e.1
    refine ⟨a, ?_⟩
    apply E.vertexEquiv.injective
    rw [E.source_compat a]
    change G₂.source e.1 =
      E.vertexEquiv v
    exact e.2
  left_inv := by
    intro e
    apply Subtype.ext
    simp
  right_inv := by
    intro e
    apply Subtype.ext
    simp

/-- Incoming stars also correspond. -/
def incomingEquiv
    (v : V₁) :
    G₁.Incoming v ≃
      G₂.Incoming (E.vertexEquiv v) where
  toFun := fun e =>
    ⟨E.edgeEquiv e.1, by
      rw [← E.target_compat e.1,
        e.2]⟩
  invFun := fun e => by
    let a := E.edgeEquiv.symm e.1
    refine ⟨a, ?_⟩
    apply E.vertexEquiv.injective
    rw [E.target_compat a]
    exact e.2
  left_inv := by
    intro e
    apply Subtype.ext
    simp
  right_inv := by
    intro e
    apply Subtype.ext
    simp

/-- Non-backtracking successor sets correspond edgewise. -/
def successorEquiv
    (e : E₁) :
    G₁.Successor e ≃
      G₂.Successor (E.edgeEquiv e) where
  toFun := fun f =>
    ⟨E.edgeEquiv f.1,
      (E.nonbacktracking_iff e f.1).mp
        f.2⟩
  invFun := fun f =>
    ⟨E.edgeEquiv.symm f.1,
      (E.nonbacktracking_iff
        e (E.edgeEquiv.symm f.1)).mpr
        (by simpa using f.2)⟩
  left_inv := by
    intro f
    apply Subtype.ext
    simp
  right_inv := by
    intro f
    apply Subtype.ext
    simp

end DirectedEdgeEquiv
end CausalGeometry
