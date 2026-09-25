import CausalGeometry.Cyclic.DirectedEdge
import CausalGeometry.Cyclic.TransferSignatureInvariant

namespace CausalGeometry

universe u₁ u₂

/-- Locally bijective quotient/covering map between directed-edge systems.

The source may be infinite and the target finite. Global injectivity is not
required; indeed global identifications are precisely what can create quotient
cycles. Local outgoing stars, however, are required to be equivalent. -/
structure DirectedEdgeCovering
    {V₁ E₁ : Type u₁}
    {V₂ E₂ : Type u₂}
    (G : DirectedEdgeSystem V₁ E₁)
    (H : DirectedEdgeSystem V₂ E₂) where
  vertexMap : V₁ → V₂
  edgeMap : E₁ → E₂

  source_compat :
    ∀ e,
      vertexMap (G.source e) =
        H.source (edgeMap e)

  target_compat :
    ∀ e,
      vertexMap (G.target e) =
        H.target (edgeMap e)

  reverse_compat :
    ∀ e,
      edgeMap (G.reverse e) =
        H.reverse (edgeMap e)

  vertex_surjective :
    Function.Surjective vertexMap

  edge_surjective :
    Function.Surjective edgeMap

  /-- Local covering condition: outgoing stars are preserved bijectively. -/
  outgoingEquiv :
    ∀ v, G.Outgoing v ≃
      H.Outgoing (vertexMap v)

  outgoingEquiv_val :
    ∀ v (e : G.Outgoing v),
      ((outgoingEquiv v e : H.Outgoing (vertexMap v)) : E₂) =
        edgeMap e.1

namespace DirectedEdgeCovering

variable
    {V₁ E₁ : Type u₁}
    {V₂ E₂ : Type u₂}
    {G : DirectedEdgeSystem V₁ E₁}
    {H : DirectedEdgeSystem V₂ E₂}
    (C : DirectedEdgeCovering G H)

/-- A local star equivalence implies that edgeMap is injective on all edges
leaving a fixed source vertex. -/
theorem edgeMap_injective_on_outgoing
    (v : V₁)
    {e f : E₁}
    (he : G.source e = v)
    (hf : G.source f = v)
    (hmap : C.edgeMap e = C.edgeMap f) :
    e = f := by
  let e' : G.Outgoing v := ⟨e, he⟩
  let f' : G.Outgoing v := ⟨f, hf⟩
  have hEq :
      C.outgoingEquiv v e' =
        C.outgoingEquiv v f' := by
    apply Subtype.ext
    simpa [e', f'] using hmap
  exact congrArg Subtype.val
    ((C.outgoingEquiv v).injective hEq)

/-- Non-backtracking adjacency maps forward through a covering. -/
theorem map_nonbacktracking
    {e f : E₁}
    (h : G.Nonbacktracking e f) :
    H.Nonbacktracking
      (C.edgeMap e) (C.edgeMap f) := by
  constructor
  · rw [← C.target_compat e, ← C.source_compat f]
    exact congrArg C.vertexMap h.1
  · intro hrev
    have hmap :
        C.edgeMap f =
          C.edgeMap (G.reverse e) := by
      rw [C.reverse_compat]
      exact hrev
    have hf :
        G.source f = G.target e :=
      h.1.symm
    have hr :
        G.source (G.reverse e) =
          G.target e :=
      G.source_reverse e
    exact h.2
      (C.edgeMap_injective_on_outgoing
        (G.target e) hf hr hmap)

/-- The immediate reverse relation is preserved exactly. -/
@[simp] theorem map_reverse
    (e : E₁) :
    C.edgeMap (G.reverse e) =
      H.reverse (C.edgeMap e) :=
  C.reverse_compat e

/-- Incidence is preserved at both endpoints. -/
theorem map_endpoints
    (e : E₁) :
    (C.vertexMap (G.source e),
      C.vertexMap (G.target e)) =
      (H.source (C.edgeMap e),
        H.target (C.edgeMap e)) := by
  simp [C.source_compat, C.target_compat]

end DirectedEdgeCovering

/-- A finite quotient of an arbitrary directed-edge source. -/
structure FiniteDirectedEdgeQuotient
    {V E : Type u₁}
    (G : DirectedEdgeSystem V E) where
  QuotVertex : Type u₂
  QuotEdge : Type u₂

  vertexFintype : Fintype QuotVertex
  vertexDecEq : DecidableEq QuotVertex
  edgeFintype : Fintype QuotEdge
  edgeDecEq : DecidableEq QuotEdge

  finiteSystem :
    FiniteDirectedEdgeSystem QuotVertex QuotEdge

  covering :
    DirectedEdgeCovering G finiteSystem.toDirected

namespace FiniteDirectedEdgeQuotient

variable
    {V E : Type u₁}
    {G : DirectedEdgeSystem V E}
    (Q : FiniteDirectedEdgeQuotient.{u₁, u₂} G)

noncomputable local instance :
    Fintype Q.QuotVertex := Q.vertexFintype

noncomputable local instance :
    DecidableEq Q.QuotVertex := Q.vertexDecEq

noncomputable local instance :
    Fintype Q.QuotEdge := Q.edgeFintype

noncomputable local instance :
    DecidableEq Q.QuotEdge := Q.edgeDecEq

/-- Hashimoto transfer system carried by the finite quotient. -/
noncomputable def hashimotoTransfer :
    FiniteTransferSystem ℤ :=
  Q.finiteSystem.hashimotoTransfer ℤ

/-- Stable signature of the finite quotient. -/
noncomputable def transferSignature :
    FiniteTransferSignature :=
  FiniteTransferSignature.ofHashimoto Q.finiteSystem

end FiniteDirectedEdgeQuotient
end CausalGeometry
