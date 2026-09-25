import CausalGeometry.Cyclic.TransferSignatureInvariant

namespace CausalGeometry

universe u₁ u₂

/-- Isomorphism of finite directed-edge systems.

Both vertices and oriented edges may be represented by different Lean types.
The equivalence must preserve incidence and edge reversal. -/
structure FiniteDirectedEdgeEquiv
    {V₁ E₁ : Type u₁}
    {V₂ E₂ : Type u₂}
    [Fintype V₁] [DecidableEq V₁]
    [Fintype E₁] [DecidableEq E₁]
    [Fintype V₂] [DecidableEq V₂]
    [Fintype E₂] [DecidableEq E₂]
    (G₁ : FiniteDirectedEdgeSystem V₁ E₁)
    (G₂ : FiniteDirectedEdgeSystem V₂ E₂) where
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

namespace FiniteDirectedEdgeEquiv

variable
    {V₁ E₁ : Type u₁}
    {V₂ E₂ : Type u₂}
    [Fintype V₁] [DecidableEq V₁]
    [Fintype E₁] [DecidableEq E₁]
    [Fintype V₂] [DecidableEq V₂]
    [Fintype E₂] [DecidableEq E₂]
    {G₁ : FiniteDirectedEdgeSystem V₁ E₁}
    {G₂ : FiniteDirectedEdgeSystem V₂ E₂}
    (E : FiniteDirectedEdgeEquiv G₁ G₂)

/-- Non-backtracking adjacency is invariant under directed-edge isomorphism. -/
theorem nonbacktracking_iff
    (e f : E₁) :
    G₁.Nonbacktracking e f ↔
      G₂.Nonbacktracking
        (E.edgeEquiv e) (E.edgeEquiv f) := by
  constructor
  · intro h
    constructor
    · apply E.vertexEquiv.injective
      rw [← E.target_compat e, ← E.source_compat f]
      exact congrArg E.vertexEquiv h.1
    · intro hrev
      apply h.2
      apply E.edgeEquiv.injective
      rw [E.reverse_compat]
      exact hrev
  · intro h
    constructor
    · have hinc :=
        congrArg E.vertexEquiv.symm h.1
      simpa [E.target_compat, E.source_compat] using hinc
    · intro hrev
      apply h.2
      rw [← E.reverse_compat, hrev]

/-- Hashimoto weights are transported exactly by the edge equivalence. -/
theorem hashimotoWeight_compat
    (e f : E₁) :
    G₂.hashimotoWeight
        (R := ℤ)
        (E.edgeEquiv e) (E.edgeEquiv f) =
      G₁.hashimotoWeight
        (R := ℤ) e f := by
  simp [FiniteDirectedEdgeSystem.hashimotoWeight,
    E.nonbacktracking_iff e f]

/-- Reindexing the first Hashimoto matrix along the edge equivalence yields the
second Hashimoto matrix entrywise. -/
theorem reindexed_hashimoto_matrix_eq :
    ((G₁.hashimotoTransfer ℤ).reindex E.edgeEquiv).matrix =
      (G₂.hashimotoTransfer ℤ).matrix := by
  ext e f
  change
    G₁.hashimotoWeight
        (R := ℤ)
        (E.edgeEquiv.symm e)
        (E.edgeEquiv.symm f) =
      G₂.hashimotoWeight
        (R := ℤ) e f
  simpa using
    (E.hashimotoWeight_compat
      (E.edgeEquiv.symm e)
      (E.edgeEquiv.symm f)).symm

/-- Equality of matrices on the reindexed system yields equality of every
trace power. -/
theorem reindexed_tracePower_eq
    (n : ℕ) :
    ((G₁.hashimotoTransfer ℤ).reindex E.edgeEquiv).tracePower n =
      (G₂.hashimotoTransfer ℤ).tracePower n := by
  unfold FiniteTransferSystem.tracePower
  rw [E.reindexed_hashimoto_matrix_eq]

/-- And equality of determinant polynomials. -/
theorem reindexed_determinantPolynomial_eq :
    ((G₁.hashimotoTransfer ℤ).reindex E.edgeEquiv).determinantPolynomial =
      (G₂.hashimotoTransfer ℤ).determinantPolynomial := by
  unfold FiniteTransferSystem.determinantPolynomial
  rw [E.reindexed_hashimoto_matrix_eq]

/-- Directed-edge isomorphisms preserve all Hashimoto trace powers. -/
theorem tracePower_eq
    (n : ℕ) :
    (G₁.hashimotoTransfer ℤ).tracePower n =
      (G₂.hashimotoTransfer ℤ).tracePower n := by
  rw [← E.reindexed_tracePower_eq n]
  exact
    ((G₁.hashimotoTransfer ℤ).reindex_tracePower
      E.edgeEquiv n).symm

/-- Directed-edge isomorphisms preserve the universal Hashimoto determinant. -/
theorem determinantPolynomial_eq :
    G₁.hashimotoDeterminantPolynomial =
      G₂.hashimotoDeterminantPolynomial := by
  change
    (G₁.hashimotoTransfer ℤ).determinantPolynomial =
      (G₂.hashimotoTransfer ℤ).determinantPolynomial
  rw [← E.reindexed_determinantPolynomial_eq]
  exact
    ((G₁.hashimotoTransfer ℤ).reindex_determinantPolynomial
      E.edgeEquiv).symm

/-- Therefore the complete finite transfer signature is a graph-isomorphism
invariant. -/
theorem transferSignature_eq :
    FiniteTransferSignature.ofHashimoto G₁ =
      FiniteTransferSignature.ofHashimoto G₂ := by
  apply FiniteTransferSignature.ext
  · funext n
    exact E.tracePower_eq n
  · exact E.determinantPolynomial_eq

end FiniteDirectedEdgeEquiv
end CausalGeometry
