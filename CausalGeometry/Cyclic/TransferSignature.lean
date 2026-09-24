import CausalGeometry.Cyclic.TransferDeterminant

namespace CausalGeometry

/-- Decategorized finite transfer data stable under changes of state
presentation: all power traces together with the universal determinant
polynomial. -/
structure FiniteTransferSignature where
  traceSequence : ℕ → ℤ
  determinantPolynomial : ℤ[X]

namespace FiniteTransferSignature

/-- Signature carried by one finite directed-edge/Hashimoto realization. -/
def ofHashimoto
    {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    (G : FiniteDirectedEdgeSystem Vertex Edge) :
    FiniteTransferSignature where
  traceSequence n :=
    (G.hashimotoTransfer ℤ).tracePower n
  determinantPolynomial :=
    G.hashimotoDeterminantPolynomial

@[simp] theorem ofHashimoto_trace
    {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    (G : FiniteDirectedEdgeSystem Vertex Edge)
    (n : ℕ) :
    (ofHashimoto G).traceSequence n =
      (G.hashimotoTransfer ℤ).tracePower n := rfl

@[simp] theorem ofHashimoto_determinant
    {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    (G : FiniteDirectedEdgeSystem Vertex Edge) :
    (ofHashimoto G).determinantPolynomial =
      G.hashimotoDeterminantPolynomial := rfl

end FiniteTransferSignature

/-- Primitive-period data kept separate from the transfer signature. -/
structure PrimitiveSignature where
  primitive : ℕ → ℤ

namespace PrimitiveSignature

def ofComparison
    {Vertex Edge : Type*}
    [Fintype Vertex] [DecidableEq Vertex]
    [Fintype Edge] [DecidableEq Edge]
    {G : FiniteDirectedEdgeSystem Vertex Edge}
    (C : HashimotoPrimitiveComparison G) :
    PrimitiveSignature where
  primitive := C.counts.primitive

end PrimitiveSignature
end CausalGeometry
