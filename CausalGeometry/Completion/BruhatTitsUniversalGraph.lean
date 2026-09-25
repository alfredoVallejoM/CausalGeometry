import CausalGeometry.Completion.BruhatTitsRootedTree
import CausalGeometry.Cyclic.DirectedEdge

namespace CausalGeometry

universe u

namespace BruhatTitsUniversalGraph

variable
    {A : ℕ → Type u}
    [∀ n, CommRing (A n)]
    [∀ n, IsLocalRing (A n)]
    [∀ n, Fintype (A n)]
    {T : PrimePowerLocalRingTower A}
    (B : BruhatTitsBranchingContract T)

/-- Universal rooted Bruhat--Tits vertex type. -/
abbrev Vertex :=
  BruhatTitsRootedVertex T

/-- Every non-root vertex determines the unique undirected link to its parent.
Root links are parameterized by level-zero projective points; deeper links are
parameterized by their child point. -/
abbrev Link :=
  Sum
    (LocalProjectivePair.Line (A 0))
    (Σ n : ℕ,
      LocalProjectivePair.Line (A (n + 1)))

/-- Two orientations for every universal-tree link. -/
abbrev OrientedEdge :=
  Link (B := B) × Bool

def lowerVertex :
    Link (B := B) → Vertex (B := B)
  | Sum.inl x =>
      .root
  | Sum.inr nx =>
      .sphere nx.1
        (LocalProjectivePair.map
          (T.drop nx.1) nx.2)

def upperVertex :
    Link (B := B) → Vertex (B := B)
  | Sum.inl x =>
      .sphere 0 x
  | Sum.inr nx =>
      .sphere (nx.1 + 1) nx.2

def source
    (e : OrientedEdge (B := B)) :
    Vertex (B := B) :=
  if e.2 then B.upperVertex e.1
  else B.lowerVertex e.1

def target
    (e : OrientedEdge (B := B)) :
    Vertex (B := B) :=
  if e.2 then B.lowerVertex e.1
  else B.upperVertex e.1

def reverse
    (e : OrientedEdge (B := B)) :
    OrientedEdge (B := B) :=
  (e.1, !e.2)

@[simp] theorem reverse_reverse
    (e : OrientedEdge (B := B)) :
    B.reverse (B.reverse e) = e := by
  rcases e with ⟨l, b⟩
  cases b <;> rfl

@[simp] theorem source_reverse
    (e : OrientedEdge (B := B)) :
    B.source (B.reverse e) =
      B.target e := by
  rcases e with ⟨l, b⟩
  cases b <;> rfl

@[simp] theorem target_reverse
    (e : OrientedEdge (B := B)) :
    B.target (B.reverse e) =
      B.source e := by
  rcases e with ⟨l, b⟩
  cases b <;> rfl

theorem reverse_ne
    (e : OrientedEdge (B := B)) :
    B.reverse e ≠ e := by
  rcases e with ⟨l, b⟩
  cases b <;> decide

/-- Infinite universal directed-edge tree associated to the projective
restriction tower. -/
def directedEdgeSystem :
    DirectedEdgeSystem
      (Vertex (B := B))
      (OrientedEdge (B := B)) where
  source := B.source
  target := B.target
  reverse := B.reverse
  reverse_involutive := B.reverse_reverse
  source_reverse := B.source_reverse
  target_reverse := B.target_reverse
  reverse_ne := B.reverse_ne

/-- Depth of the source endpoint of an oriented edge. -/
def sourceDepth
    (e : OrientedEdge (B := B)) :
    ℕ :=
  BruhatTitsRootedVertex.depth (B.source e)

/-- Depth of the target endpoint. -/
def targetDepth
    (e : OrientedEdge (B := B)) :
    ℕ :=
  BruhatTitsRootedVertex.depth (B.target e)

/-- Every universal-tree edge joins adjacent depth layers. -/
theorem depth_adjacent
    (e : OrientedEdge (B := B)) :
    B.sourceDepth e + 1 = B.targetDepth e ∨
      B.targetDepth e + 1 = B.sourceDepth e := by
  rcases e with ⟨l, b⟩
  cases l with
  | inl x =>
      cases b <;> simp [sourceDepth, targetDepth, source,
        target, lowerVertex, upperVertex,
        BruhatTitsRootedVertex.depth]
  | inr nx =>
      rcases nx with ⟨n, x⟩
      cases b <;> simp [sourceDepth, targetDepth, source,
        target, lowerVertex, upperVertex,
        BruhatTitsRootedVertex.depth, Nat.add_assoc]

end BruhatTitsUniversalGraph
end CausalGeometry
