import CausalGeometry.Completion.BruhatTitsRootedTree
import CausalGeometry.Cyclic.TransferSignature

namespace CausalGeometry

universe u

namespace BruhatTitsFiniteGraph

variable
    {A : ℕ → Type u}
    [∀ n, CommRing (A n)]
    [∀ n, IsLocalRing (A n)]
    [∀ n, Fintype (A n)]
    {T : PrimePowerLocalRingTower A}
    (B : BruhatTitsBranchingContract T)

/-- Vertices in the rooted ball through projective level N.

The root has depth zero; projective level n has rooted depth n+1. -/
abbrev Vertex (N : ℕ) :=
  Sum Unit
    (Σ n : Fin (N + 1),
      LocalProjectivePair.Line (A n.1))

/-- Undirected links in the rooted ball through projective level N.

The first summand consists of root-to-level-zero links.  The second summand
consists of links from level n to n+1 for n < N; such a link is parameterized
by its child point, because the parent is its projective reduction. -/
abbrev Link (N : ℕ) :=
  Sum
    (LocalProjectivePair.Line (A 0))
    (Σ n : Fin N,
      LocalProjectivePair.Line (A (n.1 + 1)))

/-- Each undirected link has two Boolean orientations. -/
abbrev OrientedEdge (N : ℕ) :=
  Link (B := B) N × Bool

noncomputable instance vertexFintype (N : ℕ) :
    Fintype (Vertex (B := B) N) :=
  Fintype.ofFinite _

noncomputable instance vertexDecidableEq (N : ℕ) :
    DecidableEq (Vertex (B := B) N) :=
  Classical.decEq _

noncomputable instance linkFintype (N : ℕ) :
    Fintype (Link (B := B) N) :=
  Fintype.ofFinite _

noncomputable instance linkDecidableEq (N : ℕ) :
    DecidableEq (Link (B := B) N) :=
  Classical.decEq _

noncomputable instance orientedEdgeFintype (N : ℕ) :
    Fintype (OrientedEdge (B := B) N) :=
  inferInstance

noncomputable instance orientedEdgeDecidableEq (N : ℕ) :
    DecidableEq (OrientedEdge (B := B) N) :=
  Classical.decEq _

/-- Parent endpoint of one undirected tree link. -/
def lowerVertex {N : ℕ} :
    Link (B := B) N → Vertex (B := B) N
  | Sum.inl x =>
      Sum.inl ()
  | Sum.inr nx =>
      Sum.inr
        ⟨nx.1.castSucc,
          LocalProjectivePair.map
            (T.drop nx.1.1) nx.2⟩

/-- Child endpoint of one undirected tree link. -/
def upperVertex {N : ℕ} :
    Link (B := B) N → Vertex (B := B) N
  | Sum.inl x =>
      Sum.inr
        ⟨⟨0, Nat.succ_pos N⟩, x⟩
  | Sum.inr nx =>
      Sum.inr
        ⟨nx.1.succ, nx.2⟩

def edgeSource {N : ℕ}
    (e : OrientedEdge (B := B) N) :
    Vertex (B := B) N :=
  if e.2 then B.upperVertex e.1
  else B.lowerVertex e.1

def edgeTarget {N : ℕ}
    (e : OrientedEdge (B := B) N) :
    Vertex (B := B) N :=
  if e.2 then B.lowerVertex e.1
  else B.upperVertex e.1

def reverse {N : ℕ}
    (e : OrientedEdge (B := B) N) :
    OrientedEdge (B := B) N :=
  (e.1, !e.2)

@[simp] theorem reverse_reverse {N : ℕ}
    (e : OrientedEdge (B := B) N) :
    B.reverse (B.reverse e) = e := by
  rcases e with ⟨l, b⟩
  cases b <;> rfl

@[simp] theorem edgeSource_reverse {N : ℕ}
    (e : OrientedEdge (B := B) N) :
    B.edgeSource (B.reverse e) =
      B.edgeTarget e := by
  rcases e with ⟨l, b⟩
  cases b <;> rfl

@[simp] theorem edgeTarget_reverse {N : ℕ}
    (e : OrientedEdge (B := B) N) :
    B.edgeTarget (B.reverse e) =
      B.edgeSource e := by
  rcases e with ⟨l, b⟩
  cases b <;> rfl

theorem reverse_ne {N : ℕ}
    (e : OrientedEdge (B := B) N) :
    B.reverse e ≠ e := by
  rcases e with ⟨l, b⟩
  cases b <;> decide

/-- The finite rooted Bruhat--Tits ball supplies exactly the directed-edge
interface consumed by the generic Hashimoto development. -/
noncomputable def directedEdgeSystem (N : ℕ) :
    FiniteDirectedEdgeSystem
      (Vertex (B := B) N)
      (OrientedEdge (B := B) N) where
  source := B.edgeSource
  target := B.edgeTarget
  reverse := B.reverse
  reverse_involutive := B.reverse_reverse
  source_reverse := B.edgeSource_reverse
  target_reverse := B.edgeTarget_reverse
  reverse_ne := B.reverse_ne

/-- Stable finite transfer signature of the depth-N Bruhat--Tits truncation. -/
noncomputable def transferSignature (N : ℕ) :
    FiniteTransferSignature :=
  FiniteTransferSignature.ofHashimoto
    (B.directedEdgeSystem N)

/-- Universal Hashimoto determinant polynomial of the finite rooted ball. -/
noncomputable def determinantPolynomial (N : ℕ) :
    ℤ[X] :=
  (B.directedEdgeSystem N).hashimotoDeterminantPolynomial

/-- Hashimoto trace sequence of the finite rooted ball. -/
noncomputable def traceSequence (N : ℕ) :
    ℕ → ℤ :=
  fun n =>
    ((B.directedEdgeSystem N).hashimotoTransfer ℤ).tracePower n

end BruhatTitsFiniteGraph
end CausalGeometry
