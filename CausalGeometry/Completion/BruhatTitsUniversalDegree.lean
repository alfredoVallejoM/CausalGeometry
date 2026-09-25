import CausalGeometry.Completion.BruhatTitsUniversalGraph
import Mathlib.SetTheory.Cardinal.Finite

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

abbrev Graph :=
  B.directedEdgeSystem

/-- The unique parent link of a non-root sphere vertex. -/
def parentLink
    (n : ℕ)
    (y : LocalProjectivePair.Line (A n)) :
    Link (B := B) :=
  match n with
  | 0 => Sum.inl y
  | k + 1 => Sum.inr ⟨k, y⟩

/-- Parent-oriented edge leaving a sphere vertex toward its parent. -/
def parentEdge
    (n : ℕ)
    (y : LocalProjectivePair.Line (A n)) :
    OrientedEdge (B := B) :=
  (B.parentLink n y, true)

@[simp] theorem source_parentEdge
    (n : ℕ)
    (y : LocalProjectivePair.Line (A n)) :
    B.source (B.parentEdge n y) =
      (.sphere n y :
        Vertex (B := B)) := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      rfl

/-- A child witness gives the downward-oriented link to that child. -/
def childEdge
    {n : ℕ}
    {y : LocalProjectivePair.Line (A n)}
    (c :
      BruhatTitsRootedVertex.Child
        (B := B)
        (.sphere n y :
          BruhatTitsRootedVertex T)) :
    OrientedEdge (B := B) :=
  (Sum.inr ⟨n, c.1⟩, false)

@[simp] theorem source_childEdge
    {n : ℕ}
    {y : LocalProjectivePair.Line (A n)}
    (c :
      BruhatTitsRootedVertex.Child
        (B := B)
        (.sphere n y :
          BruhatTitsRootedVertex T)) :
    B.source (B.childEdge c) =
      (.sphere n y :
        Vertex (B := B)) := by
  change
    (.sphere n
      (LocalProjectivePair.map
        (T.drop n) c.1) :
      Vertex (B := B)) =
    .sphere n y
  rw [c.2]

/-- Root outgoing edges are canonically indexed by the first projective
sphere. -/
def rootOutgoingEquiv :
    B.Graph.Outgoing
        (.root : Vertex (B := B)) ≃
      LocalProjectivePair.Line (A 0) := by
  let f :
      LocalProjectivePair.Line (A 0) →
        B.Graph.Outgoing
          (.root : Vertex (B := B)) :=
    fun x =>
      ⟨(Sum.inl x, false), rfl⟩
  refine Equiv.ofBijective f ?_
  constructor
  · intro x y h
    have hval := congrArg Subtype.val h
    have hlink := (Prod.mk.inj_iff.mp hval).1
    exact Sum.inl.inj hlink
  · intro e
    rcases e with ⟨⟨l, b⟩, hsrc⟩
    cases b with
    | false =>
        cases l with
        | inl x =>
            exact ⟨x, rfl⟩
        | inr nx =>
            simp [Graph, directedEdgeSystem,
              source, lowerVertex] at hsrc
    | true =>
        cases l with
        | inl x =>
            simp [Graph, directedEdgeSystem,
              source, upperVertex] at hsrc
        | inr nx =>
            simp [Graph, directedEdgeSystem,
              source, upperVertex] at hsrc

/-- Parameters for the outgoing star at a non-root vertex: one parent edge
plus all q child edges. -/
abbrev SphereOutgoingParam
    (n : ℕ)
    (y : LocalProjectivePair.Line (A n)) :=
  Sum Unit
    (BruhatTitsRootedVertex.Child
      (B := B)
      (.sphere n y :
        BruhatTitsRootedVertex T))

def sphereParamToOutgoing
    (n : ℕ)
    (y : LocalProjectivePair.Line (A n)) :
    B.SphereOutgoingParam n y →
      B.Graph.Outgoing
        (.sphere n y :
          Vertex (B := B))
  | Sum.inl _ =>
      ⟨B.parentEdge n y,
        B.source_parentEdge n y⟩
  | Sum.inr c =>
      ⟨B.childEdge c,
        B.source_childEdge c⟩

/-- Every outgoing edge at a non-root tree vertex is uniquely either the
parent edge or one child edge. -/
noncomputable def sphereOutgoingEquiv
    (n : ℕ)
    (y : LocalProjectivePair.Line (A n)) :
    B.SphereOutgoingParam n y ≃
      B.Graph.Outgoing
        (.sphere n y :
          Vertex (B := B)) := by
  classical
  refine Equiv.ofBijective
    (B.sphereParamToOutgoing n y) ?_
  constructor
  · intro a b hab
    cases a with
    | inl ua =>
        cases b with
        | inl ub =>
            simp
        | inr cb =>
            have hval :=
              congrArg Subtype.val hab
            simp [sphereParamToOutgoing,
              parentEdge, childEdge] at hval
    | inr ca =>
        cases b with
        | inl ub =>
            have hval :=
              congrArg Subtype.val hab
            simp [sphereParamToOutgoing,
              parentEdge, childEdge] at hval
        | inr cb =>
            apply Sum.inr.inj
            apply Subtype.ext
            have hval :=
              congrArg Subtype.val hab
            have hlink :=
              (Prod.mk.inj_iff.mp hval).1
            have hsigma :=
              Sum.inr.inj hlink
            exact
              (Sigma.mk.inj_iff.mp hsigma).2
  · intro e
    rcases e with ⟨⟨l, b⟩, hsrc⟩
    cases b with
    | false =>
        cases l with
        | inl x =>
            simp [Graph, directedEdgeSystem,
              source, lowerVertex] at hsrc
        | inr nx =>
            rcases nx with ⟨k, x⟩
            change
              (.sphere k
                (LocalProjectivePair.map
                  (T.drop k) x) :
                Vertex (B := B)) =
              .sphere n y at hsrc
            cases hsrc
            let c :
                BruhatTitsRootedVertex.Child
                  (B := B)
                  (.sphere k
                    (LocalProjectivePair.map
                      (T.drop k) x) :
                    BruhatTitsRootedVertex T) :=
              ⟨x, rfl⟩
            exact ⟨Sum.inr c, rfl⟩
    | true =>
        cases l with
        | inl x =>
            change
              (.sphere 0 x :
                Vertex (B := B)) =
              .sphere n y at hsrc
            cases hsrc
            exact ⟨Sum.inl (), rfl⟩
        | inr nx =>
            rcases nx with ⟨k, x⟩
            change
              (.sphere (k + 1) x :
                Vertex (B := B)) =
              .sphere n y at hsrc
            cases hsrc
            exact ⟨Sum.inl (), rfl⟩

/-- Root degree is q+1. -/
theorem root_outgoing_natCard :
    Nat.card
        (B.Graph.Outgoing
          (.root : Vertex (B := B))) =
      T.q + 1 := by
  rw [Nat.card_congr B.rootOutgoingEquiv]
  exact B.projective_card_zero

/-- Every non-root vertex also has degree q+1. -/
theorem sphere_outgoing_natCard
    (n : ℕ)
    (y : LocalProjectivePair.Line (A n)) :
    Nat.card
        (B.Graph.Outgoing
          (.sphere n y :
            Vertex (B := B))) =
      T.q + 1 := by
  rw [← Nat.card_congr
    (B.sphereOutgoingEquiv n y)]
  change
    Nat.card
      (Sum Unit
        (BruhatTitsRootedVertex.Child
          (B := B)
          (.sphere n y :
            BruhatTitsRootedVertex T))) =
      _
  rw [Nat.card_sum, Nat.card_unique]
  rw [B.sphere_child_natCard n y]
  omega

/-- Universal Bruhat--Tits tree is locally (q+1)-regular. -/
theorem outgoing_natCard
    (v : Vertex (B := B)) :
    Nat.card (B.Graph.Outgoing v) =
      T.q + 1 := by
  cases v with
  | root =>
      exact B.root_outgoing_natCard
  | sphere n y =>
      exact B.sphere_outgoing_natCard n y

end BruhatTitsUniversalGraph
end CausalGeometry
