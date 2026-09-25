import CausalGeometry.Completion.PadicLatticeIndex
import CausalGeometry.Completion.ZModBruhatTits

namespace CausalGeometry

namespace zmodPrimeLocalTower

variable (p : ℕ) [Fact p.Prime]

/-- The non-unit zero used by the [0:1] projective chart at every finite
p-power level. -/
def zeroNonunit
    (n : ℕ) :
    LocalProjectivePair.Nonunit
      (ZMod (p ^ (n + 1))) :=
  ⟨0, by
    intro h
    exact (not_isUnit_zero) h⟩

/-- Canonical projective point [0:1] at depth n.

This is the branch compatible with the diagonal lattice
p^(n+1) O e1 + O e2. -/
def standardEndPoint
    (n : ℕ) :
    LocalProjectivePair.Line
      (ZMod (p ^ (n + 1))) :=
  Quotient.mk _
    (LocalProjectivePair.infinityChart
      (zeroNonunit p n))

/-- The canonical end point is stable under modular reduction. -/
theorem standardEndPoint_drop
    (n : ℕ) :
    LocalProjectivePair.map
        (drop p n)
        (standardEndPoint p (n + 1)) =
      standardEndPoint p n := by
  rw [
    LocalProjectivePair.map_infinity
      (drop p n)
      (zeroNonunit p (n + 1))
  ]
  rfl

/-- The compatible family [0:1] defines an infinite projective restriction
history. -/
def standardEndHistory :
    (localTower p).projectiveLineTower
      .CompatibleHistory where
  at := standardEndPoint p
  compatible := by
    intro n
    exact standardEndPoint_drop p n

/-- Rooted Bruhat--Tits branching contract for the standard p-adic tower. -/
abbrev StandardBranching :=
  bruhatTitsBranchingContract p

/-- Rooted tree vertex along the standard end.

Index zero is the distinguished root. Index n+1 is the [0:1] point on
projective level n. -/
def standardTreeVertex :
    ℕ →
      BruhatTitsRootedVertex
        (primePowerTower p)
  | 0 =>
      .root
  | n + 1 =>
      .sphere n (standardEndPoint p n)

/-- First child leaving the root along the standard end. -/
def standardRootChild :
    BruhatTitsRootedVertex.Child
      (B := StandardBranching p)
      (.root :
        BruhatTitsRootedVertex
          (primePowerTower p)) :=
  standardEndPoint p 0

/-- At every deeper level, the next [0:1] point is a certified child of the
previous point. -/
def standardSphereChild
    (n : ℕ) :
    BruhatTitsRootedVertex.Child
      (B := StandardBranching p)
      (.sphere n
        (standardEndPoint p n) :
        BruhatTitsRootedVertex
          (primePowerTower p)) :=
  ⟨standardEndPoint p (n + 1),
    standardEndPoint_drop p n⟩

/-- Uniform child selector for the standard infinite ray. -/
def standardNextChild :
    (n : ℕ) →
      BruhatTitsRootedVertex.Child
        (B := StandardBranching p)
        (standardTreeVertex p n)
  | 0 =>
      standardRootChild p
  | n + 1 =>
      standardSphereChild p n

/-- Following the selected child advances exactly one vertex along the
standard ray. -/
theorem childVertex_standardNext
    (n : ℕ) :
    BruhatTitsRootedVertex.childVertex
        (StandardBranching p)
        (standardTreeVertex p n)
        (standardNextChild p n) =
      standardTreeVertex p (n + 1) := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      rfl

/-- Depth along the standard ray agrees with the natural-number index. -/
@[simp] theorem standardTreeVertex_depth
    (n : ℕ) :
    BruhatTitsRootedVertex.depth
        (standardTreeVertex p n) =
      n := by
  cases n <;> rfl

/-- Matching lattice-class ray: root is O^2 and step n moves to
p^(n+1) O e1 + O e2. -/
def standardLatticeClass
    (n : ℕ) :
    RankTwoLattice.HomothetyClass
      (O := PadicLattice.O p)
      (K := PadicLattice.K p) :=
  RankTwoLattice.classOf
    (PadicLattice.diagonalLattice p n)

/-- Every consecutive pair of lattice classes is p-adjacent. -/
theorem standardLatticeClass_adjacent
    (n : ℕ) :
    RankTwoLattice.ClassAdjacent
      (O := PadicLattice.O p)
      (K := PadicLattice.K p)
      p
      (standardLatticeClass p n)
      (standardLatticeClass p (n + 1)) :=
  PadicLattice.diagonalClassAdjacent p n

/-- Calibration condition aligning an abstract projective/lattice
Bruhat--Tits graph isomorphism with the concrete standard p-adic ray.

This is deliberately a separate condition: the graph isomorphism itself does
not choose which end should correspond to the diagonal lattice ray. -/
structure StandardRayCalibration
    (C :
      BruhatTitsLatticeComparison
        (StandardBranching p)
        (PadicLattice.O p)
        (PadicLattice.K p)) : Prop where
  root :
    C.rootClass =
      standardLatticeClass p 0

  sphere :
    ∀ n,
      C.sphereClass n
          (standardEndPoint p n) =
        standardLatticeClass p (n + 1)

namespace StandardRayCalibration

variable
    {C :
      BruhatTitsLatticeComparison
        (StandardBranching p)
        (PadicLattice.O p)
        (PadicLattice.K p)}
    (H : StandardRayCalibration p C)

/-- The calibrated graph comparison sends the whole projective standard ray
to the explicit diagonal lattice ray. -/
theorem vertex_alignment
    (n : ℕ) :
    C.graphEquiv.vertexEquiv
        (standardTreeVertex p n) =
      standardLatticeClass p n := by
  cases n with
  | zero =>
      exact H.root
  | succ n =>
      exact H.sphere n

end StandardRayCalibration
end zmodPrimeLocalTower
end CausalGeometry
