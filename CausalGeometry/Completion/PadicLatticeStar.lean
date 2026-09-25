import CausalGeometry.Completion.PadicRootChildEquiv
import CausalGeometry.Completion.RankTwoLatticeFrame
import CausalGeometry.Completion.RankTwoLatticeTransport

namespace CausalGeometry

namespace PadicLattice

variable (p : ℕ) [Fact p.Prime]

/-- Index-p child of an arbitrary p-adic rank-two lattice representative. -/
structure ChildAt
    (L : RankTwoLattice (O p) (K p)) where
  lattice :
    RankTwoLattice (O p) (K p)

  step :
    RankTwoLattice.IndexStep p
      L lattice

namespace ChildAt

variable
    {p : ℕ} [Fact p.Prime]
    {L M : RankTwoLattice (O p) (K p)}

@[ext] theorem ext
    {C D : ChildAt p L}
    (h : C.lattice = D.lattice) :
    C = D := by
  cases C
  cases D
  simp_all

/-- Transport a child along an ambient linear equivalence. -/
def mapLinearEquiv
    (E :
      (K p × K p) ≃ₗ[K p]
        (K p × K p))
    (C : ChildAt p L) :
    ChildAt p (L.mapLinearEquiv E) where
  lattice :=
    C.lattice.mapLinearEquiv E
  step :=
    C.step.mapLinearEquiv E

@[simp] theorem mapLinearEquiv_lattice
    (E :
      (K p × K p) ≃ₗ[K p]
        (K p × K p))
    (C : ChildAt p L) :
    (C.mapLinearEquiv E).lattice =
      C.lattice.mapLinearEquiv E :=
  rfl

/-- Mapping by an equivalence and then its inverse returns the original child,
up to the canonical equality of parent lattices. -/
theorem map_symm_map_lattice
    (E :
      (K p × K p) ≃ₗ[K p]
        (K p × K p))
    (C : ChildAt p L) :
    ((C.mapLinearEquiv E).lattice.mapLinearEquiv E.symm) =
      C.lattice := by
  simp

end ChildAt

abbrev Root :=
  PadicRootChild.Root p

/-- A compatible frame of a p-adic lattice. -/
abbrev LatticeFrame
    (L : RankTwoLattice (O p) (K p)) :=
  RankTwoLattice.Frame L

/-- Every p-adic rank-two lattice has a canonical compatible frame. -/
noncomputable def canonicalFrame
    (L : RankTwoLattice (O p) (K p)) :
    LatticeFrame p L :=
  RankTwoLattice.Frame.canonical L

namespace LatticeFrame

variable
    {p : ℕ} [Fact p.Prime]
    {L : RankTwoLattice (O p) (K p)}
    (F : LatticeFrame p L)

/-- The standard root lattice is carried exactly to L by the ambient
equivalence associated to the frame. -/
theorem map_root_eq :
    (Root p).mapLinearEquiv
        F.ambientEquiv =
      L := by
  apply RankTwoLattice.ext
  ext x
  constructor
  · intro hx
    rcases hx with
      ⟨y, hyRoot, hyE⟩
    rw [
      PadicLattice.diagonalLattice_zero_carrier
    ] at hyRoot
    rcases hyRoot with
      ⟨a, ha⟩
    have hyCoord :
        y =
          RankTwoLattice.Frame.algebraMapProd
            (O := O p) (K := K p) a := by
      simpa [
        RankTwoLattice.Frame.algebraMapProd
      ] using ha
    subst y
    rw [
      F.ambientEquiv_algebraMapProd
    ] at hyE
    rw [← hyE]
    exact
      (F.latticeEquiv a).2
  · intro hx
    let z : L.carrier :=
      ⟨x, hx⟩
    rcases F.latticeEquiv.surjective z with
      ⟨a, ha⟩
    let y : K p × K p :=
      RankTwoLattice.Frame.algebraMapProd
        (O := O p) (K := K p) a
    have hyRoot :
        y ∈ (Root p).carrier := by
      rw [
        PadicLattice.diagonalLattice_zero_carrier
      ]
      exact ⟨a, rfl⟩
    refine ⟨y, hyRoot, ?_⟩
    rw [
      F.ambientEquiv_algebraMapProd
    ]
    exact congrArg Subtype.val ha

/-- Inverse statement: L is carried back to the standard root by the inverse
ambient equivalence. -/
theorem map_to_root_eq :
    L.mapLinearEquiv
        F.ambientEquiv.symm =
      Root p := by
  have h :=
    congrArg
      (fun M =>
        M.mapLinearEquiv
          F.ambientEquiv.symm)
      F.map_root_eq
  simpa using h.symm

/-- Transport a standard-root child to a child of L. -/
def childFromRoot
    (C : PadicRootChild.Child p) :
    ChildAt p L where
  lattice :=
    C.lattice.mapLinearEquiv
      F.ambientEquiv
  step := by
    have h :=
      C.step.mapLinearEquiv
        F.ambientEquiv
    rw [F.map_root_eq] at h
    exact h

/-- Transport a child of L back to the standard root. -/
def childToRoot
    (C : ChildAt p L) :
    PadicRootChild.Child p where
  lattice :=
    C.lattice.mapLinearEquiv
      F.ambientEquiv.symm
  step := by
    have h :=
      C.step.mapLinearEquiv
        F.ambientEquiv.symm
    rw [F.map_to_root_eq] at h
    exact h

@[simp] theorem childToRoot_fromRoot
    (C : PadicRootChild.Child p) :
    F.childToRoot
        (F.childFromRoot C) =
      C := by
  apply PadicRootChild.Child.ext
  simp [childToRoot, childFromRoot]

@[simp] theorem childFromRoot_toRoot
    (C : ChildAt p L) :
    F.childFromRoot
        (F.childToRoot C) =
      C := by
  apply ChildAt.ext
  simp [childToRoot, childFromRoot]

/-- The star of every framed p-adic lattice representative is equivalent to
the star of the standard root. -/
noncomputable def childEquivRoot :
    ChildAt p L ≃
      PadicRootChild.Child p where
  toFun :=
    F.childToRoot
  invFun :=
    F.childFromRoot
  left_inv :=
    F.childFromRoot_toRoot
  right_inv :=
    F.childToRoot_fromRoot

/-- Every p-adic lattice has a projective classification of its index-p
children. -/
noncomputable def childEquivProjective :
    ChildAt p L ≃
      PadicRootChild.P1 p :=
  F.childEquivRoot.trans
    (PadicRootChild.childEquivProjective p)

/-- Every p-adic rank-two lattice representative has exactly p+1 oriented
index-p children. -/
theorem child_natCard :
    Nat.card (ChildAt p L) =
      p + 1 := by
  rw [Nat.card_congr
    F.childEquivProjective]
  exact
    PadicRootChild.child_natCard p

/-- Every child of L has a unique projective residue coordinate relative to
the chosen frame. -/
theorem every_child_has_unique_projective
    (C : ChildAt p L) :
    ∃! q : PadicRootChild.P1 p,
      (F.childEquivProjective).symm q =
        C := by
  refine ⟨F.childEquivProjective C,
    ?_, ?_⟩
  · simp
  · intro q hq
    apply F.childEquivProjective.injective
    simpa using congrArg
      F.childEquivProjective hq

end LatticeFrame

/-- Frame-independent existence of a projective classification at every
p-adic rank-two lattice. Different frames may reparameterize P1(Fp), but the
child set and its cardinality are intrinsic. -/
theorem exists_childEquivProjective
    (L : RankTwoLattice (O p) (K p)) :
    Nonempty
      (ChildAt p L ≃
        PadicRootChild.P1 p) :=
  ⟨(canonicalFrame p L).childEquivProjective⟩

/-- Intrinsic degree statement on lattice representatives. -/
theorem childAt_natCard
    (L : RankTwoLattice (O p) (K p)) :
    Nat.card (ChildAt p L) =
      p + 1 :=
  (canonicalFrame p L).child_natCard

end PadicLattice
end CausalGeometry
