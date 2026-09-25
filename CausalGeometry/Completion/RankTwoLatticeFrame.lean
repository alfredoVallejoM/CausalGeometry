import CausalGeometry.Completion.RankTwoLatticeStandard
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Data.Fintype.EquivFin

namespace CausalGeometry

universe u v

namespace RankTwoLattice

variable
    {O : Type u} {K : Type v}
    [CommRing O] [Field K] [Algebra O K]

section PID

variable
    [IsDomain O]
    [IsPrincipalIdealRing O]
    [IsFractionRing O K]
    [Module.IsTorsionFree O K]

/-- Canonical equivalence between the chosen basis index of a rank-two lattice
and Fin 2. -/
noncomputable def basisIndexEquivFinTwo
    (L : RankTwoLattice O K) :
    Module.Free.ChooseBasisIndex O L.carrier ≃
      Fin 2 := by
  letI : Module.Finite O L.carrier :=
    Module.Finite.of_fg L.fg
  apply Fintype.equivFinOfCardEq
  rw [← Module.finrank_eq_card_basis (L.basis)]
  exact L.finrank_eq_two

/-- A frame of a lattice consists of compatible O- and K-bases indexed by the
same standard two-element type.

The ambient basis is not an independent choice: compatibility requires it to
be exactly the coercion of the lattice basis into K^2. -/
structure Frame
    (L : RankTwoLattice O K) where
  latticeBasis :
    Basis (Fin 2) O L.carrier

  ambientBasis :
    Basis (Fin 2) K (K × K)

  compatible :
    ∀ i : Fin 2,
      ambientBasis i =
        (latticeBasis i).1

namespace Frame

variable {L : RankTwoLattice O K}

/-- Canonical frame obtained by reindexing the chosen lattice basis and its
canonical extension to K^2. -/
noncomputable def canonical
    (L : RankTwoLattice O K) :
    Frame L where
  latticeBasis :=
    L.basis.reindex
      (L.basisIndexEquivFinTwo)
  ambientBasis :=
    L.ambientBasis.reindex
      (L.basisIndexEquivFinTwo)
  compatible := by
    intro i
    simp [
      basisIndexEquivFinTwo,
      Basis.reindex_apply,
      RankTwoLattice.ambientBasis_apply
    ]

/-- O-linear coordinate equivalence from the standard plane to the lattice. -/
noncomputable def latticeEquiv
    (F : Frame L) :
    (O × O) ≃ₗ[O] L.carrier :=
  Basis.equiv
    (Basis.finTwoProd O)
    F.latticeBasis
    (Equiv.refl (Fin 2))

/-- K-linear ambient change of basis sending the standard K^2 basis to the
ambient basis determined by the lattice frame. -/
noncomputable def ambientEquiv
    (F : Frame L) :
    (K × K) ≃ₗ[K] (K × K) :=
  Basis.equiv
    (Basis.finTwoProd K)
    F.ambientBasis
    (Equiv.refl (Fin 2))

@[simp] theorem latticeEquiv_basis
    (F : Frame L)
    (i : Fin 2) :
    F.latticeEquiv
        (Basis.finTwoProd O i) =
      F.latticeBasis i := by
  exact Basis.equiv_apply _ _ _ _

@[simp] theorem ambientEquiv_basis
    (F : Frame L)
    (i : Fin 2) :
    F.ambientEquiv
        (Basis.finTwoProd K i) =
      F.ambientBasis i := by
  exact Basis.equiv_apply _ _ _ _

/-- Coordinatewise algebra-map embedding O^2 -> K^2. -/
def algebraMapProd :
    (O × O) →ₗ[O] (K × K) where
  toFun := fun x =>
    (algebraMap O K x.1,
      algebraMap O K x.2)
  map_add' := by
    intro x y
    ext <;> simp
  map_smul' := by
    intro a x
    ext <;>
      simp [Algebra.smul_def]

@[simp] theorem algebraMapProd_basis
    (i : Fin 2) :
    algebraMapProd (O := O) (K := K)
        (Basis.finTwoProd O i) =
      Basis.finTwoProd K i := by
  fin_cases i <;> simp [
    algebraMapProd,
    Basis.finTwoProd_zero,
    Basis.finTwoProd_one
  ]

/-- Coercion of lattice coordinates into the ambient K^2 module. -/
def carrierSubtype :
    L.carrier →ₗ[O] (K × K) :=
  L.carrier.subtype

/-- Fundamental frame compatibility on all integral coordinates.

The ambient K-linear change of basis restricted to O^2 agrees exactly with
first expressing the vector in the lattice frame and then coercing the lattice
vector into K^2. -/
theorem ambient_integral_compat
    (F : Frame L) :
    ((F.ambientEquiv.toLinearMap.restrictScalars O).comp
        (algebraMapProd (O := O) (K := K))) =
      (carrierSubtype (L := L)).comp
        F.latticeEquiv.toLinearMap := by
  apply Basis.ext (Basis.finTwoProd O)
  intro i
  simp [
    LinearMap.comp_apply,
    ambientEquiv_basis,
    latticeEquiv_basis,
    F.compatible i
  ]

/-- Pointwise form of the integral compatibility theorem. -/
theorem ambientEquiv_algebraMapProd
    (F : Frame L)
    (x : O × O) :
    F.ambientEquiv
        (algebraMapProd (O := O) (K := K) x) =
      (F.latticeEquiv x : K × K) := by
  have h :=
    LinearMap.congr_fun
      (F.ambient_integral_compat)
      x
  exact h

/-- Every rank-two lattice has a compatible standard frame. -/
theorem nonempty_frame
    (L : RankTwoLattice O K) :
    Nonempty (Frame L) :=
  ⟨Frame.canonical L⟩

end Frame
end PID
end RankTwoLattice
end CausalGeometry
