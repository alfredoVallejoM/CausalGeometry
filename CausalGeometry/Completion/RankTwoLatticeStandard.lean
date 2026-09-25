import CausalGeometry.Completion.RankTwoLattice
import Mathlib.Algebra.Module.Lattice
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace CausalGeometry

universe u v

namespace RankTwoLattice

variable
    {O : Type u} {K : Type v}
    [CommRing O] [Field K] [Algebra O K]

/-- Our rank-two lattice carrier is exactly a mathlib Submodule.IsLattice. -/
def isLattice
    (L : RankTwoLattice O K) :
    Submodule.IsLattice K L.carrier where
  fg := L.fg
  span_eq_top := L.spans

/-- Build our explicit structure from any standard mathlib lattice in K^2. -/
def ofIsLattice
    (M : Submodule O (K × K))
    (hM : Submodule.IsLattice K M) :
    RankTwoLattice O K where
  carrier := M
  fg := hM.fg
  spans := hM.span_eq_top

@[simp] theorem ofIsLattice_carrier
    (M : Submodule O (K × K))
    (hM : Submodule.IsLattice K M) :
    (ofIsLattice M hM).carrier = M :=
  rfl

/-- The two presentations are mutually inverse up to proof irrelevance. -/
@[simp] theorem ofIsLattice_isLattice
    (L : RankTwoLattice O K) :
    ofIsLattice L.carrier L.isLattice = L := by
  apply RankTwoLattice.ext
  rfl

/-- Standard-lattice presentation as a subtype. -/
abbrev StandardPresentation :=
  {M : Submodule O (K × K) //
    Submodule.IsLattice K M}

/-- Equivalence between the project-specific carrier and mathlib's standard
lattice predicate. -/
def standardPresentationEquiv :
    RankTwoLattice O K ≃
      StandardPresentation (O := O) (K := K) where
  toFun := fun L =>
    ⟨L.carrier, L.isLattice⟩
  invFun := fun M =>
    ofIsLattice M.1 M.2
  left_inv := by
    intro L
    exact ofIsLattice_isLattice L
  right_inv := by
    intro M
    apply Subtype.ext
    rfl

section PID

variable
    [IsDomain O]
    [IsPrincipalIdealRing O]
    [IsFractionRing O K]
    [Module.IsTorsionFree O K]

/-- Every rank-two lattice is a free O-module. -/
noncomputable instance free
    (L : RankTwoLattice O K) :
    Module.Free O L.carrier := by
  letI :
      Submodule.IsLattice K L.carrier :=
    L.isLattice
  infer_instance

/-- Every rank-two lattice has the same O-rank as K^2 over K. -/
theorem rank_eq_ambient
    (L : RankTwoLattice O K) :
    Module.rank O L.carrier =
      Module.rank K (K × K) := by
  letI :
      Submodule.IsLattice K L.carrier :=
    L.isLattice
  exact
    Submodule.IsLattice.rank'
      K L.carrier

/-- In particular, the finite rank is exactly two. -/
theorem finrank_eq_two
    (L : RankTwoLattice O K) :
    Module.finrank O L.carrier = 2 := by
  have hrank :=
    L.rank_eq_ambient
  rw [show
    Module.rank K (K × K) = 2 by
      simp] at hrank
  exact
    Module.finrank_eq_of_rank_eq
      hrank

/-- Canonical chosen O-basis supplied by freeness. -/
noncomputable def basis
    (L : RankTwoLattice O K) :
    Basis
      (Module.Free.ChooseBasisIndex O L.carrier)
      O L.carrier :=
  Module.Free.chooseBasis O L.carrier

/-- Every chosen lattice basis extends canonically to a K-basis of K^2. -/
noncomputable def ambientBasis
    (L : RankTwoLattice O K) :
    Basis
      (Module.Free.ChooseBasisIndex O L.carrier)
      K (K × K) := by
  letI :
      Submodule.IsLattice K L.carrier :=
    L.isLattice
  exact
    (L.basis).extendOfIsLattice K

@[simp] theorem ambientBasis_apply
    (L : RankTwoLattice O K)
    (i :
      Module.Free.ChooseBasisIndex
        O L.carrier) :
    L.ambientBasis i =
      (L.basis i).1 := by
  letI :
      Submodule.IsLattice K L.carrier :=
    L.isLattice
  exact
    Module.Basis.extendOfIsLattice_apply
      K (L.basis) i

/-- The chosen lattice basis has exactly two indices. -/
theorem basisIndex_card
    (L : RankTwoLattice O K) :
    Cardinal.mk
        (Module.Free.ChooseBasisIndex
          O L.carrier) =
      2 := by
  rw [← Module.rank_eq_card_basis (L.basis)]
  rw [L.rank_eq_ambient]
  simp

end PID
end RankTwoLattice
end CausalGeometry
