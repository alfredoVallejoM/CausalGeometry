import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Finiteness.Basic

namespace CausalGeometry

universe u v

/-- A rank-two O-lattice inside K^2.

The carrier is an O-submodule, finitely generated over O, whose K-linear span
is the whole ambient plane. No valuation, DVR or local-field hypothesis is
built into this carrier. -/
structure RankTwoLattice
    (O : Type u) (K : Type v)
    [CommRing O] [Field K] [Algebra O K] where
  carrier : Submodule O (K × K)
  fg : carrier.FG
  spans :
    Submodule.span K (carrier : Set (K × K)) =
      ⊤

namespace RankTwoLattice

variable
    {O : Type u} {K : Type v}
    [CommRing O] [Field K] [Algebra O K]

@[ext] theorem ext
    {L M : RankTwoLattice O K}
    (h : L.carrier = M.carrier) :
    L = M := by
  cases L
  cases M
  simp_all

/-- Scalar homothety by a nonzero field element, as a K-linear equivalence. -/
def scaleEquivK
    (u : Kˣ) :
    (K × K) ≃ₗ[K] (K × K) :=
  LinearEquiv.smulOfUnit u

/-- The same homothety regarded only as O-linear. -/
def scaleEquivO
    (u : Kˣ) :
    (K × K) ≃ₗ[O] (K × K) :=
  (scaleEquivK (O := O) u).restrictScalars O

@[simp] theorem scaleEquivK_apply
    (u : Kˣ) (x : K × K) :
    scaleEquivK (O := O) u x =
      (u : K) • x := by
  rfl

@[simp] theorem scaleEquivO_apply
    (u : Kˣ) (x : K × K) :
    scaleEquivO (O := O) u x =
      (u : K) • x := by
  rfl

/-- Homothetic image of a lattice. -/
def scale
    (u : Kˣ)
    (L : RankTwoLattice O K) :
    RankTwoLattice O K where
  carrier :=
    L.carrier.map
      (scaleEquivO (O := O) u).toLinearMap
  fg :=
    L.fg.map
      (scaleEquivO (O := O) u).toLinearMap
  spans := by
    have hmap :=
      congrArg
        (Submodule.map
          (scaleEquivK (O := O) u).toLinearMap)
        L.spans
    have hcarrier :
        ((L.carrier.map
          (scaleEquivO (O := O) u).toLinearMap :
            Submodule O (K × K)) : Set (K × K)) =
          (scaleEquivK (O := O) u) ''
            (L.carrier : Set (K × K)) := by
      ext x
      simp [scaleEquivO, scaleEquivK]
    rw [hcarrier]
    rw [← Submodule.map_span]
    rw [L.spans]
    simp

@[simp] theorem scale_carrier
    (u : Kˣ)
    (L : RankTwoLattice O K) :
    (L.scale u).carrier =
      L.carrier.map
        (scaleEquivO (O := O) u).toLinearMap :=
  rfl

@[simp] theorem scale_one
    (L : RankTwoLattice O K) :
    L.scale 1 = L := by
  apply RankTwoLattice.ext
  ext x
  simp [scale, scaleEquivO, scaleEquivK]

theorem scale_mul
    (u v : Kˣ)
    (L : RankTwoLattice O K) :
    (L.scale v).scale u =
      L.scale (u * v) := by
  apply RankTwoLattice.ext
  ext x
  simp [scale, scaleEquivO, scaleEquivK,
    Submodule.mem_map]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨z, hz, ?_⟩
    simp [mul_smul]
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(v : K) • z, ?_, ?_⟩
    · exact ⟨z, hz, rfl⟩
    · simp [mul_smul]

@[simp] theorem scale_inv_scale
    (u : Kˣ)
    (L : RankTwoLattice O K) :
    (L.scale u).scale u⁻¹ = L := by
  rw [scale_mul]
  simp

/-- Homothety relation between rank-two lattices. -/
def Homothetic
    (L M : RankTwoLattice O K) : Prop :=
  ∃ u : Kˣ, M = L.scale u

theorem homothetic_refl
    (L : RankTwoLattice O K) :
    Homothetic L L :=
  ⟨1, by simp⟩

theorem homothetic_symm
    {L M : RankTwoLattice O K}
    (h : Homothetic L M) :
    Homothetic M L := by
  rcases h with ⟨u, rfl⟩
  refine ⟨u⁻¹, ?_⟩
  simp

theorem homothetic_trans
    {L M N : RankTwoLattice O K}
    (hLM : Homothetic L M)
    (hMN : Homothetic M N) :
    Homothetic L N := by
  rcases hLM with ⟨u, rfl⟩
  rcases hMN with ⟨v, rfl⟩
  refine ⟨v * u, ?_⟩
  rw [scale_mul]
  rfl

def homothetySetoid :
    Setoid (RankTwoLattice O K) where
  r := Homothetic
  iseqv := ⟨
    homothetic_refl,
    homothetic_symm,
    homothetic_trans
  ⟩

/-- Homothety classes are the vertex carrier used by lattice realizations of
Bruhat--Tits geometry. -/
abbrev HomothetyClass :=
  Quotient (homothetySetoid (O := O) (K := K))

def classOf
    (L : RankTwoLattice O K) :
    HomothetyClass (O := O) (K := K) :=
  Quotient.mk _ L

@[simp] theorem classOf_scale
    (u : Kˣ)
    (L : RankTwoLattice O K) :
    classOf (L.scale u) =
      classOf L := by
  apply Quotient.sound
  exact ⟨u, rfl⟩

/-- A property of lattices descends to homothety classes precisely when it is
invariant under all scalar homotheties. -/
def HomothetyInvariant
    (P : RankTwoLattice O K → Prop) : Prop :=
  ∀ L u, P L ↔ P (L.scale u)

end RankTwoLattice
end CausalGeometry
