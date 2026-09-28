import CausalGeometry.Realization.LocalArithmeticSource
import CausalGeometry.Models.CausalLengthAtomic
import Mathlib.Tactic

namespace CausalGeometry
namespace Models
namespace LocalArithmeticSourceControls

universe u w

open CausalLengthAtomic

/-- A genuine source observable measuring causal composition length.

The laws are stated on the weak end-diary composition system itself.  They do
not impose strict composition on end-diaries. -/
structure LengthObservable
    {A : Type u}
    (C : EndDiaryCompositionSystem.{u, w} A) where
  length :
    EndDiary.{u, w} A → ℕ
  equivalent_invariant :
    ∀ {X Y},
      C.equivalent X Y →
        length X = length Y
  unit_zero :
    length C.unit = 0
  compose_add :
    ∀ X Y,
      length (C.compose X Y) =
        length X + length Y

namespace LengthObservable

variable
    {A : Type u}
    {C : EndDiaryCompositionSystem.{u, w} A}
    (L : LengthObservable C)

/-- Interpret causal length in the already certified one-generator
commutative causal-length monoid. -/
def arithmeticShadow :
    EndDiaryCommutativeShadow
      C CausalLength where
  toArithmetic :=
    fun X =>
      Multiplicative.ofAdd (L.length X)
  equivalent_invariant := by
    intro X Y hXY
    rw [Multiplicative.ext_iff]
    exact L.equivalent_invariant hXY
  unit := by
    rw [Multiplicative.ext_iff]
    simpa using L.unit_zero
  compose := by
    intro X Y
    rw [Multiplicative.ext_iff]
    simpa [
      Multiplicative.toAdd_mul
    ] using L.compose_add X Y

/-- The length observable therefore produces an actual atomic local source,
not merely an arbitrary finite set of places. -/
def atomicSource :
    AtomicLocalSource
      C CausalLength where
  arithmeticShadow :=
    L.arithmeticShadow
  atomicDomain :=
    CausalLengthAtomic.domain

/-- Complete intrinsic depth formula for the length-derived local source. -/
theorem depth_eq
    (place : CausalLength)
    (X : EndDiary.{u, w} A) :
    L.atomicSource.depth place X =
      if place = atom
      then L.length X
      else 0 := by
  unfold AtomicLocalSource.depth
  change
    domain.valuation place
        (Multiplicative.ofAdd
          (L.length X)) =
      _
  rw [domain_valuation]
  simp

/-- The unique causal atom has local depth exactly equal to causal length. -/
@[simp]
theorem atom_depth
    (X : EndDiary.{u, w} A) :
    L.atomicSource.depth atom X =
      L.length X := by
  rw [L.depth_eq]
  simp

/-- The primary support is derived, not supplied: it is empty at zero causal
length and is exactly the singleton causal atom otherwise. -/
theorem primarySupport_eq
    (X : EndDiary.{u, w} A) :
    L.atomicSource.primarySupport X =
      if L.length X = 0
      then ∅
      else {atom} := by
  ext place
  rw [
    L.atomicSource
      .mem_primarySupport_iff_depth_pos,
    L.depth_eq
  ]
  by_cases hlen :
      L.length X = 0 <;>
    by_cases hplace :
      place = atom <;>
    simp [hlen, hplace]

/-- Nonzero causal length is equivalent to activation of the unique local
primary place. -/
theorem atom_mem_primarySupport_iff
    (X : EndDiary.{u, w} A) :
    atom ∈
        L.atomicSource.primarySupport X ↔
      0 < L.length X := by
  rw [
    L.atomicSource
      .mem_primarySupport_iff_depth_pos,
    L.atom_depth
  ]

/-- This concrete source construction inherits exact union of active places
under weak causal composition. -/
theorem primarySupport_compose
    (X Y : EndDiary.{u, w} A) :
    L.atomicSource.primarySupport
        (C.compose X Y) =
      L.atomicSource.primarySupport X ∪
        L.atomicSource.primarySupport Y :=
  L.atomicSource.primarySupport_compose X Y

/-- Mutation discriminator: if two equivalent source diaries were assigned
different lengths, they could not define a valid causal length observable. -/
theorem equivalent_length_rigid
    {X Y : EndDiary.{u, w} A}
    (hXY : C.equivalent X Y) :
    L.length X = L.length Y :=
  L.equivalent_invariant hXY

end LengthObservable

end LocalArithmeticSourceControls
end Models
end CausalGeometry
