import CausalGeometry.Number.LocalizedValuation
import CausalGeometry.Process.EndComposition
import CausalGeometry.Realization.ECIATamagawaContract

namespace CausalGeometry

universe u v w x y

/-- A commutative arithmetic shadow of a weak causal end-diary composition
system.

The source end-diaries themselves are not made into a strict monoid.  Instead,
a chosen arithmetic realization lands in a commutative monoid and must prove
that source equivalence, the weak unit and every chosen composition are
respected.

This is the generic version of `EndDiaryNatShadow`; it is deliberately
target-neutral and does not mention elliptic curves, local fields or Neron
models. -/
structure EndDiaryCommutativeShadow
    {A : Type u}
    (C : EndDiaryCompositionSystem.{u, w} A)
    (α : Type v)
    [CommMonoid α] where
  toArithmetic :
    EndDiary.{u, w} A → α
  equivalent_invariant :
    ∀ {X Y},
      C.equivalent X Y →
        toArithmetic X = toArithmetic Y
  unit :
    toArithmetic C.unit = 1
  compose :
    ∀ X Y,
      toArithmetic (C.compose X Y) =
        toArithmetic X * toArithmetic Y

namespace EndDiaryCommutativeShadow

variable
    {A : Type u}
    {α : Type v}
    [CommMonoid α]
    {C : EndDiaryCompositionSystem.{u, w} A}

instance :
    CoeFun
      (EndDiaryCommutativeShadow C α)
      (fun _ => EndDiary.{u, w} A → α) :=
  ⟨EndDiaryCommutativeShadow.toArithmetic⟩

@[simp]
theorem unit_apply
    (S : EndDiaryCommutativeShadow C α) :
    S C.unit = 1 :=
  S.unit

@[simp]
theorem compose_apply
    (S : EndDiaryCommutativeShadow C α)
    (X Y : EndDiary.{u, w} A) :
    S (C.compose X Y) =
      S X * S Y :=
  S.compose X Y

theorem equivalent_apply
    (S : EndDiaryCommutativeShadow C α)
    {X Y : EndDiary.{u, w} A}
    (h : C.equivalent X Y) :
    S X = S Y :=
  S.equivalent_invariant h

end EndDiaryCommutativeShadow

/-- Source-local arithmetic extracted from one weak causal composition system.

The arithmetic carrier has a canonical atomic factorization profile.  Hence a
source end-diary determines a finite set of active primary places and an
intrinsic nonnegative depth at every arithmetic atom.

No target meaning is attached to those places here.  In particular an active
source place is not called a bad-reduction prime until a downstream
realization proves that comparison. -/
structure AtomicLocalSource
    {A : Type u}
    (C : EndDiaryCompositionSystem.{u, w} A)
    (α : Type v)
    [CancelCommMonoid α]
    [DecidableEq α] where
  arithmeticShadow :
    EndDiaryCommutativeShadow C α
  atomicDomain :
    CausalFactorization.CanonicalAtomicDomain
      (α := α)

namespace AtomicLocalSource

variable
    {A : Type u}
    {α : Type v}
    [CancelCommMonoid α]
    [DecidableEq α]
    {C : EndDiaryCompositionSystem.{u, w} A}
    (S : AtomicLocalSource C α)

/-- Intrinsic primary depth of one arithmetic atom at one causal source
object. -/
def depth
    (place : α)
    (X : EndDiary.{u, w} A) : ℕ :=
  S.atomicDomain.valuation
    place
    (S.arithmeticShadow X)

/-- Finite source-derived set of arithmetic places active in one causal
object. -/
def primarySupport
    (X : EndDiary.{u, w} A) :
    Finset α :=
  (S.atomicDomain.canonicalProfile
    (S.arithmeticShadow X)).support

/-- Primary support is exactly positive intrinsic depth. -/
theorem mem_primarySupport_iff_depth_pos
    (place : α)
    (X : EndDiary.{u, w} A) :
    place ∈ S.primarySupport X ↔
      0 < S.depth place X := by
  exact
    (S.atomicDomain
      .valuation_pos_iff_mem_support).symm

/-- Outside the finite source support the intrinsic primary depth vanishes. -/
theorem depth_eq_zero_of_not_mem_primarySupport
    (place : α)
    (X : EndDiary.{u, w} A)
    (hplace :
      place ∉ S.primarySupport X) :
    S.depth place X = 0 := by
  exact
    S.atomicDomain
      .valuation_eq_zero_of_not_mem_support
        hplace

/-- Source equivalence preserves every primary depth. -/
theorem depth_eq_of_equivalent
    {X Y : EndDiary.{u, w} A}
    (hXY : C.equivalent X Y)
    (place : α) :
    S.depth place X =
      S.depth place Y := by
  unfold depth
  rw [
    S.arithmeticShadow
      .equivalent_apply hXY
  ]

/-- Therefore source equivalence preserves the complete finite place support. -/
theorem primarySupport_eq_of_equivalent
    {X Y : EndDiary.{u, w} A}
    (hXY : C.equivalent X Y) :
    S.primarySupport X =
      S.primarySupport Y := by
  unfold primarySupport
  rw [
    S.arithmeticShadow
      .equivalent_apply hXY
  ]

/-- Primary depth is additive under the selected weak causal composition. -/
theorem depth_compose
    (place : α)
    (X Y : EndDiary.{u, w} A) :
    S.depth place (C.compose X Y) =
      S.depth place X +
        S.depth place Y := by
  unfold depth
  rw [
    S.arithmeticShadow.compose_apply,
    S.atomicDomain.valuation_mul
  ]

/-- The weak source unit has zero depth at every arithmetic place. -/
theorem depth_unit
    (place : α) :
    S.depth place C.unit = 0 := by
  unfold depth
  rw [S.arithmeticShadow.unit_apply]
  exact
    S.atomicDomain.valuation_one place

/-- Consequently the weak source unit has empty primary support. -/
theorem primarySupport_unit :
    S.primarySupport C.unit = ∅ := by
  ext place
  simp only [Finset.mem_empty, iff_false]
  intro hplace
  have hpos :=
    (S.mem_primarySupport_iff_depth_pos
      place C.unit).1 hplace
  rw [S.depth_unit place] at hpos
  omega

/-- Composition activates exactly the union of the two finite primary
supports.

This is a source theorem: it uses only multiplicative compatibility of the
arithmetic shadow and uniqueness of the atomic profile. -/
theorem primarySupport_compose
    (X Y : EndDiary.{u, w} A) :
    S.primarySupport (C.compose X Y) =
      S.primarySupport X ∪
        S.primarySupport Y := by
  ext place
  rw [
    Finset.mem_union,
    S.mem_primarySupport_iff_depth_pos,
    S.mem_primarySupport_iff_depth_pos,
    S.mem_primarySupport_iff_depth_pos,
    S.depth_compose
  ]
  omega

/-- A primary place cannot disappear when another causal object is composed
on the right. -/
theorem primarySupport_mono_left
    (X Y : EndDiary.{u, w} A) :
    S.primarySupport X ⊆
      S.primarySupport (C.compose X Y) := by
  rw [S.primarySupport_compose]
  exact Finset.subset_union_left

/-- Symmetric monotonicity for the right factor. -/
theorem primarySupport_mono_right
    (X Y : EndDiary.{u, w} A) :
    S.primarySupport Y ⊆
      S.primarySupport (C.compose X Y) := by
  rw [S.primarySupport_compose]
  exact Finset.subset_union_right

end AtomicLocalSource

namespace Tamagawa

/-- Exact support comparison between a source-derived atomic local arithmetic
profile and a structural Tamagawa realization.

This is a theorem lock, not a source definition.  It is appropriate only when
the downstream geometry proves that the finite Tamagawa support is exactly the
chosen causal primary support.  A weaker subset comparison should be used in
domains where some active causal arithmetic places remain geometrically good. -/
structure ExactAtomicSupportCompatibility
    {A : Type u}
    {α : Type v}
    [CancelCommMonoid α]
    [DecidableEq α]
    {C : EndDiaryCompositionSystem.{u, w} A}
    (S : AtomicLocalSource C α)
    (F :
      EndDiary.{u, w} A →
        Tamagawa.Family.{v, x, y} α) : Prop where
  support_eq :
    ∀ X,
      (F X).support =
        S.primarySupport X

namespace ExactAtomicSupportCompatibility

variable
    {A : Type u}
    {α : Type v}
    [CancelCommMonoid α]
    [DecidableEq α]
    {C : EndDiaryCompositionSystem.{u, w} A}
    {S : AtomicLocalSource C α}
    {F :
      EndDiary.{u, w} A →
        Tamagawa.Family.{v, x, y} α}
    (h :
      ExactAtomicSupportCompatibility
        S F)

/-- Outside the causal primary support the compared Tamagawa factor is
necessarily neutral. -/
theorem tamagawaIndex_eq_one_of_not_mem_primarySupport
    (X : EndDiary.{u, w} A)
    (place : α)
    (hplace :
      place ∉ S.primarySupport X) :
    ((F X).local place).tamagawaIndex = 1 := by
  apply (F X).unit_outside_support
  rw [h.support_eq X]
  exact hplace

/-- Equivalent causal sources have equal compared Tamagawa support. -/
theorem target_support_eq_of_equivalent
    {X Y : EndDiary.{u, w} A}
    (hXY : C.equivalent X Y) :
    (F X).support =
      (F Y).support := by
  rw [
    h.support_eq X,
    h.support_eq Y,
    S.primarySupport_eq_of_equivalent hXY
  ]

/-- Under exact support compatibility, source composition transports to union
of finite Tamagawa supports.  No claim about multiplication of local Tamagawa
indices is made. -/
theorem target_support_compose
    (X Y : EndDiary.{u, w} A) :
    (F (C.compose X Y)).support =
      (F X).support ∪
        (F Y).support := by
  rw [
    h.support_eq (C.compose X Y),
    h.support_eq X,
    h.support_eq Y,
    S.primarySupport_compose
  ]

end ExactAtomicSupportCompatibility

/-- Weaker comparison for targets whose nontrivial Tamagawa places form only a
subset of the causal arithmetic support. -/
structure AtomicSupportUpperBound
    {A : Type u}
    {α : Type v}
    [CancelCommMonoid α]
    [DecidableEq α]
    {C : EndDiaryCompositionSystem.{u, w} A}
    (S : AtomicLocalSource C α)
    (F :
      EndDiary.{u, w} A →
        Tamagawa.Family.{v, x, y} α) : Prop where
  support_subset :
    ∀ X,
      (F X).support ⊆
        S.primarySupport X

namespace AtomicSupportUpperBound

variable
    {A : Type u}
    {α : Type v}
    [CancelCommMonoid α]
    [DecidableEq α]
    {C : EndDiaryCompositionSystem.{u, w} A}
    {S : AtomicLocalSource C α}
    {F :
      EndDiary.{u, w} A →
        Tamagawa.Family.{v, x, y} α}
    (h :
      AtomicSupportUpperBound
        S F)

/-- A place outside the causal arithmetic support cannot carry a nontrivial
Tamagawa factor in a bounded target family. -/
theorem tamagawaIndex_eq_one_of_not_mem_primarySupport
    (X : EndDiary.{u, w} A)
    (place : α)
    (hplace :
      place ∉ S.primarySupport X) :
    ((F X).local place).tamagawaIndex = 1 := by
  apply (F X).unit_outside_support
  intro htarget
  exact hplace
    (h.support_subset X htarget)

end AtomicSupportUpperBound

end Tamagawa
end CausalGeometry
