import CausalGeometry.Realization.ECIATamagawaContract
import CausalGeometry.Realization.TamagawaIndexedFamily
import CausalGeometry.Realization.LocalArithmeticSource
import CausalGeometry.Models.TamagawaControls
import CausalGeometry.Models.IndexedFamilyControls
import CausalGeometry.Models.CommonSourceControls
import CausalGeometry.Models.LocalArithmeticSourceControls

/-! Directed kernel audit for the CA-24 Tamagawa source tranche. -/

namespace CausalGeometry.Verification.Tamagawa

open scoped BigOperators
open Tamagawa
open Models.TamagawaControls
open Models.IndexedFamilyControls
open Models.CommonSourceControls
open Models.LocalArithmeticSourceControls

/-! Local structural quotient laws. -/

example : 0 < collapsedBool.tamagawaIndex :=
  collapsedBool.tamagawaIndex_pos

example : separatedBool.tamagawaIndex ≠ 0 :=
  separatedBool.tamagawaIndex_ne_zero

example :
    collapsedBool.tamagawaIndex ≠
      separatedBool.tamagawaIndex :=
  same_local_points_different_tamagawa

example :
    firstCoordinateQuotient.tamagawaIndex =
      secondCoordinateQuotient.tamagawaIndex :=
  coordinateQuotients_same_tamagawa

example :
    ¬ ∃ e :
        firstCoordinateQuotient.Component ≃
          secondCoordinateQuotient.Component,
      ∀ p : Bool × Bool,
        e (firstCoordinateQuotient.componentOf p) =
          secondCoordinateQuotient.componentOf p :=
  coordinateQuotients_no_commuting_equiv_over_id

/-! Global product and support-certificate laws. -/

example : 0 < mixedFamily.globalTamagawaIndex :=
  mixedFamily.globalTamagawaIndex_pos

example : mixedFamily.globalTamagawaIndex ≠ 0 :=
  mixedFamily.globalTamagawaIndex_ne_zero

example :
    mixedFamily.globalTamagawaIndex = 2 :=
  mixedFamily_globalTamagawaIndex

example :
    mixedFamily.globalTamagawaIndex =
      ∏ place in ({false, true} : Finset Bool),
        (mixedFamily.local place).tamagawaIndex :=
  mixedFamily_extendedSupport_same

example :
    mixedFamily.globalTamagawaIndex ≠
      ∏ place in ({true} : Finset Bool),
        (mixedFamily.local place).tamagawaIndex :=
  mixedFamily_omitting_bad_place_rejected

/-! Indexed-family provenance / loss controls. -/

example :
    coordinateFamily.JointlyConservative :=
  coordinateFamily_jointlyConservative

example :
    ¬ firstOnlyFamily.JointlyConservative :=
  firstOnlyFamily_not_jointlyConservative

example :
    emptyCausalNumber ≠ singletonCausalNumber :=
  empty_ne_singleton

universe u w

variable
    {A : Type u}
    {C : EndDiaryCompositionSystem.{u, w} A}

example
    (L : LengthObservable C)
    (X : EndDiary.{u, w} A) :
    L.atomicSource.depth
        Models.CausalLengthAtomic.atom X =
      L.length X :=
  L.atom_depth X

example
    (L : LengthObservable C)
    (X : EndDiary.{u, w} A) :
    L.atomicSource.primarySupport X =
      if L.length X = 0
      then ∅
      else {Models.CausalLengthAtomic.atom} :=
  L.primarySupport_eq X

#print axioms CausalGeometry.Tamagawa.LocalComponentQuotient.tamagawaIndex_pos
#print axioms CausalGeometry.Tamagawa.Family.globalTamagawaIndex_pos
#print axioms CausalGeometry.Tamagawa.Family.globalTamagawaIndex_ne_zero
#print axioms CausalGeometry.Tamagawa.Family.globalTamagawaIndex_eq_prod_of_unit_outside
#print axioms CausalGeometry.Tamagawa.Family.globalTamagawaIndex_insert_neutral
#print axioms CausalGeometry.Models.TamagawaControls.mixedFamily_extendedSupport_same
#print axioms CausalGeometry.Models.TamagawaControls.mixedFamily_omitting_bad_place_rejected
#print axioms CausalGeometry.IndexedRealizationFamily.collapseEverywhere_of_comparison
#print axioms CausalGeometry.Models.IndexedFamilyControls.coordinateFamily_jointlyConservative
#print axioms CausalGeometry.Models.CommonSourceControls.empty_ne_singleton
#print axioms CausalGeometry.EndDiaryCommutativeShadow.compose_apply
#print axioms CausalGeometry.AtomicLocalSource.depth_compose
#print axioms CausalGeometry.AtomicLocalSource.primarySupport_compose
#print axioms CausalGeometry.Tamagawa.ExactAtomicSupportCompatibility.target_support_compose
#print axioms CausalGeometry.Tamagawa.AtomicSupportUpperBound.tamagawaIndex_eq_one_of_not_mem_primarySupport
#print axioms CausalGeometry.Models.CausalLengthAtomic.domain_valuation
#print axioms CausalGeometry.Models.LocalArithmeticSourceControls.LengthObservable.primarySupport_eq

end CausalGeometry.Verification.Tamagawa
