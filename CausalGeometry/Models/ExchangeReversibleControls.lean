import CausalGeometry.Exchange.Defect
import CausalGeometry.Exchange.EquationFamily
import CausalGeometry.Models.ExchangeCoherenceControls
import Mathlib.CategoryTheory.Core

/-!
# CX-I3: inversion is not Yang–Baxter and not reversal of causal time

All objects remain the actual three-event histories of CX-I1. The native
free groupoid adds inverses to their exchange quiver. We construct invertible
observers, prove the ternary pair remains distinct, and separate the optional
identification of an opposite generator from the optional ternary equation.
-/
namespace CausalGeometry.Models.ExchangeReversibleControls

open CategoryTheory CausalGeometry.Exchange
open CausalGeometry.Models.ExchangeThreeEvents

noncomputable section

abbrev ModFiber : Core (Type) := ⟨ZMod 5⟩
abbrev IntFiber : Core (Type) := ⟨Int⟩
abbrev Hist := CausalPath system initial terminal
abbrev FG := Quiver.FreeGroupoid Hist
abbrev includeRoutes : HistoryCategory initial terminal ⥤ FG := Reversible.positive

def routeP : includeRoutes.obj h012 ⟶ includeRoutes.obj h210 := includeRoutes.map route121

def routeQ : includeRoutes.obj h012 ⟶ includeRoutes.obj h210 := includeRoutes.map route212

/-- A genuine groupoid-valued interpretation: every arrow carries its proved inverse. -/
def memoryCore (t : ZMod 5) : Hist ⥤q Core (Type) where
  obj _ := ⟨ZMod 5⟩
  map s := ⟨{
    hom := (memoryPrefunctor t).map s
    inv := (memoryPrefunctor t).map s
    hom_inv_id := by
      apply TypeCat.homEquiv.injective
      funext m
      exact elementary_involutive t s m
    inv_hom_id := by
      apply TypeCat.homEquiv.injective
      funext m
      exact elementary_involutive t s m
  }⟩

abbrev groupMemory (t : ZMod 5) : FG ⥤ Core (Type) := Reversible.extend (memoryCore t)

/-- The extended observer agrees with the old observer on every positive route. -/
theorem positive_memory (t : ZMod 5) {p q : Hist} (r : Exchange.Route p q) (m : ZMod 5) :
    ((groupMemory t).map (includeRoutes.map r)).iso.hom m = observed t r m := by
  induction r with
  | nil =>
      rw [Reversible.positive_nil, Functor.map_id]
      rfl
  | cons r s ih =>
      rw [Reversible.positive_cons, Functor.map_comp, Reversible.extend_generator]
      change (memoryPrefunctor t).map s
        (((groupMemory t).map (includeRoutes.map r)).iso.hom m) =
          observed t (r.cons s) m
      rw [ih]
      rfl

theorem image_routes_separated : (groupMemory 2).map routeP ≠ (groupMemory 2).map routeQ := by
  intro h
  have hv := congrArg (fun f : ModFiber ⟶ ModFiber => f.iso.hom (0 : ZMod 5)) h
  change ((groupMemory 2).map (includeRoutes.map route121)).iso.hom 0 =
    ((groupMemory 2).map (includeRoutes.map route212)).iso.hom 0 at hv
  rw [positive_memory, positive_memory, observed_route121, observed_route212] at hv
  norm_num at hv

/-- Adding formal inverses does not force the ternary equation. -/
theorem reversible_routes_distinct : routeP ≠ routeQ := by
  intro h
  exact image_routes_separated (congrArg (fun f => (groupMemory 2).map f) h)

theorem defect_nontrivial : Reversible.defect routeP routeQ ≠ 𝟙 (includeRoutes.obj h012) :=
  Reversible.defect_ne_id_of_separated (groupMemory 2) routeP routeQ image_routes_separated

/-- One additional law on this actual pair, not a universal braid presentation. -/
def ternaryFamily (_ : Unit) : Coherence.ParallelEquation FG :=
  ⟨includeRoutes.obj h012, includeRoutes.obj h210, routeP, routeQ⟩

abbrev TernaryRel := Coherence.FamilyRelation ternaryFamily
abbrev TernaryGroupoid := Coherence.FamilyQuotient ternaryFamily
abbrev ternaryProjection : FG ⥤ TernaryGroupoid := CategoryTheory.Quotient.functor TernaryRel

theorem groupoid_respects_iff_zero (t : ZMod 5) :
    Coherence.Respects TernaryRel (groupMemory t) ↔ t = 0 := by
  rw [Coherence.family_respects_iff]
  constructor
  · intro h
    have hv := congrArg (fun f : ModFiber ⟶ ModFiber => f.iso.hom (0 : ZMod 5)) (h ())
    change ((groupMemory t).map (includeRoutes.map route121)).iso.hom 0 =
      ((groupMemory t).map (includeRoutes.map route212)).iso.hom 0 at hv
    rw [positive_memory, positive_memory, observed_route121, observed_route212] at hv
    simp only [sub_zero] at hv
    have hz : (3 : ZMod 5) * t = 0 := by
      calc
        3 * t = (t + t) - (-t) := by ring
        _ = 0 := sub_eq_zero.mpr hv.symm
    exact (mul_eq_zero.mp hz).resolve_left (by decide)
  · intro ht
    subst t
    intro i
    apply Core.hom_ext
    apply TypeCat.homEquiv.injective
    funext m
    change ((groupMemory 0).map (includeRoutes.map route121)).iso.hom m =
      ((groupMemory 0).map (includeRoutes.map route212)).iso.hom m
    rw [positive_memory, positive_memory]
    exact zero_offset_forgets m

/-- The quotient of this groupoid still has actual inverses. -/
theorem ternary_quotient_inverse {X Y : TernaryGroupoid} (f : X ⟶ Y) :
    f ≫ Groupoid.inv f = 𝟙 X := Groupoid.comp_inv f

theorem defect_killed_by_ternary :
    ternaryProjection.map (Reversible.defect routeP routeQ) =
      𝟙 (ternaryProjection.obj (includeRoutes.obj h012)) := by
  rw [Reversible.map_defect]
  apply (Reversible.defect_eq_id_iff _ _).mpr
  exact CategoryTheory.Quotient.sound TernaryRel (Coherence.FamilyRelation.equation ())

def zeroOnTernary : TernaryGroupoid ⥤ Core (Type) :=
  Coherence.descend TernaryRel (groupMemory 0) ((groupoid_respects_iff_zero 0).mpr rfl)

theorem groupoid_factorsUpToIso_iff_zero (t : ZMod 5) :
    (∃ F : TernaryGroupoid ⥤ Core (Type), Nonempty (ternaryProjection ⋙ F ≅ groupMemory t))
      ↔ t = 0 := by
  rw [← Coherence.respects_iff_factorsUpToIso]
  exact groupoid_respects_iff_zero t

/-- A chronological reverse generator is a different piece of quiver data. -/
def firstForward : includeRoutes.obj h012 ⟶ includeRoutes.obj h102 :=
  (Quiver.FreeGroupoid.of Hist).map (swapFirst 0 1 2 (by decide) (by decide) (by decide))

def firstBackward : includeRoutes.obj h102 ⟶ includeRoutes.obj h012 :=
  (Quiver.FreeGroupoid.of Hist).map (swapFirst 1 0 2 (by decide) (by decide) (by decide))

/-- Integer translations are invertible and count POSITIVE generators,
including independently named generators in the opposite direction. -/
def counterCore : Hist ⥤q Core (Type) where
  obj _ := ⟨Int⟩
  map _ := ⟨{
    hom := TypeCat.ofHom (fun z : Int => z + 1)
    inv := TypeCat.ofHom (fun z : Int => z - 1)
    hom_inv_id := by
      apply TypeCat.homEquiv.injective
      funext z
      change (z + 1) - 1 = z
      omega
    inv_hom_id := by
      apply TypeCat.homEquiv.injective
      funext z
      change (z - 1) + 1 = z
      omega
  }⟩

abbrev groupCounter : FG ⥤ Core (Type) := Reversible.extend counterCore

@[simp] theorem counter_positive {p q : Hist} (r : Exchange.Route p q) (z : Int) :
    (groupCounter.map (includeRoutes.map r)).iso.hom z = z + (r.length : Int) := by
  induction r with
  | nil =>
      rw [Reversible.positive_nil, Functor.map_id]
      change z = z + (0 : Int)
      omega
  | cons r s ih =>
      rw [Reversible.positive_cons, Functor.map_comp, Reversible.extend_generator]
      change (groupCounter.map (includeRoutes.map r)).iso.hom z + 1 =
        z + ((r.length + 1 : Nat) : Int)
      rw [ih]
      omega

theorem opposite_generator_not_formal_inverse : firstBackward ≠ Groupoid.inv firstForward := by
  intro h
  have hv := congrArg (fun r : includeRoutes.obj h102 ⟶ includeRoutes.obj h012 => (groupCounter.map r).iso.hom (0 : Int)) h
  simp only [firstBackward, firstForward, Reversible.extend_inverse,
    Reversible.extend_generator] at hv
  change (1 : Int) = -1 at hv
  omega

/-- It is legitimate to impose that comparison, but it is an explicit new law. -/
def reversalFamily (_ : Unit) : Coherence.ParallelEquation FG :=
  Coherence.reverseGeneratorEquation firstForward firstBackward

abbrev ReversalRel := Coherence.FamilyRelation reversalFamily
abbrev ReversalGroupoid := Coherence.FamilyQuotient reversalFamily
abbrev reversalProjection : FG ⥤ ReversalGroupoid := CategoryTheory.Quotient.functor ReversalRel

theorem memory_respects_reversal (t : ZMod 5) :
    Coherence.Respects ReversalRel (groupMemory t) := by
  rw [Coherence.family_respects_iff]
  intro i
  apply Core.hom_ext
  apply TypeCat.homEquiv.injective
  funext m
  change ((groupMemory t).map firstBackward).iso.hom m =
    ((groupMemory t).map (Groupoid.inv firstForward)).iso.hom m
  simp only [firstBackward, firstForward, Reversible.extend_inverse,
    Reversible.extend_generator]
  rfl

theorem reversal_pair_cancels :
    reversalProjection.map firstForward ≫ reversalProjection.map firstBackward =
      𝟙 (reversalProjection.obj (includeRoutes.obj h012)) := by
  have h := CategoryTheory.Quotient.sound ReversalRel (Coherence.FamilyRelation.equation ())
  change reversalProjection.map firstBackward = reversalProjection.map (Groupoid.inv firstForward) at h
  rw [h]
  simp only [Groupoid.inv_eq_inv, Functor.map_inv]
  simp

/-- Identifying one true reverse pair still does NOT impose the ternary law. -/
theorem reversal_only_preserves_ternary_defect :
    reversalProjection.map routeP ≠ reversalProjection.map routeQ :=
  Coherence.separated_not_generated ReversalRel (groupMemory 2)
    (memory_respects_reversal 2) image_routes_separated

theorem respects_both_iff_zero (t : ZMod 5) :
    Coherence.Respects (Coherence.joinRelation ReversalRel TernaryRel) (groupMemory t) ↔ t = 0 := by
  rw [Coherence.respects_join_iff, groupoid_respects_iff_zero]
  exact ⟨fun h => h.2, fun h => ⟨memory_respects_reversal t, h⟩⟩

/-- Counting positive generators remains a reversible observer and respects
the ternary relation, but not the opposite-generator inverse relation. -/
theorem counter_respects_ternary : Coherence.Respects TernaryRel groupCounter := by
  rw [Coherence.family_respects_iff]
  intro i
  apply Core.hom_ext
  apply TypeCat.homEquiv.injective
  funext z
  change (groupCounter.map (includeRoutes.map route121)).iso.hom z =
    (groupCounter.map (includeRoutes.map route212)).iso.hom z
  rw [counter_positive, counter_positive]
  rfl

/-- The ternary quotient remains nontrivial even after formal inverses exist. -/
theorem ternary_quotient_not_indiscrete :
    ternaryProjection.map routeP ≠
      ternaryProjection.map (includeRoutes.map ExchangeCoherenceControls.longerRoute) := by
  apply Coherence.separated_not_generated TernaryRel groupCounter counter_respects_ternary
  intro h
  have hv := congrArg (fun f : IntFiber ⟶ IntFiber => f.iso.hom (0 : Int)) h
  change (groupCounter.map (includeRoutes.map route121)).iso.hom 0 =
    (groupCounter.map (includeRoutes.map ExchangeCoherenceControls.longerRoute)).iso.hom 0 at hv
  rw [counter_positive, counter_positive] at hv
  have hbad : (3 : Int) = 5 := hv
  omega

end
end CausalGeometry.Models.ExchangeReversibleControls
