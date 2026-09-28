import CausalGeometry.Exchange.Path
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# CX-I1: actual three-event histories and distinguishable exchange routes

All vertices are CausalPath values over one EventSystem. The six arrows are
witnessed concurrency diamonds with actual prefixes and suffixes. Positions
are derived from prefix lengths. The ZMod 5 fiber is only an observation; it
is neither an event nor a new primitive field of the causal source.
-/
namespace CausalGeometry.Models.ExchangeThreeEvents

open EventSystem CausalVariational Exchange CategoryTheory

/-- Three distinct, compatible occurrences; no imposed geometry or state. -/
def system : EventSystem (Fin 3) Unit where
  precedes := fun _ _ => False
  conflict := fun _ _ => False
  label := fun _ => ()
  precedes_irrefl := by intro _ h; exact h
  precedes_trans := by intro _ _ _ h _; exact h
  conflict_symm := by intro _ _ h; exact h
  conflict_irrefl := by intro _ h; exact h
  conflict_future := by intro _ _ _ h _; exact h

def initial : Configuration system := system.empty

def terminal : Configuration system where
  carrier := Set.univ
  downClosed := by intro _ _ _ _; trivial
  conflictFree := by intro _ _ _ _ h; exact h

/-- In this particular independent-event model, absence is sufficient. -/
def enabledOfAbsent (C : Configuration system) (i : Fin 3) (h : i ∉ C) :
    system.Enabled C i :=
  ⟨h, by intro _ hp; exact False.elim hp, by intro _ _ hf; exact hf⟩

def enabledInitial (i : Fin 3) : system.Enabled initial i :=
  enabledOfAbsent initial i (by simp [initial, EventSystem.empty])

def afterOne (i : Fin 3) : Configuration system :=
  system.extend initial i (enabledInitial i)

def onePath (i : Fin 3) : CausalPath system initial (afterOne i) :=
  .step i (enabledInitial i) (.nil _)

def initialDiamond (i j : Fin 3) (hij : i ≠ j) :
    ConcurrencyDiamond initial i j where
  concurrent := ⟨enabledInitial i, enabledInitial j,
    not_false, not_false, not_false, hij⟩

def afterTwo (i j : Fin 3) (hij : i ≠ j) : Configuration system :=
  (initialDiamond i j hij).afterEF

def enabledThird (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    system.Enabled (afterTwo i j hij) k :=
  enabledOfAbsent _ k (by
    change k ∉ insert j (insert i (∅ : Set (Fin 3)))
    simp [Ne.symm hik, Ne.symm hjk])

theorem third_endpoint (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    system.extend (afterTwo i j hij) k (enabledThird i j k hij hik hjk) = terminal := by
  apply system.configuration_eq_of_carrier_eq
  ext x
  change (x = k ∨ x = j ∨ x = i ∨ False) ↔ True
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases x <;> simp_all

/-- Actual final event, transported only along the proved configuration equality. -/
def lastPath (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    CausalPath system (afterTwo i j hij) terminal :=
  (CausalPath.step k (enabledThird i j k hij hik hjk) (.nil _)).castEnd
    (third_endpoint i j k hij hik hjk)

@[simp] theorem lastPath_eventList (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (lastPath i j k hij hik hjk).eventList = [k] := by
  simp only [lastPath, CausalPath.eventList_castEnd,
    CausalPath.eventList_step, CausalPath.eventList_nil]

def history (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    CausalPath system initial terminal :=
  (diamondPathEF (initialDiamond i j hij)).comp (lastPath i j k hij hik hjk)

@[simp] theorem history_eventList (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (history i j k hij hik hjk).eventList = [i, j, k] := by
  simp [history]

def secondDiamond (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ConcurrencyDiamond (afterOne i) j k where
  concurrent := ⟨
    enabledOfAbsent _ j (by
      change j ∉ insert i (∅ : Set (Fin 3))
      simp [Ne.symm hij]),
    enabledOfAbsent _ k (by
      change k ∉ insert i (∅ : Set (Fin 3))
      simp [Ne.symm hik]),
    not_false, not_false, not_false, hjk⟩

theorem secondDiamond_endpoint (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (secondDiamond i j k hij hik hjk).afterEF = terminal := by
  apply system.configuration_eq_of_carrier_eq
  ext x
  change (x = k ∨ x = j ∨ x = i ∨ False) ↔ True
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases x <;> simp_all

/-- Exchange at position zero, backed by the initial diamond and final event. -/
def swapFirst (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Exchange.Step (history i j k hij hik hjk)
      (history j i k hij.symm hjk hik) where
  pivot := initial
  first := i
  second := j
  diamond := initialDiamond i j hij
  prefix := .nil initial
  suffix := lastPath i j k hij hik hjk
  source_eq := rfl
  target_eq := by
    apply CausalPath.eq_of_eventList_eq
    simp

/-- Exchange at position one, backed by a diamond AFTER the first event. -/
def swapSecond (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Exchange.Step (history i j k hij hik hjk)
      (history i k j hik hij hjk.symm) where
  pivot := afterOne i
  first := j
  second := k
  diamond := secondDiamond i j k hij hik hjk
  prefix := onePath i
  suffix := (CausalPath.nil _).castEnd (secondDiamond_endpoint i j k hij hik hjk)
  source_eq := by
    apply CausalPath.eq_of_eventList_eq
    simp [onePath]
  target_eq := by
    apply CausalPath.eq_of_eventList_eq
    simp [onePath]

@[simp] theorem swapFirst_position (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (swapFirst i j k hij hik hjk).position = 0 := rfl

@[simp] theorem swapSecond_position (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (swapSecond i j k hij hik hjk).position = 1 := rfl

abbrev h012 := history 0 1 2 (by decide) (by decide) (by decide)
abbrev h102 := history 1 0 2 (by decide) (by decide) (by decide)
abbrev h120 := history 1 2 0 (by decide) (by decide) (by decide)
abbrev h210 := history 2 1 0 (by decide) (by decide) (by decide)
abbrev h021 := history 0 2 1 (by decide) (by decide) (by decide)
abbrev h201 := history 2 0 1 (by decide) (by decide) (by decide)

def route121 : Exchange.Route h012 h210 :=
  ((Quiver.Path.nil.cons (swapFirst 0 1 2 (by decide) (by decide) (by decide))).cons
    (swapSecond 1 0 2 (by decide) (by decide) (by decide))).cons
    (swapFirst 1 2 0 (by decide) (by decide) (by decide))

def route212 : Exchange.Route h012 h210 :=
  ((Quiver.Path.nil.cons (swapSecond 0 1 2 (by decide) (by decide) (by decide))).cons
    (swapFirst 0 2 1 (by decide) (by decide) (by decide))).cons
    (swapSecond 2 0 1 (by decide) (by decide) (by decide))

@[simp] theorem route121_positions : route121.positions = [0, 1, 0] := rfl
@[simp] theorem route212_positions : route212.positions = [1, 0, 1] := rfl

/-- The free source keeps these routes distinct. No inverse/YB quotient was taken. -/
theorem routes_distinct : route121 ≠ route212 := by
  intro h
  have hw := congrArg (fun r : Exchange.Route h012 h210 => r.positions) h
  have hbad : ([0, 1, 0] : List Nat) = [1, 0, 1] := hw
  cases hbad

/-- One family of same-typed observers. The parameter is in the realization,
not in EventSystem. Offset zero is the positive symmetric control. -/
def memoryPrefunctor (offset : ZMod 5) :
    CausalPath system initial terminal ⥤q Type where
  obj _ := ZMod 5
  map s := TypeCat.ofHom (fun m : ZMod 5 =>
    if s.position % 2 = 0 then -m else offset - m)

def observed (offset : ZMod 5) {p q : CausalPath system initial terminal}
    (r : Exchange.Route p q) (m : ZMod 5) : ZMod 5 :=
  (Exchange.interpret (memoryPrefunctor offset)).map r m

@[simp] theorem observed_nil (offset : ZMod 5)
    (p : CausalPath system initial terminal) (m : ZMod 5) :
    observed offset (Quiver.Path.nil : Exchange.Route p p) m = m := rfl

@[simp] theorem observed_cons (offset : ZMod 5)
    {p q r : CausalPath system initial terminal}
    (a : Exchange.Route p q) (s : Exchange.Step q r) (m : ZMod 5) :
    observed offset (a.cons s) m =
      if s.position % 2 = 0 then -(observed offset a m)
      else offset - observed offset a m := rfl

/-- Both actions have exact algebraic formulas, not only one sampled value. -/
theorem observed_route121 (offset m : ZMod 5) :
    observed offset route121 m = -offset - m := by
  simp [route121, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

theorem observed_route212 (offset m : ZMod 5) :
    observed offset route212 m = offset + offset - m := by
  simp [route212, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

theorem observed_three_four :
    observed 2 route121 0 = 3 ∧ observed 2 route212 0 = 4 := by
  rw [observed_route121, observed_route212]
  norm_num

/-- Same source routes, same target type; a different observer forgets the defect. -/
theorem zero_offset_forgets (m : ZMod 5) :
    observed 0 route121 m = observed 0 route212 m := by
  rw [observed_route121, observed_route212]
  simp

/-- Individual exchange actions are involutions, even in the non-YB control. -/
theorem elementary_involutive (offset : ZMod 5)
    {p q : CausalPath system initial terminal} (s : Exchange.Step p q) (m : ZMod 5) :
    let f := (memoryPrefunctor offset).map s
    f (f m) = m := by
  dsimp [memoryPrefunctor]
  split_ifs <;> abel

end CausalGeometry.Models.ExchangeThreeEvents
