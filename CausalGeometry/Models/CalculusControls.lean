import CausalGeometry.Calculus.GaugeCovariance
import Mathlib.Tactic

namespace CausalGeometry.Models

open EventSystem

/-- Two primitive events with no precedence and no conflict. -/
def twoEventSystem : EventSystem Bool Unit where
  precedes := fun _ _ => False
  conflict := fun _ _ => False
  label := fun _ => ()
  precedes_irrefl := by
    intro e h
    exact h
  precedes_trans := by
    intro a b c h
    exact False.elim h
  conflict_symm := by
    intro a b h
    exact h
  conflict_irrefl := by
    intro e h
    exact h
  conflict_future := by
    intro e f g h
    exact False.elim h

theorem twoEvent_enabled_empty (e : Bool) :
    twoEventSystem.Enabled twoEventSystem.empty e := by
  refine ⟨?_, ?_, ?_⟩
  · simp [EventSystem.empty]
  · intro f h
    exact False.elim h
  · intro f hf h
    exact False.elim h

def twoEventDiamond :
    ConcurrencyDiamond twoEventSystem.empty false true where
  concurrent := by
    refine ⟨twoEvent_enabled_empty false,
      twoEvent_enabled_empty true, ?_, ?_, ?_, ?_⟩
    · simp [twoEventSystem]
    · simp [twoEventSystem]
    · simp [twoEventSystem]
    · decide

/-- A flat positive control. -/
def identityLinearConnection :
    LinearCausalConnection ℤ twoEventSystem (ℤ × ℤ) where
  transport := fun _ _ _ => LinearMap.id

theorem identityLinearConnection_flat :
    identityLinearConnection.FlatOn twoEventDiamond := by
  unfold LinearCausalConnection.FlatOn
  ext x
  rfl

/-- First noncommuting transport generator: (x,y) ↦ (y,0). -/
def transportA : (ℤ × ℤ) →ₗ[ℤ] (ℤ × ℤ) where
  toFun := fun p => (p.2, 0)
  map_add' := by
    intro x y
    ext <;> simp
  map_smul' := by
    intro c x
    ext <;> simp

/-- Second noncommuting transport generator: (x,y) ↦ (0,x). -/
def transportB : (ℤ × ℤ) →ₗ[ℤ] (ℤ × ℤ) where
  toFun := fun p => (0, p.1)
  map_add' := by
    intro x y
    ext <;> simp
  map_smul' := by
    intro c x
    ext <;> simp

/-- Same base causal system, but event transports do not commute. -/
def noncommutingLinearConnection :
    LinearCausalConnection ℤ twoEventSystem (ℤ × ℤ) where
  transport := fun _ e _ =>
    match e with
    | false => transportA
    | true => transportB

theorem noncommuting_transportEF_test :
    noncommutingLinearConnection.transportEF twoEventDiamond (1, 0) =
      (0, 0) := by
  norm_num [LinearCausalConnection.transportEF,
    noncommutingLinearConnection, transportA, transportB,
    twoEventDiamond]

theorem noncommuting_transportFE_test :
    noncommutingLinearConnection.transportFE twoEventDiamond (1, 0) =
      (1, 0) := by
  norm_num [LinearCausalConnection.transportFE,
    noncommutingLinearConnection, transportA, transportB,
    twoEventDiamond]

/-- Same-type adversarial mutation: causal connection does not imply flatness. -/
theorem noncommutingLinearConnection_not_flat :
    ¬ noncommutingLinearConnection.FlatOn twoEventDiamond := by
  intro h
  have hx := congrArg
    (fun L : (ℤ × ℤ) →ₗ[ℤ] (ℤ × ℤ) => L (1, 0)) h
  rw [noncommuting_transportEF_test, noncommuting_transportFE_test] at hx
  norm_num at hx

end CausalGeometry.Models
