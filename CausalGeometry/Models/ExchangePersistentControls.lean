import CausalGeometry.Exchange.PersistentCompatibility
import CausalGeometry.Models.ExchangeLinearDefectControls

/-!
# Proper persistent domains and genuine delayed failures

Every route in these controls is a route of the old three-event EventSystem.
The local mutation agrees at BOTH available first steps, then fails after a
second admitted step. Scalar observations and terminal agreement are weaker.
-/
namespace CausalGeometry.Models.ExchangePersistentControls

open CategoryTheory CausalGeometry.Exchange LocalOperator OperatorTransport LinearizedAction
open CausalGeometry.Models.ExchangeThreeEvents
open CausalGeometry.Models.ExchangeOperatorControls
open CausalGeometry.Models.ExchangeLinearDefectControls
noncomputable section

/-- The old flip/copy pair has a nonzero persistent state without being globally compatible. -/
theorem constant_is_persistent :
    ModuleCat.freeMk (Persistent.constantState false h012.length) ∈
      Persistent.domain (K := ℚ) (id : Bool → Bool) flip copyRight h012 :=
  Persistent.constant_basis_mem _ _ _ false rfl rfl h012

theorem constant_basis_nonzero :
    (ModuleCat.freeMk (R := ℚ) (Persistent.constantState false h012.length)) ≠ 0 := by
  intro h
  have he := congrArg (fun z => z (Persistent.constantState false h012.length)) h
  simp [ModuleCat.freeMk] at he

/-- Same source and portador: a different state is already rejected by the old route121. -/
theorem middle_not_persistent :
    ModuleCat.freeMk middleState ∉
      Persistent.domain (K := ℚ) (id : Bool → Bool) flip copyRight h012 := by
  intro hx
  have h := (Persistent.basis_mem_iff (K := ℚ) (id : Bool → Bool)
    flip copyRight h012 middleState).mp hx h210 route121
  have hv := congrArg Subtype.val h
  change ([false,false,false] : List Bool) = [false,true,false] at hv
  cases hv

/-- The constructed subdomain is neither bottom nor top. -/
theorem persistent_nonzero_proper :
    Persistent.domain (K := ℚ) (id : Bool → Bool) flip copyRight h012 ≠ ⊥ ∧
    Persistent.domain (K := ℚ) (id : Bool → Bool) flip copyRight h012 ≠ ⊤ := by
  constructor
  · intro h
    have hx := constant_is_persistent
    rw [h] at hx
    exact constant_basis_nonzero hx
  · intro h
    apply middle_not_persistent
    rw [h]
    trivial

/-- This operator agrees with flip except at the pair (false,false). -/
def wakeZero : PairOperator Bool := fun p =>
  if p.1 || p.2 then (p.2,p.1) else (true,true)

def delayedRoute : Route h012 h120 :=
  (Quiver.Path.nil.cons (swapFirst 0 1 2 (by decide) (by decide) (by decide))).cons
    (swapSecond 1 0 2 (by decide) (by decide) (by decide))

/-- All actual outgoing generators are initially compatible on this basis state. -/
theorem middle_locally_compatible :
    ModuleCat.freeMk middleState ∈
      Persistent.generatorDomain (K := ℚ) (id : Bool → Bool) flip wakeZero h012 := by
  intro q s
  change LinearizedAction.defect (K := ℚ) (id : Bool → Bool) flip wakeZero s.toPath
    (ModuleCat.freeMk middleState) = 0
  rw [LinearizedAction.defect_basis]
  apply sub_eq_zero.mpr
  apply congrArg (ModuleCat.freeMk (R := ℚ))
  apply Subtype.ext
  have hb := s.position_bound
  have hn : h012.length = 3 := by simpa using zeroState.property.symm
  have hp : s.position = 0 ∨ s.position = 1 := by omega
  change stepList wakeZero s.position [false,true,false] =
    List.map id (stepList flip s.position [false,true,false])
  rcases hp with hp | hp <;> rw [hp] <;> rfl

/-- Requiring every prefix catches a failure not visible in the outgoing kernels alone. -/
theorem middle_delayed_failure :
    ModuleCat.freeMk middleState ∉
      Persistent.domain (K := ℚ) (id : Bool → Bool) flip wakeZero h012 := by
  intro hx
  have h := (Persistent.basis_mem_iff (K := ℚ) (id : Bool → Bool)
    flip wakeZero h012 middleState).mp hx h120 delayedRoute
  have hv := congrArg Subtype.val h
  change ([true,true,true] : List Bool) = [true,false,false] at hv
  cases hv

theorem outgoing_kernels_are_not_persistent_domain :
    Persistent.generatorDomain (K := ℚ) (id : Bool → Bool) flip wakeZero h012 ≠
      Persistent.domain (K := ℚ) (id : Bool → Bool) flip wakeZero h012 := by
  intro h
  exact middle_delayed_failure (h ▸ middle_locally_compatible)

/-- The cancelling composite from I6 does not retrospectively repair its factors. -/
theorem composition_inclusion_can_be_strict :
    (Persistent.domain (K := ℚ) (id : Bool → Bool) flip toggleFirst h012 ⊓
      (Persistent.domain (K := ℚ) (id : Bool → Bool) toggleFirst flip h012).comap
        (coefficient ℚ (id : Bool → Bool) h012.length)) ≠
      Persistent.domain (K := ℚ) (id : Bool → Bool) flip flip h012 := by
  intro h
  have hz : ModuleCat.freeMk zeroState ∈
      Persistent.domain (K := ℚ) (id : Bool → Bool) flip flip h012 := by
    rw [Persistent.domain_top_of_intertwines _ _ _ (intertwines_id _)]; trivial
  have hleft := h.symm ▸ hz
  have hx := (Persistent.basis_mem_iff (K := ℚ) (id : Bool → Bool)
    flip toggleFirst h012 zeroState).mp hleft.1 h210 route121
  have hv := congrArg Subtype.val hx
  change ([false,true,false] : List Bool) = [false,false,false] at hv
  cases hv

/-- A projection onto a singleton is compatible everywhere, but has no recovery claim. -/
theorem lossy_observation_has_full_domain :
    Persistent.domain (K := ℚ) ExchangeTransportControls.collapse
      toggleFirst ExchangeTransportControls.singletonOperator h012 = ⊤ :=
  Persistent.domain_top_of_intertwines _ _ _ ExchangeTransportControls.collapse_intertwines _

end CausalGeometry.Models.ExchangePersistentControls
