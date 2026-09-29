import CausalGeometry.Exchange.LinearizedCausalAction
import CausalGeometry.Exchange.TensorTransportDefect
import CausalGeometry.Calculus.GradedDefectCompatibility
import CausalGeometry.Models.ExchangeTransportControls

/-!
# CX-I6: source-connected nonzero defects and anti-overclaim controls

All event/history inputs are the old three-event source. Linear combinations
are formal observations, not probabilities or a change of causal ontology.
-/
namespace CausalGeometry.Models.ExchangeLinearDefectControls

open CausalGeometry.Exchange LocalOperator OperatorTransport LinearizedAction
open CausalGeometry.Models.ExchangeThreeEvents
open CausalGeometry.Models.ExchangeOperatorControls
open CausalGeometry.Models.ExchangeTransportControls
open CategoryTheory
noncomputable section

/-- A whole genuine causal route can fail coefficient naturality. -/
theorem causal_defect_nonzero :
    LinearizedAction.defect (K := ℚ) (id : Bool → Bool) flip toggleFirst route121 ≠ 0 := by
  intro h
  have hx := (LinearizedAction.defect_zero_iff (K := ℚ)
    (id : Bool → Bool) flip toggleFirst route121).mp h zeroState
  have hv := congrArg Subtype.val hx
  change ([false, true, false] : List Bool) = [false, false, false] at hv
  cases hv

theorem reverse_causal_defect_nonzero :
    LinearizedAction.defect (K := ℚ) (id : Bool → Bool) toggleFirst flip route121 ≠ 0 := by
  intro h
  have hx := (LinearizedAction.defect_zero_iff (K := ℚ)
    (id : Bool → Bool) toggleFirst flip route121).mp h zeroState
  have hv := congrArg Subtype.val hx
  change ([false, false, false] : List Bool) = [false, true, false] at hv
  cases hv

/-- Both directional failures can cancel in a round trip. Zero total defect
therefore does not prove either intermediate square was compatible. -/
theorem nonzero_directional_defects_zero_roundtrip :
    LinearizedAction.defect (K := ℚ) (id : Bool → Bool) flip toggleFirst route121 ≠ 0 ∧
    LinearizedAction.defect (K := ℚ) (id : Bool → Bool) toggleFirst flip route121 ≠ 0 ∧
    LinearizedAction.defect (K := ℚ) (id : Bool → Bool) flip flip route121 = 0 := by
  exact ⟨causal_defect_nonzero, reverse_causal_defect_nonzero,
    LinearizedAction.defect_zero_of_intertwines _ _ _ (intertwines_id _) _⟩

/-- I5's forward-only example survives canonical linearization. -/
theorem forward_only_defect_zero :
    LinearizedAction.defect (K := ℚ) forwardOnly.forward copyRight flip route121 = 0 :=
  LinearizedAction.defect_zero_of_intertwines _ _ _ forward_only_intertwines _

def middleState : Sized Bool h012.length :=
  ⟨[false, true, false], zeroState.property⟩

theorem backward_only_defect_nonzero :
    LinearizedAction.defect (K := ℚ) forwardOnly.backward flip copyRight route121 ≠ 0 := by
  intro h
  have hx := (LinearizedAction.defect_zero_iff (K := ℚ)
    forwardOnly.backward flip copyRight route121).mp h middleState
  have hv := congrArg Subtype.val hx
  change ([false, false, false] : List Bool) = [false, true, false] at hv
  cases hv

/-- Forgetting all Boolean coefficients erases a real mismatch. -/
theorem collapse_erases_route_defect :
    LinearizedAction.defect (K := ℚ) collapse toggleFirst singletonOperator route121 = 0 :=
  LinearizedAction.defect_zero_of_intertwines _ _ _ collapse_intertwines _

/-- A compatible pair can still have a genuinely nonidentity source round trip. -/
theorem compatible_not_identity :
    LinearizedAction.defect (K := ℚ) collapsingPair.sourceRoundTrip flip flip route121 = 0 ∧
      collapsingPair.sourceRoundTrip true ≠ true := by
  exact ⟨LinearizedAction.defect_zero_of_intertwines _ _ _
    (CausalOperatorTransport.sourceRoundTrip_intertwines _ _ _ collapsingPair_compatible) _,
    roundTrip_not_identity⟩

abbrev Plane := ℚ × ℚ

def swapLinear : Plane →ₗ[ℚ] Plane where
  toFun x := (x.2, x.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def projectRight : Plane →ₗ[ℚ] Plane where
  toFun x := (0, x.2)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

def targetLinear : Plane →ₗ[ℚ] Plane := swapLinear + projectRight

/-- A maximal pointwise compatibility subspace need NOT be forward invariant. -/
theorem compatible_domain_not_invariant :
    (1, 0) ∈ LinearSquare.compatibleDomain swapLinear targetLinear LinearMap.id LinearMap.id ∧
      swapLinear (1, 0) ∉
        LinearSquare.compatibleDomain swapLinear targetLinear LinearMap.id LinearMap.id := by
  constructor
  · rw [LinearSquare.mem_compatibleDomain]
    ext <;> norm_num [targetLinear, swapLinear, projectRight]
  · rw [LinearSquare.mem_compatibleDomain]
    intro h
    have hb := congrArg Prod.snd h
    norm_num [targetLinear, swapLinear, projectRight] at hb

/-- Purely algebraic same-type cancellation; neither directional defect is zero. -/
theorem square_cancellation :
    LinearSquare.defect (0 : ℚ →ₗ[ℚ] ℚ) LinearMap.id LinearMap.id LinearMap.id ≠ 0 ∧
    LinearSquare.defect (LinearMap.id : ℚ →ₗ[ℚ] ℚ) 0 LinearMap.id LinearMap.id ≠ 0 ∧
    LinearSquare.defect (0 : ℚ →ₗ[ℚ] ℚ) 0 LinearMap.id LinearMap.id = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hh := LinearMap.congr_fun h 1
    norm_num [LinearSquare.defect] at hh
  · intro h
    have hh := LinearMap.congr_fun h 1
    norm_num [LinearSquare.defect] at hh
  · ext x
    simp [LinearSquare.defect]

end CausalGeometry.Models.ExchangeLinearDefectControls
