import CausalGeometry.Exchange.Variational
import CausalGeometry.Models.ExchangeThreeEvents
import CausalGeometry.Variational.QuasiNoether
import CausalGeometry.Variational.CausalMomentumMap

/-!
This harness is not part of the ordinary root import. It must be executed by
Lean; textual presence of these commands does not certify their outputs.
-/
#print axioms CausalGeometry.CausalPath.comp_assoc
#print axioms CausalGeometry.CausalPath.comp_nil
#print axioms CausalGeometry.CausalPath.eq_of_eventList_eq
#print axioms CausalGeometry.Exchange.Step.length_eq
#print axioms CausalGeometry.Exchange.Step.position_bound
#print axioms CausalGeometry.Exchange.Step.not_conflict
#print axioms CausalGeometry.Exchange.Step.distinct_occurrences
#print axioms CausalGeometry.Exchange.interpret_unique
#print axioms CausalGeometry.Exchange.Route.historyLength_eq
#print axioms CausalGeometry.Exchange.Step.actionDifference_eq
#print axioms CausalGeometry.Exchange.Route.preservesAction
#print axioms CausalGeometry.Models.ExchangeThreeEvents.third_endpoint
#print axioms CausalGeometry.Models.ExchangeThreeEvents.secondDiamond_endpoint
#print axioms CausalGeometry.Models.ExchangeThreeEvents.routes_distinct
#print axioms CausalGeometry.Models.ExchangeThreeEvents.observed_route121
#print axioms CausalGeometry.Models.ExchangeThreeEvents.observed_route212
#print axioms CausalGeometry.Models.ExchangeThreeEvents.observed_three_four
#print axioms CausalGeometry.Models.ExchangeThreeEvents.zero_offset_forgets
#print axioms CausalGeometry.Models.ExchangeThreeEvents.elementary_involutive
#print axioms CausalGeometry.CausalVariational.actionDifference_diamondPaths
#print axioms CausalGeometry.CausalVariational.elementaryEulerLagrange_iff_swapStationary
#print axioms CausalGeometry.CausalVariational.elementaryEulerLagrange_addBoundary_iff
