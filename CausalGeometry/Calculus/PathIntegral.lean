import CausalGeometry.Calculus.Difference
import CausalGeometry.History.Path
import CausalGeometry.History.Trace
import Mathlib.Tactic

namespace CausalGeometry

universe u v w
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

/-- Discrete line integral of the exact causal difference dF along a derived
causal path. -/
def causalLineIntegral {V : Type w} [AddCommGroup V]
    (F : Configuration S → V)
    {C D : Configuration S} :
    CausalPath S C D → V
  | .nil _ => 0
  | .step e h tail =>
      causalDifference F C e h + causalLineIntegral F tail

/-- Fundamental theorem for exact causal differences: integration along any
finite causal path telescopes to endpoint variation. -/
theorem causalLineIntegral_eq_sub {V : Type w} [AddCommGroup V]
    (F : Configuration S → V)
    {C D : Configuration S}
    (p : CausalPath S C D) :
    causalLineIntegral F p = F D - F C := by
  induction p with
  | nil C =>
      simp [causalLineIntegral]
  | step e h tail ih =>
      simp only [causalLineIntegral, causalDifference, ih]
      abel

/-- Oriented exact-difference integral around a concurrency square. -/
def causalSquareBoundaryIntegral {V : Type w} [AddCommGroup V]
    (F : Configuration S → V)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) : V :=
  causalDifference F C e d.concurrent.1
    + causalDifference F d.afterE f
        (S.concurrent_enabled_after_left d.concurrent)
    - causalDifference F C f d.concurrent.2.1
    - causalDifference F d.afterF e
        (S.concurrent_enabled_after_right d.concurrent)

/-- Discrete Stokes theorem for a flat causal concurrency square: the integral
of an exact causal difference around the boundary vanishes. -/
theorem causalSquareBoundaryIntegral_eq_zero
    {V : Type w} [AddCommGroup V]
    (F : Configuration S → V)
    {C : Configuration S} {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    causalSquareBoundaryIntegral F d = 0 := by
  unfold causalSquareBoundaryIntegral causalDifference
  rw [ConcurrencyDiamond.endpoint_eq d]
  abel

end CausalGeometry
