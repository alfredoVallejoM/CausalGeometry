import CausalGeometry.Calculus.CausalMetric
import CausalGeometry.Foundation.PairedTransform
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

/-- A linear realization of the structural pair Phi/Psi between two metric
fibers.  Linearity is carried by the maps; no inverse or metric law is
assumed. -/
structure PairedMetricTransport
    (K : Type u)
    (V : Type v)
    (W : Type w)
    [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] where

  forward : V →ₗ[K] W
  backward : W →ₗ[K] V

namespace PairedMetricTransport

variable
    {K : Type u}
    {V : Type v}
    {W : Type w}
    [Field K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (P : PairedMetricTransport K V W)

/-- Forget linearity and recover the foundational structural pair. -/
def toPaired : PairedTransform V W where
  forward := P.forward
  backward := P.backward

def sourceRoundTrip : V →ₗ[K] V :=
  P.backward.comp P.forward

def targetRoundTrip : W →ₗ[K] W :=
  P.forward.comp P.backward

/-- Forward metric defect:
g_W(Phi x,Phi y)-g_V(x,y). -/
def forwardMetricDefect
    (gV : CausalMetric K V)
    (gW : CausalMetric K W)
    (x y : V) : K :=
  gW.pair (P.forward x) (P.forward y) -
    gV.pair x y

/-- Backward metric defect:
g_V(Psi x,Psi y)-g_W(x,y). -/
def backwardMetricDefect
    (gV : CausalMetric K V)
    (gW : CausalMetric K W)
    (x y : W) : K :=
  gV.pair (P.backward x) (P.backward y) -
    gW.pair x y

def ForwardMetricNatural
    (gV : CausalMetric K V)
    (gW : CausalMetric K W) : Prop :=
  ∀ x y,
    gW.pair (P.forward x) (P.forward y) =
      gV.pair x y

def BackwardMetricNatural
    (gV : CausalMetric K V)
    (gW : CausalMetric K W) : Prop :=
  ∀ x y,
    gV.pair (P.backward x) (P.backward y) =
      gW.pair x y

theorem forwardMetricNatural_iff_defect_zero
    (gV : CausalMetric K V)
    (gW : CausalMetric K W) :
    P.ForwardMetricNatural gV gW ↔
      ∀ x y, P.forwardMetricDefect gV gW x y = 0 := by
  constructor
  · intro h x y
    exact sub_eq_zero.mpr (h x y)
  · intro h x y
    exact sub_eq_zero.mp (h x y)

theorem backwardMetricNatural_iff_defect_zero
    (gV : CausalMetric K V)
    (gW : CausalMetric K W) :
    P.BackwardMetricNatural gV gW ↔
      ∀ x y, P.backwardMetricDefect gV gW x y = 0 := by
  constructor
  · intro h x y
    exact sub_eq_zero.mpr (h x y)
  · intro h x y
    exact sub_eq_zero.mp (h x y)

/-- Source round-trip metric defect. -/
def sourceRoundTripMetricDefect
    (gV : CausalMetric K V)
    (x y : V) : K :=
  gV.pair (P.sourceRoundTrip x)
      (P.sourceRoundTrip y) -
    gV.pair x y

/-- Target round-trip metric defect. -/
def targetRoundTripMetricDefect
    (gW : CausalMetric K W)
    (x y : W) : K :=
  gW.pair (P.targetRoundTrip x)
      (P.targetRoundTrip y) -
    gW.pair x y

/-- Exact attribution of source round-trip metric failure:

D_g(Psi Phi)
  = D_g(Psi) evaluated on Phi-images + D_g(Phi).

No preservation law is hidden in the definition. -/
theorem sourceRoundTripMetricDefect_decompose
    (gV : CausalMetric K V)
    (gW : CausalMetric K W)
    (x y : V) :
    P.sourceRoundTripMetricDefect gV x y =
      P.backwardMetricDefect gV gW
        (P.forward x) (P.forward y) +
      P.forwardMetricDefect gV gW x y := by
  unfold sourceRoundTripMetricDefect
    sourceRoundTrip
    backwardMetricDefect
    forwardMetricDefect
  simp only [LinearMap.comp_apply]
  abel

/-- Symmetric target decomposition. -/
theorem targetRoundTripMetricDefect_decompose
    (gV : CausalMetric K V)
    (gW : CausalMetric K W)
    (x y : W) :
    P.targetRoundTripMetricDefect gW x y =
      P.forwardMetricDefect gV gW
        (P.backward x) (P.backward y) +
      P.backwardMetricDefect gV gW x y := by
  unfold targetRoundTripMetricDefect
    targetRoundTrip
    backwardMetricDefect
    forwardMetricDefect
  simp only [LinearMap.comp_apply]
  abel

theorem sourceRoundTrip_metricNatural
    (gV : CausalMetric K V)
    (gW : CausalMetric K W)
    (hF : P.ForwardMetricNatural gV gW)
    (hB : P.BackwardMetricNatural gV gW)
    (x y : V) :
    gV.pair (P.sourceRoundTrip x)
        (P.sourceRoundTrip y) =
      gV.pair x y := by
  unfold sourceRoundTrip
  simp only [LinearMap.comp_apply]
  rw [hB, hF]

theorem targetRoundTrip_metricNatural
    (gV : CausalMetric K V)
    (gW : CausalMetric K W)
    (hF : P.ForwardMetricNatural gV gW)
    (hB : P.BackwardMetricNatural gV gW)
    (x y : W) :
    gW.pair (P.targetRoundTrip x)
        (P.targetRoundTrip y) =
      gW.pair x y := by
  unfold targetRoundTrip
  simp only [LinearMap.comp_apply]
  rw [hF, hB]

end PairedMetricTransport
end CausalGeometry
