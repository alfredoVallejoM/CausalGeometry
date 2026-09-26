import CausalGeometry.Calculus.CausalTorsion
import Mathlib.Tactic

namespace CausalGeometry

universe u v w x
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}
variable {K : Type w} {V : Type x}
variable [Field K] [CharZero K]
variable [AddCommGroup V] [Module K V]

namespace CausalGaugePotential

variable {C : Configuration S}

/-- Metric pairing of a local connection coefficient. -/
def christoffelPair
    (A : CausalGaugePotential K S V C)
    (g : CausalMetric K V)
    (theta : CausalSolderForm K S V C)
    (d e f : EventDirection S C) : K :=
  g.pair
    (A.operator d (theta.value e))
    (theta.value f)

/-- Bracket pairing used by the causal Koszul formula. -/
def bracketPair
    (g : CausalMetric K V)
    (theta : CausalSolderForm K S V C)
    (B : CausalDirectionBracket S V C)
    (d e f : EventDirection S C) : K :=
  g.pair (B.value d e) (theta.value f)

/-- Local causal Koszul identity.

For a metric-compatible torsion-free local connection, the coefficient
g(A_d theta(e), theta(f)) is completely determined by the bracket data:

2 Gamma(d,e,f)
  = <B(d,e),f> - <B(e,f),d> + <B(f,d),e>.

This is derived rather than built into the connection structure. -/
theorem koszul_identity
    (A : CausalGaugePotential K S V C)
    (g : CausalMetric K V)
    (theta : CausalSolderForm K S V C)
    (B : CausalDirectionBracket S V C)
    (hmetric : A.MetricCompatibleLocal g)
    (hT : A.TorsionFree theta B)
    (d e f : EventDirection S C) :
    (2 : K) * A.christoffelPair g theta d e f =
      bracketPair g theta B d e f
        - bracketPair g theta B e f d
        + bracketPair g theta B f d e := by

  have h1 :=
    A.torsion_pair g theta B hT d e f
  have h2 :=
    A.torsion_pair g theta B hT e f d
  have h3 :=
    A.torsion_pair g theta B hT f d e

  have m1 :=
    A.metric_skew g hmetric e
      (theta.value d) (theta.value f)
  have m2 :=
    A.metric_skew g hmetric f
      (theta.value e) (theta.value d)
  have m3 :=
    A.metric_skew g hmetric d
      (theta.value f) (theta.value e)

  unfold christoffelPair bracketPair

  rw [m1] at h1
  rw [m2] at h2
  rw [m3] at h3

  linear_combination h1 - h2 + h3

/-- Any two local metric-compatible torsion-free potentials agree on every
soldered direction once the solder form spans the fiber. -/
theorem leviCivita_agree_on_solder
    (A A' : CausalGaugePotential K S V C)
    (g : CausalMetric K V)
    (theta : CausalSolderForm K S V C)
    (B : CausalDirectionBracket S V C)
    (hspan : theta.Spans)
    (hmetric : A.MetricCompatibleLocal g)
    (hmetric' : A'.MetricCompatibleLocal g)
    (hT : A.TorsionFree theta B)
    (hT' : A'.TorsionFree theta B)
    (d e : EventDirection S C) :
    A.operator d (theta.value e) =
      A'.operator d (theta.value e) := by

  apply sub_eq_zero.mp
  apply g.eq_zero_of_pair_all_zero
  intro y

  have hzeroOnRange :
      ∀ f : EventDirection S C,
        g.pair
            (A.operator d (theta.value e) -
              A'.operator d (theta.value e))
            (theta.value f)
          =
        0 := by
    intro f
    have hA :=
      A.koszul_identity g theta B
        hmetric hT d e f
    have hA' :=
      A'.koszul_identity g theta B
        hmetric' hT' d e f
    have htwo :
        (2 : K) *
          (g.pair
              (A.operator d (theta.value e))
              (theta.value f)
            -
           g.pair
              (A'.operator d (theta.value e))
              (theta.value f))
          =
        0 := by
      rw [mul_sub, hA, hA']
      ring
    have h2 : (2 : K) ≠ 0 := by
      norm_num
    have hz :
        g.pair
              (A.operator d (theta.value e))
              (theta.value f)
            -
           g.pair
              (A'.operator d (theta.value e))
              (theta.value f)
          =
        0 :=
      (mul_eq_zero.mp htwo).resolve_left h2
    simpa [CausalMetric.pair, map_sub] using hz

  -- Use spanning directly on the scalar linear functional obtained after
  -- fixing the difference vector on theta(e).
  let phi : V →ₗ[K] K :=
    g.form
      (A.operator d (theta.value e) -
        A'.operator d (theta.value e))

  have hRangePhi :
      Set.range theta.value ⊆ phi.ker := by
    rintro z ⟨f, rfl⟩
    exact hzeroOnRange f

  have hSpanPhi :
      Submodule.span K (Set.range theta.value) ≤
        phi.ker :=
    Submodule.span_le.mpr hRangePhi

  have hTopPhi :
      (⊤ : Submodule K V) ≤ phi.ker := by
    simpa [hspan] using hSpanPhi

  change phi y = 0
  exact hTopPhi Submodule.mem_top

/-- Causal Levi-Civita uniqueness theorem for the local linearized model.

Once the soldered event directions span the fiber, there is at most one local
gauge potential compatible with the metric and torsion-free relative to the
same bracket. -/
theorem leviCivita_unique
    (A A' : CausalGaugePotential K S V C)
    (g : CausalMetric K V)
    (theta : CausalSolderForm K S V C)
    (B : CausalDirectionBracket S V C)
    (hspan : theta.Spans)
    (hmetric : A.MetricCompatibleLocal g)
    (hmetric' : A'.MetricCompatibleLocal g)
    (hT : A.TorsionFree theta B)
    (hT' : A'.TorsionFree theta B) :
    A = A' := by
  cases A with
  | mk op =>
    cases A' with
    | mk op' =>
      congr
      funext d
      exact
        theta.linearMap_ext_of_spans
          hspan
          (op d) (op' d)
          (fun e =>
            leviCivita_agree_on_solder
              ⟨op⟩ ⟨op'⟩ g theta B
              hspan hmetric hmetric'
              hT hT' d e)

/-- In the canonical commuting-direction sector B=0, the Koszul identity forces
all local connection coefficients on soldered directions to vanish. -/
theorem koszul_zeroBracket
    (A : CausalGaugePotential K S V C)
    (g : CausalMetric K V)
    (theta : CausalSolderForm K S V C)
    (hmetric : A.MetricCompatibleLocal g)
    (hT :
      A.TorsionFree theta
        (CausalDirectionBracket.zero
          (S := S) (V := V) (C := C)))
    (d e f : EventDirection S C) :
    A.christoffelPair g theta d e f = 0 := by
  have h :=
    A.koszul_identity g theta
      (CausalDirectionBracket.zero
        (S := S) (V := V) (C := C))
      hmetric hT d e f
  simp [bracketPair] at h
  have h2 : (2 : K) ≠ 0 := by
    norm_num
  exact (mul_eq_zero.mp h).resolve_left h2

end CausalGaugePotential
end CausalGeometry
