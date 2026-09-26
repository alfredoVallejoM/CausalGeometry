import CausalGeometry.Calculus.CausalMetric
import CausalGeometry.Calculus.GaugePotential
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic

namespace CausalGeometry

universe u v w x
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}
variable {K : Type w} {V : Type x}
variable [Field K] [AddCommGroup V] [Module K V]

/-- A causal solder form at one configuration realizes each enabled primitive
event direction as an actual vector in the local linear fiber.

No linear structure is imposed on EventDirection itself. -/
structure CausalSolderForm
    (K : Type w)
    (S : EventSystem Event Label)
    (V : Type x)
    (C : Configuration S)
    [Field K] [AddCommGroup V] [Module K V] where

  value : EventDirection S C → V

namespace CausalSolderForm

variable {C : Configuration S}

/-- The solder form is spanning when its realized causal directions generate
the entire local fiber. -/
def Spans
    (theta : CausalSolderForm K S V C) : Prop :=
  Submodule.span K (Set.range theta.value) = ⊤

/-- A linear map is determined by its values on a spanning solder form. -/
theorem linearMap_ext_of_spans
    (theta : CausalSolderForm K S V C)
    (hspan : theta.Spans)
    (A B : V →ₗ[K] V)
    (hdir : ∀ d, A (theta.value d) = B (theta.value d)) :
    A = B := by
  apply LinearMap.ext
  intro x
  have hrange :
      Set.range theta.value ⊆
        LinearMap.ker (A - B) := by
    rintro y ⟨d, rfl⟩
    change A (theta.value d) - B (theta.value d) = 0
    exact sub_eq_zero.mpr (hdir d)
  have hspanKer :
      Submodule.span K (Set.range theta.value) ≤
        LinearMap.ker (A - B) :=
    Submodule.span_le.mpr hrange
  have hx :
      x ∈ LinearMap.ker (A - B) := by
    have htop :
        (⊤ : Submodule K V) ≤
          LinearMap.ker (A - B) := by
      simpa [hspan] using hspanKer
    exact htop Submodule.mem_top
  change A x - B x = 0 at hx
  exact sub_eq_zero.mp hx

end CausalSolderForm

/-- A vector-valued antisymmetric bracket on enabled causal directions.

For pairwise-concurrent event directions the canonical commuting bracket is
zero, but the explicit interface also supports non-holonomic realizations. -/
structure CausalDirectionBracket
    (S : EventSystem Event Label)
    (V : Type x)
    (C : Configuration S)
    [AddCommGroup V] where

  value :
    EventDirection S C →
      EventDirection S C → V

  skew :
    ∀ d e,
      value d e = - value e d

namespace CausalDirectionBracket

variable {C : Configuration S}

/-- Canonical zero bracket for commuting causal coordinates. -/
def zero :
    CausalDirectionBracket S V C where
  value := fun _ _ => 0
  skew := by
    intro d e
    simp

@[simp] theorem zero_value
    (d e : EventDirection S C) :
    (zero (S := S) (V := V) (C := C)).value d e = 0 :=
  rfl

end CausalDirectionBracket

namespace CausalGaugePotential

variable {C : Configuration S}

/-- Infinitesimal metric compatibility for a local gauge potential.

This is the linearized counterpart of exact metric preservation by a finite
transport. -/
def MetricCompatibleLocal
    (A : CausalGaugePotential K S V C)
    (g : CausalMetric K V) : Prop :=
  ∀ d x y,
    g.pair (A.operator d x) y +
      g.pair x (A.operator d y) = 0

/-- Metric compatibility says each directional operator is skew-adjoint with
respect to the causal metric. -/
theorem metric_skew
    (A : CausalGaugePotential K S V C)
    (g : CausalMetric K V)
    (hmetric : A.MetricCompatibleLocal g)
    (d : EventDirection S C)
    (x y : V) :
    g.pair (A.operator d x) y =
      - g.pair (A.operator d y) x := by
  have h := hmetric d x y
  rw [g.pair_symm x (A.operator d y)] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Torsion of a local causal gauge potential relative to a solder form and a
chosen causal direction bracket. -/
def torsion
    (A : CausalGaugePotential K S V C)
    (theta : CausalSolderForm K S V C)
    (B : CausalDirectionBracket S V C)
    (d e : EventDirection S C) : V :=
  A.operator d (theta.value e) -
    A.operator e (theta.value d) -
    B.value d e

/-- Torsion-free means the causal first structure equation vanishes on every
ordered pair of enabled directions. -/
def TorsionFree
    (A : CausalGaugePotential K S V C)
    (theta : CausalSolderForm K S V C)
    (B : CausalDirectionBracket S V C) : Prop :=
  ∀ d e, A.torsion theta B d e = 0

/-- Torsion-free condition rewritten as the connection/bracket identity. -/
theorem torsionFree_iff
    (A : CausalGaugePotential K S V C)
    (theta : CausalSolderForm K S V C)
    (B : CausalDirectionBracket S V C) :
    A.TorsionFree theta B ↔
      ∀ d e,
        A.operator d (theta.value e) -
            A.operator e (theta.value d)
          =
        B.value d e := by
  constructor
  · intro h d e
    have ht := h d e
    unfold torsion at ht
    exact sub_eq_zero.mp ht
  · intro h d e
    unfold TorsionFree torsion
    rw [h d e]
    exact sub_self _

/-- Pairing form of the torsion-free identity. -/
theorem torsion_pair
    (A : CausalGaugePotential K S V C)
    (g : CausalMetric K V)
    (theta : CausalSolderForm K S V C)
    (B : CausalDirectionBracket S V C)
    (hT : A.TorsionFree theta B)
    (d e f : EventDirection S C) :
    g.pair (A.operator d (theta.value e))
        (theta.value f)
      -
      g.pair (A.operator e (theta.value d))
        (theta.value f)
      =
    g.pair (B.value d e)
      (theta.value f) := by
  have hvec :=
    (A.torsionFree_iff theta B).1 hT d e
  have hp :=
    congrArg
      (fun x => g.pair x (theta.value f))
      hvec
  simpa [CausalMetric.pair, map_sub] using hp

end CausalGaugePotential
end CausalGeometry
