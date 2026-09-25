import CausalGeometry.Calculus.BilinearField
import CausalGeometry.Calculus.DependentLinearConnection

namespace CausalGeometry

universe u v w x
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalBilinear

variable {K : Type w}
variable {Fiber : Configuration S → Type x}
variable [CommRing K]
variable [∀ C, AddCommGroup (Fiber C)]
variable [∀ C, Module K (Fiber C)]

variable
    (B : Field (K := K) (S := S) (Fiber := Fiber))
    (∇ : DependentLinearEquivConnection K S Fiber)

/-- Preservation predicate specialized to the underlying linear connection. -/
def PreservedByEquiv : Prop :=
  B.PreservedBy ∇.toLinearConnection

/-- If the bilinear field is preserved, flat commutes with transport.

The vector is pushed forward and its associated covector is pushed forward
using inverse vector transport. -/
theorem flat_natural
    (hpres : B.PreservedByEquiv ∇)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e)
    (x : Fiber C) :
    B.flat (S.extend C e h)
        (∇.transport C e h x) =
      ∇.covectorPushforward C e h
        (B.flat C x) := by
  ext y
  have hp :=
    hpres C e h x
      ((∇.transport C e h).symm y)
  simpa [Field.flat,
    DependentLinearEquivConnection.covectorPushforward] using hp

/-- Equivalent commuting-square formulation of flat naturality. -/
theorem flat_naturality_square
    (hpres : B.PreservedByEquiv ∇)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    (B.flat (S.extend C e h)).comp
        (∇.transport C e h).toLinearMap =
      (∇.covectorPushforward C e h).comp
        (B.flat C) := by
  ext x y
  exact LinearMap.congr_fun
    (B.flat_natural ∇ hpres C e h x) y

/-- A musical bridge converts the same preservation law into naturality of
sharp. -/
theorem sharp_natural
    {M : MusicalBridge B}
    (hpres : B.PreservedByEquiv ∇)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e)
    (ω : Module.Dual K (Fiber C)) :
    ∇.transport C e h (M.sharp C ω) =
      M.sharp (S.extend C e h)
        (∇.covectorPushforward C e h ω) := by
  apply (M.equiv (S.extend C e h)).injective
  change
    B.flat (S.extend C e h)
        (∇.transport C e h (M.sharp C ω)) =
      B.flat (S.extend C e h)
        (M.sharp (S.extend C e h)
          (∇.covectorPushforward C e h ω))
  rw [B.flat_natural ∇ hpres]
  rw [M.flat_sharp, M.flat_sharp]

/-- The sharp square also commutes as a linear-map identity. -/
theorem sharp_naturality_square
    {M : MusicalBridge B}
    (hpres : B.PreservedByEquiv ∇)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    (∇.transport C e h).toLinearMap.comp
        (M.sharp C) =
      (M.sharp (S.extend C e h)).comp
        (∇.covectorPushforward C e h) := by
  ext ω
  exact B.sharp_natural ∇ hpres C e h ω

/-- Preservation of a nondegenerate bilinear field is already enough to make
the underlying linear transport injective. -/
theorem injective_of_nondegenerate_preserved
    (hnd : B.LeftNondegenerate)
    (hpres : B.PreservedByEquiv ∇)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    Function.Injective
      (∇.transport C e h) := by
  exact B.transport_injective_of_preserved
    ∇.toLinearConnection hnd hpres C e h

end CausalBilinear
end CausalGeometry
