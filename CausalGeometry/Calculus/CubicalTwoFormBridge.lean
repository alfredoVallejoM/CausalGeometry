import CausalGeometry.Calculus.CubicalExterior
import CausalGeometry.Calculus.ExteriorOneForm
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalEventCube

/-- Reversing a diamond is exactly swapping the two coordinates of its
canonical ordered two-cube. -/
theorem ofDiamond_symm
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    ofDiamond d.symm =
      (ofDiamond d).permute
        (Equiv.swap (0 : Fin 2) (1 : Fin 2)) := by
  apply CausalEventCube.ext
  · rfl
  · funext i
    fin_cases i <;> rfl

/-- Swapping the axes of an arbitrary two-cube reverses its canonical
concurrency diamond. -/
theorem diamond01_swap
    (Q : CausalEventCube S 2) :
    (Q.permute
      (Equiv.swap (0 : Fin 2) (1 : Fin 2))).diamond01
      =
    Q.diamond01.symm := by
  rw [← ofDiamond_diamond01 Q]
  rw [← ofDiamond_symm]
  exact diamond01_ofDiamond _

end CausalEventCube

namespace CausalCubicalCochain

variable {K : Type w} [Field K]

/-- Convert an old skew causal two-form into a raw degree-two cubical
cochain by evaluating it on the canonical ordered diamond of the cube. -/
def twoFormToCubical
    (η : CausalTwoForm S K) :
    CausalCubicalCochain S K 2 :=
  fun Q => η.value Q.diamond01

/-- The cubical cochain underlying a skew two-form is alternating. -/
theorem twoFormToCubical_alternating
    (η : CausalTwoForm S K) :
    Alternating (twoFormToCubical η) := by
  intro Q i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · change
      η.value
          ((Q.permute
            (Equiv.swap (0 : Fin 2) (1 : Fin 2))).diamond01)
        =
      - η.value Q.diamond01
    rw [CausalEventCube.diamond01_swap]
    exact η.skew Q.diamond01
  ·
    have hswap :
        Equiv.swap (1 : Fin 2) (0 : Fin 2)
          =
        Equiv.swap (0 : Fin 2) (1 : Fin 2) :=
      Equiv.swap_comm _ _
    rw [hswap]
    change
      η.value
          ((Q.permute
            (Equiv.swap (0 : Fin 2) (1 : Fin 2))).diamond01)
        =
      - η.value Q.diamond01
    rw [CausalEventCube.diamond01_swap]
    exact η.skew Q.diamond01
  · exact (hij rfl).elim

/-- Every old CausalTwoForm gives a genuine exterior degree-two cubical
cochain. -/
def twoFormToExterior
    (η : CausalTwoForm S K) :
    CausalExteriorCochain
      (S := S) (K := K) 2 :=
  ⟨twoFormToCubical η,
    twoFormToCubical_alternating η⟩

/-- Recover the old skew-diamond presentation from one alternating cubical
degree-two cochain. -/
def exteriorToTwoForm
    (ω :
      CausalExteriorCochain
        (S := S) (K := K) 2) :
    CausalTwoForm S K where

  value := fun d =>
    ω.1 (CausalEventCube.ofDiamond d)

  skew := by
    intro C e f d
    rw [CausalEventCube.ofDiamond_symm]
    exact
      ω.2
        (CausalEventCube.ofDiamond d)
        (0 : Fin 2) (1 : Fin 2)
        (by decide)

/-- Round trip from legacy two-forms to exterior cubical two-forms and back. -/
theorem exteriorToTwoForm_twoFormToExterior
    (η : CausalTwoForm S K) :
    exteriorToTwoForm
        (twoFormToExterior η)
      =
    η := by
  apply CausalTwoForm.ext
  intro C e f d
  simp [exteriorToTwoForm,
    twoFormToExterior,
    twoFormToCubical]

/-- Round trip from exterior cubical two-forms to legacy two-forms and back. -/
theorem twoFormToExterior_exteriorToTwoForm
    (ω :
      CausalExteriorCochain
        (S := S) (K := K) 2) :
    twoFormToExterior
        (exteriorToTwoForm ω)
      =
    ω := by
  apply Subtype.ext
  funext Q
  change
    ω.1
        (CausalEventCube.ofDiamond Q.diamond01)
      =
    ω.1 Q
  rw [CausalEventCube.ofDiamond_diamond01]

/-- Structural equivalence between the legacy skew-diamond two-form carrier
and the new alternating cubical degree-two carrier. -/
def exteriorTwoEquiv :
    CausalExteriorCochain
        (S := S) (K := K) 2
      ≃
    CausalTwoForm S K where
  toFun := exteriorToTwoForm
  invFun := twoFormToExterior
  left_inv :=
    twoFormToExterior_exteriorToTwoForm
  right_inv :=
    exteriorToTwoForm_twoFormToExterior

end CausalCubicalCochain
end CausalGeometry
