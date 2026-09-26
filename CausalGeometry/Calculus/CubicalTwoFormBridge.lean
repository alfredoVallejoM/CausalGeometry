import CausalGeometry.Calculus.CubicalExterior
import CausalGeometry.Calculus.ExteriorOneForm
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalCubeFrame

/-- Two cube frames over the same base are equal once their ordered event
families agree.  All remaining fields are propositions/proof witnesses. -/
theorem ext_event
    {C : Configuration S}
    {ι : Type*}
    {F G : CausalCubeFrame S C ι}
    (h : F.event = G.event) :
    F = G := by
  cases F with
  | mk event enabled injective independent =>
      cases G with
      | mk event' enabled' injective' independent' =>
          dsimp at h
          subst event'
          rfl

end CausalCubeFrame

namespace CausalEventCube

/-- Canonical ordered two-cube attached to one concurrency diamond. -/
def ofDiamond
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    CausalEventCube S 2 :=
  ⟨C,
    { event := fun i =>
        Fin.cases e
          (fun _ : Fin 1 => f) i

      enabled := fun i =>
        Fin.cases d.concurrent.1
          (fun _ : Fin 1 =>
            d.concurrent.2.1) i

      injective := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exfalso
          exact
            d.concurrent.2.2.2.2.2 hij
        · exfalso
          exact
            d.concurrent.2.2.2.2.2 hij.symm
        · rfl

      independent := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · exact (hij rfl).elim
        · exact
            ⟨d.concurrent.2.2.1,
              d.concurrent.2.2.2.1,
              d.concurrent.2.2.2.2.1⟩
        · exact
            ⟨d.concurrent.2.2.2.1,
              d.concurrent.2.2.1,
              fun hconf =>
                d.concurrent.2.2.2.2.1
                  (S.conflict_symm hconf)⟩
        · exact (hij rfl).elim }⟩

/-- Canonical oriented concurrency diamond read from a two-cube. -/
def toDiamond
    (Q : CausalEventCube S 2) :
    ConcurrencyDiamond
      Q.base
      (Q.frame.event (0 : Fin 2))
      (Q.frame.event (1 : Fin 2)) :=
  Q.frame.diamond (by decide)

@[simp] theorem toDiamond_ofDiamond
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    (ofDiamond d).toDiamond = d := by
  cases d
  rfl

/-- Every ordered two-cube is recovered from its canonical diamond. -/
@[simp] theorem ofDiamond_toDiamond
    (Q : CausalEventCube S 2) :
    ofDiamond Q.toDiamond = Q := by
  apply Sigma.ext
  · rfl
  · apply CausalCubeFrame.ext_event
    funext i
    fin_cases i <;> rfl

/-- Reversing a diamond is exactly swapping the two cubical axes. -/
theorem ofDiamond_symm
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    ofDiamond d.symm =
      (ofDiamond d).permute
        (Equiv.swap (0 : Fin 2) (1 : Fin 2)) := by
  apply Sigma.ext
  · rfl
  · apply CausalCubeFrame.ext_event
    funext i
    fin_cases i <;> rfl

/-- Swapping the axes of an arbitrary two-cube reverses its canonical
concurrency diamond. -/
theorem toDiamond_swap
    (Q : CausalEventCube S 2) :
    (Q.permute
      (Equiv.swap (0 : Fin 2) (1 : Fin 2))).toDiamond
      =
    Q.toDiamond.symm := by
  rw [← ofDiamond_toDiamond Q]
  rw [← ofDiamond_symm]
  exact toDiamond_ofDiamond _

end CausalEventCube

namespace CausalCubicalCochain

variable {K : Type w} [Field K]

/-- Convert an old skew causal two-form into a raw degree-two cubical cochain. -/
def twoFormToCubical
    (η : CausalTwoForm S K) :
    CausalCubicalCochain S K 2 :=
  fun Q => η.value Q.toDiamond

/-- The cubical cochain underlying a skew two-form is alternating. -/
theorem twoFormToCubical_alternating
    (η : CausalTwoForm S K) :
    Alternating (twoFormToCubical η) := by
  intro Q i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · rw [twoFormToCubical]
    rw [CausalEventCube.toDiamond_swap]
    exact η.skew Q.toDiamond
  ·
    have hswap :
        Equiv.swap (1 : Fin 2) (0 : Fin 2)
          =
        Equiv.swap (0 : Fin 2) (1 : Fin 2) := by
      exact Equiv.swap_comm _ _
    rw [hswap]
    rw [twoFormToCubical]
    rw [CausalEventCube.toDiamond_swap]
    exact η.skew Q.toDiamond
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

/-- The two presentations contain exactly the same data. -/
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
  simp [twoFormToExterior,
    exteriorToTwoForm,
    twoFormToCubical]

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
