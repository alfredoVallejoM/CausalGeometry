import CausalGeometry.Calculus.BilinearTransport
import CausalGeometry.Calculus.ExteriorTwoForm

namespace CausalGeometry

universe u v w x
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

/-- Explicit representation of primitive event directions inside a
configuration-dependent vector fiber.

No identification between events and vectors is built into EventSystem. -/
structure CausalSoldering
    (S : EventSystem Event Label)
    (Fiber : Configuration S → Type x) where
  vector :
    ∀ (C : Configuration S),
      EventDirection S C → Fiber C

namespace CausalSoldering

variable {K : Type w}
variable {Fiber : Configuration S → Type x}
variable [CommRing K]
variable [∀ C, AddCommGroup (Fiber C)]
variable [∀ C, Module K (Fiber C)]

/-- Soldering is preserved by a connection when every direction concurrent
with an executed event is represented after the step by the transported old
vector. -/
def PreservedBy
    (θ : CausalSoldering S Fiber)
    (∇ : DependentLinearCausalConnection K S Fiber) : Prop :=
  ∀ {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f),
      θ.vector d.afterE
          (CausalOneForm.afterE_F d) =
        ∇.transport C e d.concurrent.1
          (θ.vector C
            (CausalOneForm.baseF d))

/-- Cube-indexed form of soldering preservation. -/
theorem preserved_cube_direction
    (θ : CausalSoldering S Fiber)
    (∇ : DependentLinearCausalConnection K S Fiber)
    (hθ : θ.PreservedBy ∇)
    {C : Configuration S}
    {ι : Type*}
    (Q : CausalCubeFrame S C ι)
    (i j : ι)
    (hji : j ≠ i) :
    θ.vector (Q.after i)
        (Q.directionAfter i j hji) =
      ∇.transport C (Q.event i) (Q.enabled i)
        (θ.vector C (Q.direction j)) := by
  let d := Q.diamond hji.symm
  have h := hθ d
  have hbase :
      CausalOneForm.baseF d =
        Q.direction j := by
    apply EventDirection.ext
    rfl
  have hafter :
      CausalOneForm.afterE_F d =
        Q.directionAfter i j hji := by
    apply EventDirection.ext
    rfl
  rw [hbase, hafter] at h
  exact h

/-- Bilinear field evaluated on soldered event directions. -/
def inducedTwoForm
    (θ : CausalSoldering S Fiber)
    (B : CausalBilinear.Field
      (K := K) (S := S) (Fiber := Fiber))
    (halt : B.Alternating) :
    CausalTwoForm S K where
  value := fun {C} {e} {f} d =>
    B.form C
      (θ.vector C
        (CausalOneForm.baseE d))
      (θ.vector C
        (CausalOneForm.baseF d))
  skew := by
    intro C e f d
    have he :
        CausalOneForm.baseE d.symm =
          CausalOneForm.baseF d := by
      apply EventDirection.ext
      rfl
    have hf :
        CausalOneForm.baseF d.symm =
          CausalOneForm.baseE d := by
      apply EventDirection.ext
      rfl
    rw [he, hf]
    exact B.skew_of_alternating
      halt C
      (θ.vector C
        (CausalOneForm.baseE d))
      (θ.vector C
        (CausalOneForm.baseF d))

/-- When both the bilinear field and the soldering are parallel under the same
connection, every two-form component is constant along independent causal
directions. -/
theorem inducedTwoForm_variationAlong_eq_zero
    (θ : CausalSoldering S Fiber)
    (B : CausalBilinear.Field
      (K := K) (S := S) (Fiber := Fiber))
    (halt : B.Alternating)
    (∇ : DependentLinearCausalConnection K S Fiber)
    (hB : B.PreservedBy ∇)
    (hθ : θ.PreservedBy ∇)
    {C : Configuration S}
    {ι : Type*}
    (Q : CausalCubeFrame S C ι)
    (i j k : ι)
    (hji : j ≠ i)
    (hki : k ≠ i)
    (hjk : j ≠ k) :
    CausalTwoForm.variationAlong
        (θ.inducedTwoForm B halt)
        Q i j k hji hki hjk = 0 := by
  let dShift :=
    Q.diamondAfter i j k
      hji hki hjk
  let dBase :=
    Q.diamond hjk
  have hShiftJ :
      CausalOneForm.baseE dShift =
        Q.directionAfter i j hji := by
    apply EventDirection.ext
    rfl
  have hShiftK :
      CausalOneForm.baseF dShift =
        Q.directionAfter i k hki := by
    apply EventDirection.ext
    rfl
  have hBaseJ :
      CausalOneForm.baseE dBase =
        Q.direction j := by
    apply EventDirection.ext
    rfl
  have hBaseK :
      CausalOneForm.baseF dBase =
        Q.direction k := by
    apply EventDirection.ext
    rfl
  have hj :=
    θ.preserved_cube_direction
      ∇ hθ Q i j hji
  have hk :=
    θ.preserved_cube_direction
      ∇ hθ Q i k hki
  unfold CausalTwoForm.variationAlong
    inducedTwoForm
  rw [hShiftJ, hShiftK,
    hBaseJ, hBaseK, hj, hk]
  rw [hB C (Q.event i) (Q.enabled i)
    (θ.vector C (Q.direction j))
    (θ.vector C (Q.direction k))]
  exact sub_self _

/-- Parallel bilinear geometry plus parallel soldering is a sufficient
closedness criterion for the induced causal two-form. -/
theorem inducedTwoForm_closed
    (θ : CausalSoldering S Fiber)
    (B : CausalBilinear.Field
      (K := K) (S := S) (Fiber := Fiber))
    (halt : B.Alternating)
    (∇ : DependentLinearCausalConnection K S Fiber)
    (hB : B.PreservedBy ∇)
    (hθ : θ.PreservedBy ∇) :
    (θ.inducedTwoForm B halt).Closed := by
  intro C ι Q i j k hij hik hjk
  unfold CausalTwoForm.exteriorDerivative
  rw [
    θ.inducedTwoForm_variationAlong_eq_zero
      B halt ∇ hB hθ
      Q i j k hij.symm hik.symm hjk,
    θ.inducedTwoForm_variationAlong_eq_zero
      B halt ∇ hB hθ
      Q j i k hij hjk.symm hik,
    θ.inducedTwoForm_variationAlong_eq_zero
      B halt ∇ hB hθ
      Q k i j hik hjk hij
  ]
  simp

end CausalSoldering
end CausalGeometry
