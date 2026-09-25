import CausalGeometry.Calculus.FormEquivariance
import CausalGeometry.Calculus.HamiltonianEventEquation
import CausalGeometry.Calculus.SymplecticGeometry

namespace CausalGeometry

universe u₁ v₁ u₂ v₂ w x

open EventSystem

variable
    {Event₁ : Type u₁} {Label₁ : Type v₁}
    {Event₂ : Type u₂} {Label₂ : Type v₂}
    {S₁ : EventSystem Event₁ Label₁}
    {S₂ : EventSystem Event₂ Label₂}

namespace EventSystemEquiv

variable (E : EventSystemEquiv S₁ S₂)

/-- Pull a configuration-dependent fiber family back along a causal-system
isomorphism. -/
abbrev pullFiber
    (Fiber : Configuration S₂ → Type x) :
    Configuration S₁ → Type x :=
  fun C => Fiber (E.mapConfiguration C)

variable {K : Type w}
variable {Fiber : Configuration S₂ → Type x}
variable [CommRing K]
variable [∀ C, AddCommGroup (Fiber C)]
variable [∀ C, Module K (Fiber C)]

/-- Pull back a bilinear field to the reindexed causal system. -/
def pullBilinearField
    (B : CausalBilinear.Field
      (K := K) (S := S₂) (Fiber := Fiber)) :
    CausalBilinear.Field
      (K := K) (S := S₁)
      (Fiber := E.pullFiber Fiber) where
  form := fun C =>
    B.form (E.mapConfiguration C)

/-- Alternation is invariant under event-system reindexing. -/
theorem pullBilinearField_alternating
    {B : CausalBilinear.Field
      (K := K) (S := S₂) (Fiber := Fiber)}
    (h : B.Alternating) :
    (E.pullBilinearField B).Alternating := by
  intro C x
  exact h (E.mapConfiguration C) x

/-- Left nondegeneracy is invariant too. -/
theorem pullBilinearField_nondegenerate
    {B : CausalBilinear.Field
      (K := K) (S := S₂) (Fiber := Fiber)}
    (h : B.LeftNondegenerate) :
    (E.pullBilinearField B)
      .LeftNondegenerate := by
  intro C x hx
  exact h (E.mapConfiguration C) x hx

/-- Pull back an algebraic symplectic field. -/
def pullSymplecticField
    (B : CausalBilinear.SymplecticField
      (K := K) (S := S₂) (Fiber := Fiber)) :
    CausalBilinear.SymplecticField
      (K := K) (S := S₁)
      (Fiber := E.pullFiber Fiber) where
  toField :=
    E.pullBilinearField B.toField
  alternating :=
    E.pullBilinearField_alternating
      B.alternating
  nondegenerate :=
    E.pullBilinearField_nondegenerate
      B.nondegenerate

/-- Pull back the explicit event-to-vector soldering. -/
def pullSoldering
    (θ : CausalSoldering S₂ Fiber) :
    CausalSoldering S₁
      (E.pullFiber Fiber) where
  vector := fun C d =>
    θ.vector
      (E.mapConfiguration C)
      (E.directionEquiv C d)

@[simp] theorem pullSoldering_vector
    (θ : CausalSoldering S₂ Fiber)
    (C : Configuration S₁)
    (d : EventDirection S₁ C) :
    (E.pullSoldering θ).vector C d =
      θ.vector
        (E.mapConfiguration C)
        (E.directionEquiv C d) :=
  rfl

/-- The scalar event two-form induced from pulled bilinear/soldering data is
exactly the causal two-form pullback. -/
theorem inducedTwoForm_pull
    (θ : CausalSoldering S₂ Fiber)
    (B : CausalBilinear.Field
      (K := K) (S := S₂) (Fiber := Fiber))
    (halt : B.Alternating) :
    (E.pullSoldering θ).inducedTwoForm
        (E.pullBilinearField B)
        (E.pullBilinearField_alternating halt)
      =
    E.pullTwoForm
      (θ.inducedTwoForm B halt) := by
  apply CausalTwoForm.ext
  intro C e f d
  unfold
    CausalSoldering.inducedTwoForm
    pullSoldering
    pullBilinearField
    pullTwoForm
  rw [
    E.directionEquiv_baseE d,
    E.directionEquiv_baseF d
  ]

/-- Pullback of a closed causal symplectic geometry is again a closed causal
symplectic geometry. -/
def pullSymplecticGeometry
    (G : CausalSymplecticGeometry
      K S₂ Fiber) :
    CausalSymplecticGeometry
      K S₁ (E.pullFiber Fiber) where
  symplectic :=
    E.pullSymplecticField G.symplectic

  soldering :=
    E.pullSoldering G.soldering

  closed := by
    have hclosed :=
      E.pullTwoForm_closed G.closed
    rw [E.inducedTwoForm_pull
      G.soldering
      G.symplectic.toField
      G.symplectic.alternating]
    exact hclosed

@[simp] theorem pullSymplecticGeometry_eventTwoForm
    (G : CausalSymplecticGeometry
      K S₂ Fiber) :
    (E.pullSymplecticGeometry G).eventTwoForm =
      E.pullTwoForm G.eventTwoForm := by
  exact
    E.inducedTwoForm_pull
      G.soldering
      G.symplectic.toField
      G.symplectic.alternating

/-- Pull a Hamiltonian pair back along the causal-system isomorphism. -/
def pullHamiltonianPair
    {B : CausalBilinear.Field
      (K := K) (S := S₂) (Fiber := Fiber)}
    (H : CausalHamiltonian.Pair B) :
    CausalHamiltonian.Pair
      (E.pullBilinearField B) where
  vector := fun C =>
    H.vector (E.mapConfiguration C)

  covector := fun C =>
    H.covector (E.mapConfiguration C)

  hamiltonian := by
    intro C
    exact H.hamiltonian
      (E.mapConfiguration C)

/-- Hamiltonian contraction one-forms are pullback-natural. -/
theorem contractionOneForm_pull
    {B : CausalBilinear.Field
      (K := K) (S := S₂) (Fiber := Fiber)}
    (H : CausalHamiltonian.Pair B)
    (θ : CausalSoldering S₂ Fiber) :
    CausalHamiltonian.contractionOneForm
        (E.pullBilinearField B)
        (E.pullSoldering θ)
        (E.pullHamiltonianPair H).vector
      =
    E.pullOneForm
      (CausalHamiltonian.contractionOneForm
        B θ H.vector) := by
  apply CausalOneForm.ext
  intro C d
  rfl

/-- Pull back a Hamiltonian potential pair.  Naturality of the causal finite
difference supplies the directional differential law. -/
def pullHamiltonianPotentialPair
    {B : CausalBilinear.Field
      (K := K) (S := S₂) (Fiber := Fiber)}
    {θ : CausalSoldering S₂ Fiber}
    (H : CausalHamiltonian.PotentialPair B θ) :
    CausalHamiltonian.PotentialPair
      (E.pullBilinearField B)
      (E.pullSoldering θ) where
  toPair :=
    E.pullHamiltonianPair H.toPair

  potential :=
    E.pullObservable H.potential

  differential_on_directions := by
    intro C d
    have hH :=
      H.differential_on_directions
        (E.mapConfiguration C)
        (E.directionEquiv C d)
    exact hH.trans
      (E.causalDifference_natural
        H.potential C
        d.event d.enabled)

/-- Event-level Hamilton equations are therefore representation invariant. -/
theorem eventHamiltonEquation_pull
    {B : CausalBilinear.Field
      (K := K) (S := S₂) (Fiber := Fiber)}
    {θ : CausalSoldering S₂ Fiber}
    (H : CausalHamiltonian.PotentialPair B θ)
    (C : Configuration S₁)
    (d : EventDirection S₁ C) :
    (E.pullBilinearField B).form C
        ((E.pullHamiltonianPotentialPair H)
          .toPair.vector C)
        ((E.pullSoldering θ).vector C d)
      =
    causalDifference
      (E.pullObservable H.potential)
      C d.event d.enabled :=
  (E.pullHamiltonianPotentialPair H)
    .eventHamiltonEquation C d

end EventSystemEquiv
end CausalGeometry
