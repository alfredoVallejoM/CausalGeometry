import CausalGeometry.Calculus.CubeShift
import CausalGeometry.Calculus.GaugePotential
import CausalGeometry.Calculus.LinearConnection
import Mathlib.Tactic

namespace CausalGeometry

universe u v w x
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}
variable {K : Type w} {V : Type x}
variable [Semiring K] [AddCommGroup V] [Module K V]

/-- Exact finite/local comparison data.

Each primitive finite transport is required to be exactly I+A_e.  The local
operator field must also be stable when another concurrent event is executed.
These are explicit hypotheses; no infinitesimal-limit claim is hidden here. -/
structure FiniteLocalCurvatureComparison
    (K : Type w)
    (S : EventSystem Event Label)
    (V : Type x)
    [Semiring K] [AddCommGroup V] [Module K V] where
  finite :
    LinearCausalConnection K S V

  local :
    (C : Configuration S) →
      CausalGaugePotential K S V C

  transport_eq_id_add :
    ∀ (C : Configuration S)
      (e : Event)
      (h : S.Enabled C e),
      finite.transport C e h =
        LinearMap.id +
          (local C).operator ⟨e, h⟩

  /-- A direction f concurrent with e carries the same local operator after
  executing e. -/
  local_parallel :
    ∀ {C : Configuration S}
      {e f : Event}
      (d : ConcurrencyDiamond C e f),
      (local d.afterE).operator
          (CausalOneForm.afterE_F d) =
        (local C).operator
          (CausalOneForm.baseF d)

namespace FiniteLocalCurvatureComparison

variable
    (M : FiniteLocalCurvatureComparison K S V)

/-- The opposite transported direction is covered by the same parallel law
applied to the symmetric diamond. -/
theorem local_parallel_afterF
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    (M.local d.afterF).operator
        (CausalOneForm.afterF_E d) =
      (M.local C).operator
        (CausalOneForm.baseE d) := by
  have h := M.local_parallel d.symm
  exact h

/-- Exact comparison theorem.

Finite e-then-f minus f-then-e curvature equals the local commutator in the
reverse order [A_f,A_e]. -/
theorem finite_curvature_eq_local_reverse
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    M.finite.curvature d =
      (M.local C).curvature
        (CausalOneForm.baseF d)
        (CausalOneForm.baseE d) := by
  ext x
  unfold LinearCausalConnection.curvature
    LinearCausalConnection.transportEF
    LinearCausalConnection.transportFE
    CausalGaugePotential.curvature
    linearCommutator
  rw [
    M.transport_eq_id_add C e d.concurrent.1,
    M.transport_eq_id_add C f d.concurrent.2.1,
    M.transport_eq_id_add
      d.afterE f
      (S.concurrent_enabled_after_left
        d.concurrent),
    M.transport_eq_id_add
      d.afterF e
      (S.concurrent_enabled_after_right
        d.concurrent),
    M.local_parallel d,
    M.local_parallel_afterF d
  ]
  simp only [
    LinearMap.sub_apply,
    LinearMap.add_apply,
    LinearMap.comp_apply,
    LinearMap.id_apply
  ]
  abel

/-- Same comparison in the more familiar orientation: finite curvature is
minus [A_e,A_f]. -/
theorem finite_curvature_eq_neg_local
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    M.finite.curvature d =
      - (M.local C).curvature
          (CausalOneForm.baseE d)
          (CausalOneForm.baseF d) := by
  rw [M.finite_curvature_eq_local_reverse d]
  exact
    (M.local C).curvature_skew
      (CausalOneForm.baseF d)
      (CausalOneForm.baseE d)

/-- Local covariant commutator is additive in the transported endomorphism. -/
theorem covariantEndDerivative_neg
    {C : Configuration S}
    (A : CausalGaugePotential K S V C)
    (d : EventDirection S C)
    (T : V →ₗ[K] V) :
    A.covariantEndDerivative d (-T) =
      - A.covariantEndDerivative d T := by
  ext x
  simp [
    CausalGaugePotential.covariantEndDerivative,
    linearCommutator
  ]
  abel

/-- Finite Bianchi identity obtained by transporting the exact
finite/local-curvature comparison through the local Jacobi identity.

The three finite curvatures are those of the three oriented pair-faces of one
causal cube. -/
theorem finite_bianchi_on_cube
    {C : Configuration S}
    {ι : Type*}
    (Q : CausalCubeFrame S C ι)
    (i j k : ι)
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k) :
    let A := M.local C
    A.covariantEndDerivative
        (Q.direction i)
        (M.finite.curvature
          (Q.diamond hjk))
      +
      A.covariantEndDerivative
        (Q.direction j)
        (M.finite.curvature
          (Q.diamond hik.symm))
      +
      A.covariantEndDerivative
        (Q.direction k)
        (M.finite.curvature
          (Q.diamond hij)) =
      0 := by
  dsimp
  let A := M.local C
  have hJK :=
    M.finite_curvature_eq_neg_local
      (Q.diamond hjk)
  have hKI :=
    M.finite_curvature_eq_neg_local
      (Q.diamond hik.symm)
  have hIJ :=
    M.finite_curvature_eq_neg_local
      (Q.diamond hij)
  have hB :=
    A.bianchi
      (Q.direction i)
      (Q.direction j)
      (Q.direction k)
  rw [hJK, hKI, hIJ]
  rw [
    M.covariantEndDerivative_neg
      A (Q.direction i),
    M.covariantEndDerivative_neg
      A (Q.direction j),
    M.covariantEndDerivative_neg
      A (Q.direction k)
  ]
  have hneg := congrArg Neg.neg hB
  simpa using hneg

end FiniteLocalCurvatureComparison
end CausalGeometry
