import CausalGeometry.Calculus.CubicalShuffleCup
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalCubicalCochain

variable {K : Type w} [Field K]

/-- A raw cubical cochain is alternating when every transposition of two
distinct event axes reverses its sign.

This definition is independent of a global permutation-sign API and is enough
to characterize ordinary alternating behavior because transpositions generate
the finite symmetric group. -/
def Alternating
    {n : ℕ}
    (ω : CausalCubicalCochain S K n) : Prop :=
  ∀ (Q : CausalEventCube S n)
    (i j : Fin n),
      i ≠ j →
        ω (Q.permute (Equiv.swap i j)) =
          - ω Q

/-- Alternating degree-n causal cubical cochains form a linear subspace of the
raw cubical cochains. -/
def alternatingSubmodule
    (n : ℕ) :
    Submodule K
      (CausalCubicalCochain S K n) where
  carrier :=
    {ω | Alternating ω}
  zero_mem' := by
    intro Q i j hij
    simp
  add_mem' := by
    intro α β hα hβ
    intro Q i j hij
    simp only [Pi.add_apply]
    rw [hα Q i j hij, hβ Q i j hij]
    simp
  smul_mem' := by
    intro a α hα
    intro Q i j hij
    simp only [Pi.smul_apply]
    rw [hα Q i j hij]
    simp

/-- Genuine exterior causal cochains are alternating raw cubical cochains. -/
abbrev CausalExteriorCochain
    (n : ℕ) :=
  alternatingSubmodule
    (S := S) (K := K) n

/-- Degree zero alternation is vacuous. -/
theorem alternating_zero
    (ω : CausalCubicalCochain S K 0) :
    Alternating ω := by
  intro Q i
  exact Fin.elim0 i

/-- Degree one alternation is also vacuous because there are no two distinct
axes.  Hence the exterior degree-one carrier agrees with the raw cubical
degree-one carrier. -/
theorem alternating_one
    (ω : CausalCubicalCochain S K 1) :
    Alternating ω := by
  intro Q i j hij
  exact
    (hij (Subsingleton.elim i j)).elim

/-- Canonical embedding of any raw degree-zero cochain into the exterior
subspace. -/
def toExteriorZero
    (ω : CausalCubicalCochain S K 0) :
    CausalExteriorCochain
      (S := S) (K := K) 0 :=
  ⟨ω, alternating_zero ω⟩

/-- Canonical embedding of any raw degree-one cochain into the exterior
subspace. -/
def toExteriorOne
    (ω : CausalCubicalCochain S K 1) :
    CausalExteriorCochain
      (S := S) (K := K) 1 :=
  ⟨ω, alternating_one ω⟩

/-- Exterior degree one is linearly equivalent to raw cubical degree one. -/
def exteriorOneLinearEquiv :
    CausalExteriorCochain
        (S := S) (K := K) 1
      ≃ₗ[K]
    CausalCubicalCochain S K 1 where
  toFun := fun ω => ω.1
  invFun := toExteriorOne
  left_inv := by
    intro ω
    apply Subtype.ext
    rfl
  right_inv := by
    intro ω
    rfl
  map_add' := by
    intro α β
    rfl
  map_smul' := by
    intro a α
    rfl

/-- Through the existing degree-one cubical equivalence, every old
CausalOneForm is canonically an exterior degree-one cubical cochain. -/
def oneFormToExterior
    (ω : CausalOneForm S K) :
    CausalExteriorCochain
      (S := S) (K := K) 1 :=
  toExteriorOne
    (degreeOneLinearEquiv
      (S := S) (K := K) ω)

end CausalCubicalCochain
end CausalGeometry
