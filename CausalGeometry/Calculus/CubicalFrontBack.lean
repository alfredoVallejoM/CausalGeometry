import CausalGeometry.Calculus.EventCube
import Mathlib.Tactic

namespace CausalGeometry

universe u v

open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalEventCube

/-- Transport one causal event cube across an equality of dimensions.

Keeping this cast explicit makes recursive front/back face constructions
independent of definitional choices in natural-number addition. -/
def castDim
    {m n : ℕ}
    (h : m = n)
    (Q : CausalEventCube S m) :
    CausalEventCube S n :=
  h ▸ Q

@[simp] theorem castDim_rfl
    {n : ℕ}
    (Q : CausalEventCube S n) :
    castDim rfl Q = Q :=
  rfl

/-- Front p-face of a (p+q)-cube.

All final q coordinates are fixed to their lower faces.  The surviving
coordinates are therefore the first p primitive-event directions, based at the
original configuration. -/
def frontFace
    (p : ℕ) :
    (q : ℕ) →
      CausalEventCube S (p + q) →
        CausalEventCube S p
  | 0, Q =>
      castDim (Nat.add_zero p) Q
  | q + 1, Q =>
      let Q' :
          CausalEventCube S ((p + q) + 1) :=
        castDim (Nat.add_succ p q) Q
      frontFace p q
        (Q'.lowerFace (Fin.last (p + q)))

/-- Back q-face of a (p+q)-cube.

All initial p coordinates are fixed to their upper faces.  Operationally this
executes the first p independent primitive events, one after another, and
retains the final q directions. -/
def backFace :
    (p q : ℕ) →
      CausalEventCube S (p + q) →
        CausalEventCube S q
  | 0, q, Q =>
      castDim (Nat.zero_add q) Q
  | p + 1, q, Q =>
      let Q' :
          CausalEventCube S ((p + q) + 1) :=
        castDim (Nat.succ_add p q) Q
      backFace p q
        (Q'.upperFace (0 : Fin ((p + q) + 1)))

@[simp] theorem frontFace_zero_zero
    (Q : CausalEventCube S 0) :
    frontFace 0 0 Q = Q := by
  rfl

@[simp] theorem backFace_zero_zero
    (Q : CausalEventCube S 0) :
    backFace 0 0 Q = Q := by
  rfl

/-- Splitting a one-cube as 0+1 retains the whole cube in the back factor. -/
@[simp] theorem backFace_zero_one
    (Q : CausalEventCube S 1) :
    backFace 0 1 Q = Q := by
  rfl

/-- Splitting a one-cube as 1+0 retains the whole cube in the front factor. -/
@[simp] theorem frontFace_one_zero
    (Q : CausalEventCube S 1) :
    frontFace 1 0 Q = Q := by
  rfl

/-- The zero-dimensional front face of a one-cube is its lower endpoint. -/
theorem frontFace_zero_one
    (Q : CausalEventCube S 1) :
    frontFace 0 1 Q =
      Q.lowerFace (0 : Fin 1) := by
  rfl

/-- The zero-dimensional back face of a one-cube is its upper endpoint. -/
theorem backFace_one_zero
    (Q : CausalEventCube S 1) :
    backFace 1 0 Q =
      Q.upperFace (0 : Fin 1) := by
  rfl

end CausalEventCube
end CausalGeometry
