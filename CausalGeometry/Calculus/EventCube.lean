import CausalGeometry.Calculus.CubeShift
import Mathlib.Data.Fin.Embedding
import Mathlib.Tactic

namespace CausalGeometry

universe u v

open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

/-- A concrete n-dimensional causal event cube is a derived configuration
equipped with n pairwise concurrent primitive event directions.

This is a geometric carrier.  It contains no coefficient ring and no
cohomology data. -/
abbrev CausalEventCube
    (S : EventSystem Event Label)
    (n : ℕ) :=
  Σ C : Configuration S,
    CausalCubeFrame S C (Fin n)

namespace CausalEventCube

/-- The unique empty-direction frame over a chosen configuration. -/
def emptyFrame
    (C : Configuration S) :
    CausalCubeFrame S C (Fin 0) where
  event := fun i => Fin.elim0 i
  enabled := fun i => Fin.elim0 i
  injective := by
    intro i
    exact Fin.elim0 i
  independent := by
    intro i
    exact Fin.elim0 i

/-- Every configuration determines a canonical zero-dimensional causal cube. -/
def zeroCube
    (C : Configuration S) :
    CausalEventCube S 0 :=
  ⟨C, emptyFrame C⟩

def base
    {n : ℕ}
    (Q : CausalEventCube S n) :
    Configuration S :=
  Q.1

def frame
    {n : ℕ}
    (Q : CausalEventCube S n) :
    CausalCubeFrame S Q.base (Fin n) :=
  Q.2

@[simp] theorem zeroCube_base
    (C : Configuration S) :
    (zeroCube C).base = C :=
  rfl


/-- One enabled primitive event determines a canonical one-dimensional causal
cube. -/
def oneCube
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    CausalEventCube S 1 :=
  ⟨C,
    { event := fun _ => e
      enabled := fun _ => h
      injective := by
        intro i j hij
        exact Subsingleton.elim i j
      independent := by
        intro i j hij
        exact False.elim
          (hij (Subsingleton.elim i j)) }⟩

@[simp] theorem oneCube_base
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    (oneCube C e h).base = C :=
  rfl

@[simp] theorem oneCube_event_zero
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    (oneCube C e h).frame.event 0 = e :=
  rfl

/-- Delete one direction without executing it: the lower cubical face. -/
def lowerFace
    {n : ℕ}
    (Q : CausalEventCube S (n + 1))
    (i : Fin (n + 1)) :
    CausalEventCube S n :=
  ⟨Q.base,
    Q.frame.reindex
      i.succAbove
      i.succAbove_right_injective⟩

/-- Delete one direction after executing it: the upper cubical face.

The remaining directions are still pairwise concurrent because they are
obtained from the canonical afterFace frame. -/
def upperFace
    {n : ℕ}
    (Q : CausalEventCube S (n + 1))
    (i : Fin (n + 1)) :
    CausalEventCube S n :=
  ⟨Q.frame.after i,
    (Q.frame.afterFace i).reindex
      (fun j : Fin n =>
        ⟨i.succAbove j,
          i.succAbove_ne j⟩)
      (by
        intro j k h
        apply i.succAbove_right_injective
        exact congrArg Subtype.val h)⟩

@[simp] theorem lowerFace_base
    {n : ℕ}
    (Q : CausalEventCube S (n + 1))
    (i : Fin (n + 1)) :
    (Q.lowerFace i).base = Q.base :=
  rfl

@[simp] theorem upperFace_base
    {n : ℕ}
    (Q : CausalEventCube S (n + 1))
    (i : Fin (n + 1)) :
    (Q.upperFace i).base =
      Q.frame.after i :=
  rfl

@[simp] theorem lowerFace_event
    {n : ℕ}
    (Q : CausalEventCube S (n + 1))
    (i : Fin (n + 1))
    (j : Fin n) :
    (Q.lowerFace i).frame.event j =
      Q.frame.event (i.succAbove j) :=
  rfl

@[simp] theorem upperFace_event
    {n : ℕ}
    (Q : CausalEventCube S (n + 1))
    (i : Fin (n + 1))
    (j : Fin n) :
    (Q.upperFace i).frame.event j =
      Q.frame.event (i.succAbove j) :=
  rfl

/-- Lower and upper faces retain the same ordered list of surviving primitive
event labels; they differ only in the base configuration. -/
theorem face_events_agree
    {n : ℕ}
    (Q : CausalEventCube S (n + 1))
    (i : Fin (n + 1)) :
    (Q.lowerFace i).frame.event =
      (Q.upperFace i).frame.event := by
  funext j
  rfl


/-- In a causal square, the surviving direction of the lower zero-face reaches
the same one-step configuration as the upper one-face base. -/
theorem twoCube_lowerZero_after_eq_upperOne
    (Q : CausalEventCube S 2) :
    (Q.lowerFace (0 : Fin 2)).frame.after (0 : Fin 1) =
      (Q.upperFace (1 : Fin 2)).base := by
  apply S.configuration_eq_of_carrier_eq
  simp [lowerFace, upperFace, frame, base,
    CausalCubeFrame.reindex,
    CausalCubeFrame.after]

/-- Symmetric one-step face identity. -/
theorem twoCube_lowerOne_after_eq_upperZero
    (Q : CausalEventCube S 2) :
    (Q.lowerFace (1 : Fin 2)).frame.after (0 : Fin 1) =
      (Q.upperFace (0 : Fin 2)).base := by
  apply S.configuration_eq_of_carrier_eq
  simp [lowerFace, upperFace, frame, base,
    CausalCubeFrame.reindex,
    CausalCubeFrame.after]

/-- Executing the two directions of a causal square in either order gives the
same terminal configuration.  This is the two-dimensional upper-face identity
needed by the first d² regression. -/
theorem twoCube_upperUpper_endpoint
    (Q : CausalEventCube S 2) :
    (Q.upperFace (0 : Fin 2)).frame.after (0 : Fin 1) =
      (Q.upperFace (1 : Fin 2)).frame.after (0 : Fin 1) := by
  apply S.configuration_eq_of_carrier_eq
  simp [upperFace, frame, base,
    CausalCubeFrame.reindex,
    CausalCubeFrame.after,
    CausalCubeFrame.afterFace,
    Set.insert_comm]

end CausalEventCube
end CausalGeometry
