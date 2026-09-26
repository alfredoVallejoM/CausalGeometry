import CausalGeometry.Calculus.EventCube
import Mathlib.Data.Fin.SuccPred
import Mathlib.Tactic

namespace CausalGeometry

universe u v

open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

/-- Two causal cube frames over the same base are equal as soon as their
primitive-event coordinate maps agree.  All remaining fields are proof data. -/
theorem CausalCubeFrame.ext_event
    {C : Configuration S}
    {ι : Type*}
    {Q R : CausalCubeFrame S C ι}
    (h : Q.event = R.event) :
    Q = R := by
  cases Q with
  | mk qEvent qEnabled qInjective qIndependent =>
      cases R with
      | mk rEvent rEnabled rInjective rIndependent =>
          dsimp at h
          cases h
          rfl

namespace CausalEventCube

/-- Extensionality for concrete causal cubes: the base configuration and the
ordered surviving primitive-event coordinates determine the entire cube. -/
theorem ext
    {n : ℕ}
    {Q R : CausalEventCube S n}
    (hbase : Q.base = R.base)
    (hevent : Q.frame.event = R.frame.event) :
    Q = R := by
  rcases Q with ⟨C, Q⟩
  rcases R with ⟨D, R⟩
  dsimp [base, frame] at hbase hevent
  cases hbase
  have hframe : Q = R :=
    CausalCubeFrame.ext_event hevent
  cases hframe
  rfl

/-- Coordinate identity for the axis that is executed/deleted second after
swapping two face operations.

If i is removed first and j is the next coordinate in the remaining cube,
then q=i.succAbove j is the corresponding original coordinate.  Removing q
first makes j.predAbove i the new coordinate of i. -/
theorem swapped_removed_axis
    {n : ℕ}
    (i : Fin (n + 2))
    (j : Fin (n + 1)) :
    (i.succAbove j).succAbove
        (j.predAbove i)
      =
    i :=
  Fin.succAbove_succAbove_predAbove i j

/-- Coordinate identity for every axis that survives two face operations. -/
theorem swapped_surviving_axis
    {n : ℕ}
    (i : Fin (n + 2))
    (j : Fin (n + 1))
    (k : Fin n) :
    (i.succAbove j).succAbove
        ((j.predAbove i).succAbove k)
      =
    i.succAbove (j.succAbove k) :=
  Fin.succAbove_succAbove_succAbove_predAbove
    i j k

/-- Lower/lower cubical face relation in arbitrary dimension. -/
theorem lowerFace_lowerFace
    {n : ℕ}
    (Q : CausalEventCube S (n + 2))
    (i : Fin (n + 2))
    (j : Fin (n + 1)) :
    (Q.lowerFace i).lowerFace j =
      (Q.lowerFace (i.succAbove j)).lowerFace
        (j.predAbove i) := by
  apply CausalEventCube.ext
  · rfl
  · funext k
    change
      Q.frame.event
          (i.succAbove (j.succAbove k))
        =
      Q.frame.event
          ((i.succAbove j).succAbove
            ((j.predAbove i).succAbove k))
    rw [swapped_surviving_axis i j k]

/-- Upper/lower cubical face relation.

Executing i and then deleting the surviving j-axis agrees with first deleting
the corresponding original q=i.succAbove j axis and then executing i in its
reindexed position. -/
theorem upperFace_lowerFace
    {n : ℕ}
    (Q : CausalEventCube S (n + 2))
    (i : Fin (n + 2))
    (j : Fin (n + 1)) :
    (Q.upperFace i).lowerFace j =
      (Q.lowerFace (i.succAbove j)).upperFace
        (j.predAbove i) := by
  apply CausalEventCube.ext
  · apply S.configuration_eq_of_carrier_eq
    change
      insert (Q.frame.event i) Q.base.carrier =
        insert
          (Q.frame.event
            ((i.succAbove j).succAbove
              (j.predAbove i)))
          Q.base.carrier
    rw [swapped_removed_axis i j]
  · funext k
    change
      Q.frame.event
          (i.succAbove (j.succAbove k))
        =
      Q.frame.event
          ((i.succAbove j).succAbove
            ((j.predAbove i).succAbove k))
    rw [swapped_surviving_axis i j k]

/-- Lower/upper cubical face relation. -/
theorem lowerFace_upperFace
    {n : ℕ}
    (Q : CausalEventCube S (n + 2))
    (i : Fin (n + 2))
    (j : Fin (n + 1)) :
    (Q.lowerFace i).upperFace j =
      (Q.upperFace (i.succAbove j)).lowerFace
        (j.predAbove i) := by
  apply CausalEventCube.ext
  · rfl
  · funext k
    change
      Q.frame.event
          (i.succAbove (j.succAbove k))
        =
      Q.frame.event
          ((i.succAbove j).succAbove
            ((j.predAbove i).succAbove k))
    rw [swapped_surviving_axis i j k]

/-- Upper/upper cubical face relation.

The base equality is the arbitrary-dimensional version of the concurrency
diamond endpoint law: executing two pairwise-independent primitive events in
either order produces the same derived configuration. -/
theorem upperFace_upperFace
    {n : ℕ}
    (Q : CausalEventCube S (n + 2))
    (i : Fin (n + 2))
    (j : Fin (n + 1)) :
    (Q.upperFace i).upperFace j =
      (Q.upperFace (i.succAbove j)).upperFace
        (j.predAbove i) := by
  apply CausalEventCube.ext
  · apply S.configuration_eq_of_carrier_eq
    change
      insert
          (Q.frame.event (i.succAbove j))
          (insert (Q.frame.event i)
            Q.base.carrier)
        =
      insert
          (Q.frame.event
            ((i.succAbove j).succAbove
              (j.predAbove i)))
          (insert (Q.frame.event
            (i.succAbove j))
            Q.base.carrier)
    rw [swapped_removed_axis i j]
    exact Set.insert_comm _ _ _
  · funext k
    change
      Q.frame.event
          (i.succAbove (j.succAbove k))
        =
      Q.frame.event
          ((i.succAbove j).succAbove
            ((j.predAbove i).succAbove k))
    rw [swapped_surviving_axis i j k]

/-- All four cubical face combinations satisfy one uniform exchange law.

The boolean parameter records lower=false / upper=true. -/
def face
    {n : ℕ}
    (Q : CausalEventCube S (n + 1))
    (upper : Bool)
    (i : Fin (n + 1)) :
    CausalEventCube S n :=
  if upper then Q.upperFace i
  else Q.lowerFace i

theorem face_face
    {n : ℕ}
    (Q : CausalEventCube S (n + 2))
    (ε η : Bool)
    (i : Fin (n + 2))
    (j : Fin (n + 1)) :
    (Q.face ε i).face η j =
      (Q.face η (i.succAbove j)).face ε
        (j.predAbove i) := by
  cases ε <;> cases η
  · exact lowerFace_lowerFace Q i j
  · exact lowerFace_upperFace Q i j
  · exact upperFace_lowerFace Q i j
  · exact upperFace_upperFace Q i j

end CausalEventCube
end CausalGeometry
