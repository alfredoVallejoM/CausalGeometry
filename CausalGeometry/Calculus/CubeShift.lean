import CausalGeometry.Calculus.CubeFrame

namespace CausalGeometry

universe u v w
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}
variable {C : Configuration S} {ι : Type w}

namespace CausalCubeFrame

/-- Canonical event direction represented by one cube index. -/
def direction
    (Q : CausalCubeFrame S C ι)
    (i : ι) :
    EventDirection S C where
  event := Q.event i
  enabled := Q.enabled i

/-- Configuration obtained by executing one direction of the cube. -/
def after
    (Q : CausalCubeFrame S C ι)
    (i : ι) :
    Configuration S :=
  S.extend C (Q.event i) (Q.enabled i)

/-- After executing direction i, every other direction remains enabled and the
remaining directions still form a causal cube frame. -/
def afterFace
    (Q : CausalCubeFrame S C ι)
    (i : ι) :
    CausalCubeFrame S (Q.after i)
      {j : ι // j ≠ i} where
  event := fun j => Q.event j.1
  enabled := by
    intro j
    apply S.enabled_after_compatible
      (Q.enabled i) (Q.enabled j.1)
    · exact Q.injective.ne j.2
    · exact (Q.independent j.2.symm).2.2
  injective := by
    intro j k h
    apply Subtype.ext
    exact Q.injective h
  independent := by
    intro j k hjk
    have hval : j.1 ≠ k.1 := by
      intro h
      apply hjk
      exact Subtype.ext h
    exact Q.independent hval

@[simp] theorem after_carrier
    (Q : CausalCubeFrame S C ι)
    (i : ι) :
    (Q.after i).carrier =
      insert (Q.event i) C.carrier :=
  rfl

@[simp] theorem afterFace_event
    (Q : CausalCubeFrame S C ι)
    (i : ι)
    (j : {j : ι // j ≠ i}) :
    (Q.afterFace i).event j =
      Q.event j.1 :=
  rfl

/-- Canonical remaining direction j after executing i. -/
def directionAfter
    (Q : CausalCubeFrame S C ι)
    (i j : ι)
    (hji : j ≠ i) :
    EventDirection S (Q.after i) where
  event := Q.event j
  enabled :=
    (Q.afterFace i).enabled ⟨j, hji⟩

@[simp] theorem direction_event
    (Q : CausalCubeFrame S C ι)
    (i : ι) :
    (Q.direction i).event = Q.event i :=
  rfl

@[simp] theorem directionAfter_event
    (Q : CausalCubeFrame S C ι)
    (i j : ι)
    (hji : j ≠ i) :
    (Q.directionAfter i j hji).event =
      Q.event j :=
  rfl

/-- The remaining j,k directions after i form a genuine concurrency diamond. -/
def diamondAfter
    (Q : CausalCubeFrame S C ι)
    (i j k : ι)
    (hji : j ≠ i)
    (hki : k ≠ i)
    (hjk : j ≠ k) :
    ConcurrencyDiamond
      (Q.after i)
      (Q.event j)
      (Q.event k) :=
  (Q.afterFace i).diamond
    (i := ⟨j, hji⟩)
    (j := ⟨k, hki⟩)
    (by
      intro h
      apply hjk
      exact congrArg Subtype.val h)

/-- Executing i then j reaches the same configuration as executing j then i. -/
theorem after_after_eq_swap
    (Q : CausalCubeFrame S C ι)
    (i j : ι)
    (hij : i ≠ j) :
    (Q.diamond hij).afterEF =
      (Q.diamond hij).afterFE :=
  ConcurrencyDiamond.endpoint_eq
    (Q.diamond hij)

/-- Three pairwise distinct directions have a canonical common terminal
configuration independent of the order in which their carriers are inserted. -/
theorem triple_endpoint_eq
    (Q : CausalCubeFrame S C ι)
    (i j k : ι)
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k) :
    (Q.diamondAfter i j k
      hij.symm hik.symm hjk).afterEF =
      (Q.diamondAfter j i k
        hij hjk.symm hik).afterEF := by
  apply S.configuration_eq_of_carrier_eq
  simp [diamondAfter, afterFace, after,
    ConcurrencyDiamond.afterEF,
    ConcurrencyDiamond.afterE,
    Set.insert_comm, Set.insert_left_comm,
    Set.insert_assoc]

end CausalCubeFrame
end CausalGeometry
