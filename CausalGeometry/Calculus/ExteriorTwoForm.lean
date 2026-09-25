import CausalGeometry.Calculus.CubeShift
import CausalGeometry.Calculus.ExteriorOneForm
import Mathlib.Tactic

namespace CausalGeometry

universe u v w
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalTwoForm

variable {K : Type w} [AddCommGroup K]

/-- Variation of a two-form component omega(j,k) along a third direction i. -/
def variationAlong
    (ω : CausalTwoForm S K)
    {C : Configuration S}
    {ι : Type*}
    (Q : CausalCubeFrame S C ι)
    (i j k : ι)
    (hji : j ≠ i)
    (hki : k ≠ i)
    (hjk : j ≠ k) : K :=
  ω.value
      (Q.diamondAfter i j k
        hji hki hjk) -
    ω.value (Q.diamond hjk)

/-- Discrete exterior derivative of a causal two-form on an oriented triple.

The signs follow the ordinary formula
  dω(i,j,k)=Δ_i ω(j,k)-Δ_j ω(i,k)+Δ_k ω(i,j).
-/
def exteriorDerivative
    (ω : CausalTwoForm S K)
    {C : Configuration S}
    {ι : Type*}
    (Q : CausalCubeFrame S C ι)
    (i j k : ι)
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k) : K :=
  variationAlong ω Q
      i j k hij.symm hik.symm hjk -
    variationAlong ω Q
      j i k hij hjk.symm hik +
    variationAlong ω Q
      k i j hik hjk hij

/-- Closedness is a separate property of a causal two-form. -/
def Closed
    (ω : CausalTwoForm S K) : Prop :=
  ∀ {C : Configuration S}
    {ι : Type*}
    (Q : CausalCubeFrame S C ι)
    (i j k : ι)
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k),
      exteriorDerivative ω Q
        i j k hij hik hjk = 0

/-- Zero causal two-form. -/
def zero :
    CausalTwoForm S K where
  value := fun _ => 0
  skew := by
    intro C e f d
    simp

@[simp] theorem zero_value
    {C : Configuration S}
    {e f : Event}
    (d : ConcurrencyDiamond C e f) :
    (zero (S := S) (K := K)).value d = 0 :=
  rfl

theorem zero_closed :
    (zero (S := S) (K := K)).Closed := by
  intro C ι Q i j k hij hik hjk
  simp [Closed, exteriorDerivative,
    variationAlong]

/-- Pointwise sum of causal two-forms. -/
def add
    (ω η : CausalTwoForm S K) :
    CausalTwoForm S K where
  value := fun d =>
    ω.value d + η.value d
  skew := by
    intro C e f d
    rw [ω.skew d, η.skew d]
    abel

/-- Pointwise negation. -/
def neg
    (ω : CausalTwoForm S K) :
    CausalTwoForm S K where
  value := fun d =>
    - ω.value d
  skew := by
    intro C e f d
    rw [ω.skew d]
    simp

@[simp] theorem variationAlong_add
    (ω η : CausalTwoForm S K)
    {C : Configuration S}
    {ι : Type*}
    (Q : CausalCubeFrame S C ι)
    (i j k : ι)
    (hji : j ≠ i)
    (hki : k ≠ i)
    (hjk : j ≠ k) :
    variationAlong (add ω η) Q
        i j k hji hki hjk =
      variationAlong ω Q
          i j k hji hki hjk +
        variationAlong η Q
          i j k hji hki hjk := by
  unfold variationAlong add
  abel

@[simp] theorem exteriorDerivative_add
    (ω η : CausalTwoForm S K)
    {C : Configuration S}
    {ι : Type*}
    (Q : CausalCubeFrame S C ι)
    (i j k : ι)
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k) :
    exteriorDerivative (add ω η) Q
        i j k hij hik hjk =
      exteriorDerivative ω Q
          i j k hij hik hjk +
        exteriorDerivative η Q
          i j k hij hik hjk := by
  unfold exteriorDerivative
  simp only [variationAlong_add]
  abel

theorem add_closed
    {ω η : CausalTwoForm S K}
    (hω : ω.Closed)
    (hη : η.Closed) :
    (add ω η).Closed := by
  intro C ι Q i j k hij hik hjk
  rw [exteriorDerivative_add]
  rw [hω Q i j k hij hik hjk,
    hη Q i j k hij hik hjk]
  simp

@[simp] theorem variationAlong_neg
    (ω : CausalTwoForm S K)
    {C : Configuration S}
    {ι : Type*}
    (Q : CausalCubeFrame S C ι)
    (i j k : ι)
    (hji : j ≠ i)
    (hki : k ≠ i)
    (hjk : j ≠ k) :
    variationAlong (neg ω) Q
        i j k hji hki hjk =
      - variationAlong ω Q
          i j k hji hki hjk := by
  unfold variationAlong neg
  abel

@[simp] theorem exteriorDerivative_neg
    (ω : CausalTwoForm S K)
    {C : Configuration S}
    {ι : Type*}
    (Q : CausalCubeFrame S C ι)
    (i j k : ι)
    (hij : i ≠ j)
    (hik : i ≠ k)
    (hjk : j ≠ k) :
    exteriorDerivative (neg ω) Q
        i j k hij hik hjk =
      - exteriorDerivative ω Q
          i j k hij hik hjk := by
  unfold exteriorDerivative
  simp only [variationAlong_neg]
  abel

theorem neg_closed
    {ω : CausalTwoForm S K}
    (hω : ω.Closed) :
    (neg ω).Closed := by
  intro C ι Q i j k hij hik hjk
  rw [exteriorDerivative_neg,
    hω Q i j k hij hik hjk]
  simp

end CausalTwoForm
end CausalGeometry
