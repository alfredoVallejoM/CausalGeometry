import CausalGeometry.Calculus.PairedCochainTransport
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

namespace GradedLinearTransport

variable
    {K : Type u}
    {C : ℕ → Type v}
    {D : ℕ → Type w}
    [Field K]
    [∀ n, AddCommGroup (C n)]
    [∀ n, Module K (C n)]
    [∀ n, AddCommGroup (D n)]
    [∀ n, Module K (D n)]
    {A : GradedCausalCochainComplex K C}
    {B : GradedCausalCochainComplex K D}
    (F : GradedLinearTransport A B)

/-- A genuine cochain map sends closed positive-degree cochains to closed
cochains. -/
def closedMapSucc
    (hF : F.Natural)
    (n : ℕ) :
    A.Closed (n + 1) →ₗ[K]
      B.Closed (n + 1) where
  toFun := fun x =>
    ⟨F.map (n + 1) x, by
      change
        B.d (n + 1)
          (F.map (n + 1) x) = 0
      rw [GradedLinearTransport.map_d
        hF (n + 1) x]
      rw [x.2]
      simp⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    simp
  map_smul' := by
    intro a x
    apply Subtype.ext
    simp

/-- A genuine cochain map sends exact positive-degree cochains to exact
cochains.  This is the exact condition needed to descend to cohomology. -/
theorem exactInClosedSucc_le_comap
    (hF : F.Natural)
    (n : ℕ) :
    A.ExactInClosedSucc n ≤
      Submodule.comap
        (F.closedMapSucc hF n)
        (B.ExactInClosedSucc n) := by
  intro x hx
  change
    (F.map (n + 1) x :
      D (n + 1)) ∈
        B.ExactSucc n
  change
    (x : C (n + 1)) ∈
      A.ExactSucc n at hx
  rcases hx with ⟨a, ha⟩
  refine ⟨F.map n a, ?_⟩
  rw [GradedLinearTransport.map_d hF n a]
  rw [ha]

/-- Induced linear map on arbitrary positive-degree causal cohomology. -/
def hSuccMap
    (hF : F.Natural)
    (n : ℕ) :
    A.HSucc n →ₗ[K] B.HSucc n :=
  (A.ExactInClosedSucc n).mapQ
    (B.ExactInClosedSucc n)
    (F.closedMapSucc hF n)
    (F.exactInClosedSucc_le_comap hF n)

/-- The induced cohomology map is represented by the original transport on
closed representatives. -/
@[simp] theorem hSuccMap_classOfClosed
    (hF : F.Natural)
    (n : ℕ)
    (x : A.Closed (n + 1)) :
    F.hSuccMap hF n
        (A.classOfClosedSucc n x)
      =
    B.classOfClosedSucc n
      (F.closedMapSucc hF n x) := by
  rfl

/-- Degree-zero closed cochains also transport functorially; no quotient is
needed because there is no incoming negative-degree differential. -/
def h0Map
    (hF : F.Natural) :
    A.H0 →ₗ[K] B.H0 where
  toFun := fun x =>
    ⟨F.map 0 x, by
      change B.d 0 (F.map 0 x) = 0
      rw [GradedLinearTransport.map_d hF 0 x]
      rw [x.2]
      simp⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    simp
  map_smul' := by
    intro a x
    apply Subtype.ext
    simp

end GradedLinearTransport

namespace PairedCochainTransport

variable
    {K : Type u}
    {C : ℕ → Type v}
    {D : ℕ → Type w}
    [Field K]
    [∀ n, AddCommGroup (C n)]
    [∀ n, Module K (C n)]
    [∀ n, AddCommGroup (D n)]
    [∀ n, Module K (D n)]
    {A : GradedCausalCochainComplex K C}
    {B : GradedCausalCochainComplex K D}
    (P : PairedCochainTransport A B)

/-- Phi-induced map on H^(n+1), when the forward differential defect
vanishes. -/
def forwardHSuccMap
    (hF : P.forward.Natural)
    (n : ℕ) :
    A.HSucc n →ₗ[K] B.HSucc n :=
  P.forward.hSuccMap hF n

/-- Psi-induced map on H^(n+1), independently requiring the backward defect to
vanish. -/
def backwardHSuccMap
    (hB : P.backward.Natural)
    (n : ℕ) :
    B.HSucc n →ₗ[K] A.HSucc n :=
  P.backward.hSuccMap hB n

def forwardH0Map
    (hF : P.forward.Natural) :
    A.H0 →ₗ[K] B.H0 :=
  P.forward.h0Map hF

def backwardH0Map
    (hB : P.backward.Natural) :
    B.H0 →ₗ[K] A.H0 :=
  P.backward.h0Map hB

/-- Cohomological source round trip.  It is an observable endomorphism and is
not assumed to be the identity. -/
def sourceHSuccRoundTrip
    (hF : P.forward.Natural)
    (hB : P.backward.Natural)
    (n : ℕ) :
    A.HSucc n →ₗ[K] A.HSucc n :=
  (P.backwardHSuccMap hB n).comp
    (P.forwardHSuccMap hF n)

/-- Cohomological target round trip. -/
def targetHSuccRoundTrip
    (hF : P.forward.Natural)
    (hB : P.backward.Natural)
    (n : ℕ) :
    B.HSucc n →ₗ[K] B.HSucc n :=
  (P.forwardHSuccMap hF n).comp
    (P.backwardHSuccMap hB n)

end PairedCochainTransport
end CausalGeometry
