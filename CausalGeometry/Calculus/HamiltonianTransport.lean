import CausalGeometry.Calculus.BilinearTransport

namespace CausalGeometry

universe u v w x
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalHamiltonian

variable {K : Type w}
variable {Fiber : Configuration S → Type x}
variable [CommRing K]
variable [∀ C, AddCommGroup (Fiber C)]
variable [∀ C, Module K (Fiber C)]

abbrev VectorSection :=
  (C : Configuration S) → Fiber C

abbrev CovectorSection :=
  (C : Configuration S) →
    Module.Dual K (Fiber C)

/-- Hamiltonian relation relative to one bilinear field.

The sign convention is explicit here: flat(X)=dH. A consumer wanting
flat(X)=-dH uses the negated covector section rather than changing the
foundational bilinear structure. -/
structure Pair
    (B : CausalBilinear.Field
      (K := K) (S := S) (Fiber := Fiber)) where
  vector :
    VectorSection (S := S) (Fiber := Fiber)
  covector :
    CovectorSection (K := K) (S := S) (Fiber := Fiber)

  hamiltonian :
    ∀ C,
      B.flat C (vector C) =
        covector C

namespace Pair

variable
    {B : CausalBilinear.Field
      (K := K) (S := S) (Fiber := Fiber)}
    (H : Pair B)

/-- A vector section is parallel when the target vector is the forward
transport of the source vector. -/
def VectorParallelAt
    (∇ : DependentLinearEquivConnection K S Fiber)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) : Prop :=
  H.vector (S.extend C e h) =
    ∇.transport C e h (H.vector C)

/-- A covector section is parallel using the canonical forward covector
transport induced by inverse vector transport. -/
def CovectorParallelAt
    (∇ : DependentLinearEquivConnection K S Fiber)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) : Prop :=
  H.covector (S.extend C e h) =
    ∇.covectorPushforward C e h
      (H.covector C)

/-- Under nondegeneracy and preservation of the bilinear form, parallel
Hamiltonian covectors force parallel Hamiltonian vectors. -/
theorem vectorParallel_of_covectorParallel
    (∇ : DependentLinearEquivConnection K S Fiber)
    (hnd : B.LeftNondegenerate)
    (hpres : B.PreservedByEquiv ∇)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e)
    (hcov : H.CovectorParallelAt ∇ C e h) :
    H.VectorParallelAt ∇ C e h := by
  unfold VectorParallelAt
  apply (B.flat_injective hnd
    (S.extend C e h))
  rw [H.hamiltonian]
  rw [B.flat_natural ∇ hpres]
  rw [H.hamiltonian]
  exact hcov

/-- Conversely, preserved bilinear structure sends parallel Hamiltonian
vectors to parallel Hamiltonian covectors without needing nondegeneracy. -/
theorem covectorParallel_of_vectorParallel
    (∇ : DependentLinearEquivConnection K S Fiber)
    (hpres : B.PreservedByEquiv ∇)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e)
    (hvec : H.VectorParallelAt ∇ C e h) :
    H.CovectorParallelAt ∇ C e h := by
  unfold CovectorParallelAt
  rw [← H.hamiltonian]
  rw [hvec]
  exact B.flat_natural ∇ hpres C e h
    (H.vector C)

/-- For a nondegenerate preserved bilinear field, vector and covector
Hamiltonian parallelism are equivalent. -/
theorem vectorParallel_iff_covectorParallel
    (∇ : DependentLinearEquivConnection K S Fiber)
    (hnd : B.LeftNondegenerate)
    (hpres : B.PreservedByEquiv ∇)
    (C : Configuration S)
    (e : Event)
    (h : S.Enabled C e) :
    H.VectorParallelAt ∇ C e h ↔
      H.CovectorParallelAt ∇ C e h := by
  constructor
  · exact H.covectorParallel_of_vectorParallel
      ∇ hpres C e h
  · exact H.vectorParallel_of_covectorParallel
      ∇ hnd hpres C e h

end Pair

/-- A musical bridge canonically turns any covector section into a Hamiltonian
pair. -/
def Pair.ofMusical
    {B : CausalBilinear.Field
      (K := K) (S := S) (Fiber := Fiber)}
    (M : CausalBilinear.MusicalBridge B)
    (dH : CovectorSection
      (K := K) (S := S) (Fiber := Fiber)) :
    Pair B where
  vector := fun C => M.sharp C (dH C)
  covector := dH
  hamiltonian := by
    intro C
    exact M.flat_sharp C (dH C)

end CausalHamiltonian
end CausalGeometry
