import CausalGeometry.Calculus.GradedComplex
import CausalGeometry.Foundation.PairedTransform
import Mathlib.Tactic

namespace CausalGeometry

universe u v w

/-- A degree-preserving linear transport between two graded causal complexes.

It is deliberately weaker than a cochain map: commutation with d is a
separate property measured by an explicit defect. -/
structure GradedLinearTransport
    {K : Type u}
    {C : ℕ → Type v}
    {D : ℕ → Type w}
    [Field K]
    [∀ n, AddCommGroup (C n)]
    [∀ n, Module K (C n)]
    [∀ n, AddCommGroup (D n)]
    [∀ n, Module K (D n)]
    (A : GradedCausalCochainComplex K C)
    (B : GradedCausalCochainComplex K D) where

  map : ∀ n, C n →ₗ[K] D n

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

/-- The graded commutator d_B F - F d_A. -/
def defect
    (F : GradedLinearTransport A B)
    (n : ℕ) :
    C n →ₗ[K] D (n + 1) :=
  (B.d n).comp (F.map n) -
    (F.map (n + 1)).comp (A.d n)

/-- A transport is a cochain map exactly when every differential defect
vanishes. -/
def Natural
    (F : GradedLinearTransport A B) : Prop :=
  ∀ n,
    (B.d n).comp (F.map n) =
      (F.map (n + 1)).comp (A.d n)

theorem natural_iff_defect_zero
    (F : GradedLinearTransport A B) :
    F.Natural ↔
      ∀ n, F.defect n = 0 := by
  constructor
  · intro h n
    exact sub_eq_zero.mpr (h n)
  · intro h n
    exact sub_eq_zero.mp (h n)

/-- Pointwise chain-map equation. -/
theorem map_d
    {F : GradedLinearTransport A B}
    (h : F.Natural)
    (n : ℕ)
    (x : C n) :
    B.d n (F.map n x) =
      F.map (n + 1) (A.d n x) := by
  exact LinearMap.congr_fun (h n) x

/-- Identity graded transport. -/
def identity
    (A : GradedCausalCochainComplex K C) :
    GradedLinearTransport A A where
  map := fun _ => LinearMap.id

@[simp] theorem identity_defect
    (A : GradedCausalCochainComplex K C)
    (n : ℕ) :
    (identity A).defect n = 0 := by
  ext x
  simp [defect, identity]

theorem identity_natural
    (A : GradedCausalCochainComplex K C) :
    (identity A).Natural := by
  rw [natural_iff_defect_zero]
  exact identity_defect A

/-- Covariant composition of graded transports. -/
def comp
    {E : ℕ → Type*}
    [∀ n, AddCommGroup (E n)]
    [∀ n, Module K (E n)]
    {Z : GradedCausalCochainComplex K E}
    (F : GradedLinearTransport A B)
    (G : GradedLinearTransport B Z) :
    GradedLinearTransport A Z where
  map := fun n => (G.map n).comp (F.map n)

@[simp] theorem comp_map
    {E : ℕ → Type*}
    [∀ n, AddCommGroup (E n)]
    [∀ n, Module K (E n)]
    {Z : GradedCausalCochainComplex K E}
    (F : GradedLinearTransport A B)
    (G : GradedLinearTransport B Z)
    (n : ℕ)
    (x : C n) :
    (F.comp G).map n x =
      G.map n (F.map n x) :=
  rfl

/-- Leibniz rule for differential defects under composition:
D(GF) = D(G)F + G D(F). -/
theorem comp_defect
    {E : ℕ → Type*}
    [∀ n, AddCommGroup (E n)]
    [∀ n, Module K (E n)]
    {Z : GradedCausalCochainComplex K E}
    (F : GradedLinearTransport A B)
    (G : GradedLinearTransport B Z)
    (n : ℕ) :
    (F.comp G).defect n =
      (G.defect n).comp (F.map n) +
        (G.map (n + 1)).comp (F.defect n) := by
  ext x
  simp [defect, comp, LinearMap.comp_apply]
  abel

theorem comp_natural
    {E : ℕ → Type*}
    [∀ n, AddCommGroup (E n)]
    [∀ n, Module K (E n)]
    {Z : GradedCausalCochainComplex K E}
    {F : GradedLinearTransport A B}
    {G : GradedLinearTransport B Z}
    (hF : F.Natural)
    (hG : G.Natural) :
    (F.comp G).Natural := by
  intro n
  ext x
  simp only [comp_map, LinearMap.comp_apply]
  rw [hG.map_d n (F.map n x)]
  rw [hF.map_d n x]

end GradedLinearTransport

/-- Degreewise causal/restriction transport between graded complexes.

Forward (Phi) and backward (Psi) are independent graded linear transports.
Neither is required to commute with d and neither is required to invert the
other. -/
structure PairedCochainTransport
    {K : Type u}
    {C : ℕ → Type v}
    {D : ℕ → Type w}
    [Field K]
    [∀ n, AddCommGroup (C n)]
    [∀ n, Module K (C n)]
    [∀ n, AddCommGroup (D n)]
    [∀ n, Module K (D n)]
    (A : GradedCausalCochainComplex K C)
    (B : GradedCausalCochainComplex K D) where

  forward : GradedLinearTransport A B
  backward : GradedLinearTransport B A

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

/-- Forget linear structure in one degree and recover the foundational
PairedTransform. -/
def toPaired (n : ℕ) :
    PairedTransform (C n) (D n) where
  forward := P.forward.map n
  backward := P.backward.map n

/-- Source round trip Psi Phi as a graded transport. -/
def sourceRoundTrip :
    GradedLinearTransport A A :=
  P.forward.comp P.backward

/-- Target round trip Phi Psi as a graded transport. -/
def targetRoundTrip :
    GradedLinearTransport B B :=
  P.backward.comp P.forward

/-- Exact decomposition of the source round-trip differential defect.

This formula isolates the two independent failures:
D(Psi Phi) = D(Psi) Phi + Psi D(Phi). -/
theorem sourceRoundTrip_defect (n : ℕ) :
    P.sourceRoundTrip.defect n =
      (P.backward.defect n).comp
          (P.forward.map n) +
        (P.backward.map (n + 1)).comp
          (P.forward.defect n) := by
  exact
    GradedLinearTransport.comp_defect
      P.forward P.backward n

/-- Dual formula on the target round trip. -/
theorem targetRoundTrip_defect (n : ℕ) :
    P.targetRoundTrip.defect n =
      (P.forward.defect n).comp
          (P.backward.map n) +
        (P.forward.map (n + 1)).comp
          (P.backward.defect n) := by
  exact
    GradedLinearTransport.comp_defect
      P.backward P.forward n

theorem sourceRoundTrip_natural
    (hF : P.forward.Natural)
    (hB : P.backward.Natural) :
    P.sourceRoundTrip.Natural :=
  GradedLinearTransport.comp_natural hF hB

theorem targetRoundTrip_natural
    (hF : P.forward.Natural)
    (hB : P.backward.Natural) :
    P.targetRoundTrip.Natural :=
  GradedLinearTransport.comp_natural hB hF

end PairedCochainTransport
end CausalGeometry
