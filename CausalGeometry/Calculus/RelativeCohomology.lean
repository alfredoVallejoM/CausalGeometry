import CausalGeometry.Calculus.PairedCochainTransport
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

/-- Degree-n relative cochains for a restriction-like natural transport:
cochains invisible under F_n.

For a geometric restriction map this is the standard kernel model of relative
cochains.  The definition itself remains target-neutral. -/
abbrev RelativeCochain (n : ℕ) :=
  (F.map n).ker

/-- Naturality makes the differential preserve the relative kernel. -/
def relativeDifferential
    (hF : F.Natural)
    (n : ℕ) :
    F.RelativeCochain n →ₗ[K]
      F.RelativeCochain (n + 1) where
  toFun := fun x =>
    ⟨A.d n x, by
      change F.map (n + 1) (A.d n x) = 0
      rw [← GradedLinearTransport.map_d hF n x]
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

@[simp] theorem relativeDifferential_val
    (hF : F.Natural)
    (n : ℕ)
    (x : F.RelativeCochain n) :
    ((F.relativeDifferential hF n x :
      F.RelativeCochain (n + 1)) :
      C (n + 1))
      =
    A.d n x :=
  rfl

/-- Relative cochains form a genuine graded causal cochain complex. -/
def relativeComplex
    (hF : F.Natural) :
    GradedCausalCochainComplex
      K
      (fun n => F.RelativeCochain n) where
  d :=
    F.relativeDifferential hF
  d_sq := by
    intro n
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change A.d (n + 1) (A.d n x) = 0
    exact A.d_d n x

/-- Relative H0. -/
abbrev RelativeH0
    (hF : F.Natural) :=
  (F.relativeComplex hF).H0

/-- Relative H^(n+1). -/
abbrev RelativeHSucc
    (hF : F.Natural)
    (n : ℕ) :=
  (F.relativeComplex hF).HSucc n

/-- Inclusion of relative cochains into the ambient source complex. -/
def relativeInclusion
    (hF : F.Natural) :
    GradedLinearTransport
      (F.relativeComplex hF) A where
  map := fun _ => Submodule.subtype _

theorem relativeInclusion_natural
    (hF : F.Natural) :
    (F.relativeInclusion hF).Natural := by
  intro n
  apply LinearMap.ext
  intro x
  rfl

/-- The composite relative -> source -> target vanishes degreewise. -/
theorem relative_composite_zero
    (hF : F.Natural)
    (n : ℕ) :
    (F.map n).comp
        ((F.relativeInclusion hF).map n)
      =
    0 := by
  apply LinearMap.ext
  intro x
  exact x.2

/-- At the cochain level the relative complex is exactly the kernel of the
restriction-like map, not merely equivalent to an unspecified subcomplex. -/
theorem mem_relative_iff
    (n : ℕ)
    (x : C n) :
    x ∈ (F.map n).ker ↔
      F.map n x = 0 :=
  Iff.rfl

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

/-- Relative source complex detected by the forward/Phi transport. -/
def forwardRelativeComplex
    (hF : P.forward.Natural) :=
  P.forward.relativeComplex hF

/-- Relative target complex detected by the backward/Psi transport. -/
def backwardRelativeComplex
    (hB : P.backward.Natural) :=
  P.backward.relativeComplex hB

/-- Forward and backward relative theories are intentionally different
objects.  No equivalence is asserted merely from the existence of the paired
transport. -/
abbrev ForwardRelativeHSucc
    (hF : P.forward.Natural)
    (n : ℕ) :=
  P.forward.RelativeHSucc hF n

abbrev BackwardRelativeHSucc
    (hB : P.backward.Natural)
    (n : ℕ) :=
  P.backward.RelativeHSucc hB n

end PairedCochainTransport
end CausalGeometry
