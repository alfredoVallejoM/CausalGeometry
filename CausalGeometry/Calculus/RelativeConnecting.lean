import CausalGeometry.Calculus.RelativeExactSequence
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

/-- A degreewise linear section of a restriction-like graded transport.

This is stronger than mere surjectivity, but over vector spaces it is the
constructive datum needed to define a connecting morphism without arbitrary
nonlinear choices. -/
structure GradedLinearSection where
  section :
    ∀ n,
      D n →ₗ[K] C n

  right_inverse :
    ∀ n,
      (F.map n).comp (section n) =
        LinearMap.id

namespace GradedLinearSection

variable
    (Sec : F.GradedLinearSection)

@[simp] theorem map_section
    (n : ℕ)
    (y : D n) :
    F.map n (Sec.section n y) = y := by
  have h :=
    LinearMap.congr_fun
      (Sec.right_inverse n) y
  simpa using h

end GradedLinearSection

variable
    (hF : F.Natural)
    (Sec : F.GradedLinearSection)

/-- Boundary of a lifted closed target cochain, viewed in the relative kernel.

A closed target cochain z in degree n+1 is lifted by the section.  Naturality
and closedness imply that d(section z) lies in ker(F_(n+2)). -/
def connectingRelativeCochainSucc
    (n : ℕ)
    (z : B.Closed (n + 1)) :
    F.RelativeCochain (n + 2) :=
  ⟨A.d (n + 1)
      (Sec.section (n + 1) z),
    by
      change
        F.map (n + 2)
            (A.d (n + 1)
              (Sec.section (n + 1) z))
          =
        0
      rw [← GradedLinearTransport.map_d
        hF (n + 1)
        (Sec.section (n + 1) z)]
      rw [Sec.map_section]
      exact z.2⟩

/-- The lifted boundary is itself closed in the relative complex by d^2=0. -/
def connectingClosedSucc
    (n : ℕ) :
    B.Closed (n + 1) →ₗ[K]
      (F.relativeComplex hF).Closed (n + 2) where

  toFun := fun z =>
    ⟨F.connectingRelativeCochainSucc
        hF Sec n z,
      by
        change
          A.d (n + 2)
              (A.d (n + 1)
                (Sec.section (n + 1) z))
            =
          0
        exact
          A.d_d (n + 1)
            (Sec.section (n + 1) z)⟩

  map_add' := by
    intro x y
    apply Subtype.ext
    apply Subtype.ext
    simp [connectingRelativeCochainSucc]

  map_smul' := by
    intro a x
    apply Subtype.ext
    apply Subtype.ext
    simp [connectingRelativeCochainSucc]

/-- Closed target cochains map to relative cohomology one degree higher. -/
def connectingClosedClassSucc
    (n : ℕ) :
    B.Closed (n + 1) →ₗ[K]
      F.RelativeHSucc hF (n + 1) :=
  ((F.relativeComplex hF)
      .classOfClosedSucc (n + 1)).comp
    (F.connectingClosedSucc hF Sec n)

/-- If a closed target cochain is exact, its lifted boundary is relatively
exact.  This is the key well-definedness theorem for the connecting map. -/
theorem connectingClosedClassSucc_eq_zero_of_exact
    (n : ℕ)
    (z : B.Closed (n + 1))
    (hz :
      (z : D (n + 1)) ∈
        B.ExactSucc n) :
    F.connectingClosedClassSucc
        hF Sec n z
      =
    0 := by

  rcases hz with ⟨b, hb⟩

  let r :
      F.RelativeCochain (n + 1) :=
    ⟨Sec.section (n + 1) z -
        A.d n (Sec.section n b),
      by
        change
          F.map (n + 1)
              (Sec.section (n + 1) z -
                A.d n (Sec.section n b))
            =
          0
        rw [map_sub]
        rw [Sec.map_section]
        rw [← GradedLinearTransport.map_d
          hF n (Sec.section n b)]
        rw [Sec.map_section]
        rw [hb]
        exact sub_self _⟩

  apply
    ((F.relativeComplex hF)
      .classOfClosedSucc_eq_zero_iff
        (n + 1)
        (F.connectingClosedSucc hF Sec n z)).2

  refine ⟨r, ?_⟩
  apply Subtype.ext
  change
    A.d (n + 1)
        (Sec.section (n + 1) z -
          A.d n (Sec.section n b))
      =
    A.d (n + 1)
      (Sec.section (n + 1) z)

  rw [map_sub]
  rw [A.d_d n]
  simp

/-- Exact closed target cochains lie in the kernel of the pre-connecting map. -/
theorem exactInClosedSucc_le_connectingKernel
    (n : ℕ) :
    B.ExactInClosedSucc n ≤
      LinearMap.ker
        (F.connectingClosedClassSucc
          hF Sec n) := by
  intro z hz
  change
    F.connectingClosedClassSucc
        hF Sec n z
      =
    0
  exact
    F.connectingClosedClassSucc_eq_zero_of_exact
      hF Sec n z hz

/-- Positive-degree connecting homomorphism

delta : H^(n+1)(B) -> H^(n+2)(relative F).

It is obtained by quotient lifting the closed-cochain construction through the
proved vanishing on exact representatives. -/
def connectingHSucc
    (n : ℕ) :
    B.HSucc n →ₗ[K]
      F.RelativeHSucc hF (n + 1) :=
  (B.ExactInClosedSucc n).liftQ
    (F.connectingClosedClassSucc
      hF Sec n)
    (F.exactInClosedSucc_le_connectingKernel
      hF Sec n)

/-- The connecting homomorphism on a closed representative is represented by
the relative class of d(section z). -/
@[simp] theorem connectingHSucc_classOfClosed
    (n : ℕ)
    (z : B.Closed (n + 1)) :
    F.connectingHSucc hF Sec n
        (B.classOfClosedSucc n z)
      =
    F.connectingClosedClassSucc
      hF Sec n z := by
  rfl


/-- Degree-zero relative boundary of a lifted closed target 0-cochain. -/
def connectingRelativeCochain0
    (z : B.H0) :
    F.RelativeCochain 1 :=
  ⟨A.d 0 (Sec.section 0 z),
    by
      change
        F.map 1 (A.d 0 (Sec.section 0 z)) = 0
      rw [← GradedLinearTransport.map_d
        hF 0 (Sec.section 0 z)]
      rw [Sec.map_section]
      exact z.2⟩

/-- The degree-zero connecting boundary is closed in relative degree one. -/
def connectingClosed0 :
    B.H0 →ₗ[K]
      (F.relativeComplex hF).Closed 1 where
  toFun := fun z =>
    ⟨F.connectingRelativeCochain0 hF Sec z,
      by
        change
          A.d 1 (A.d 0 (Sec.section 0 z)) = 0
        exact A.d_d 0 (Sec.section 0 z)⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    apply Subtype.ext
    simp [connectingRelativeCochain0]
  map_smul' := by
    intro a x
    apply Subtype.ext
    apply Subtype.ext
    simp [connectingRelativeCochain0]

/-- Degree-zero connecting homomorphism
H^0(B) -> H^1(relative F). -/
def connectingH0 :
    B.H0 →ₗ[K]
      F.RelativeHSucc hF 0 :=
  ((F.relativeComplex hF)
      .classOfClosedSucc 0).comp
    (F.connectingClosed0 hF Sec)

/-- A source closed cochain maps to a target class with zero connecting class
in every positive degree. -/
theorem connectingClosedClassSucc_eq_zero_of_source
    (n : ℕ)
    (a : A.Closed (n + 1)) :
    F.connectingClosedClassSucc
        hF Sec n
        (F.closedMapSucc hF n a)
      =
    0 := by

  let r :
      F.RelativeCochain (n + 1) :=
    ⟨Sec.section (n + 1)
        (F.closedMapSucc hF n a) -
        (a : C (n + 1)),
      by
        change
          F.map (n + 1)
              (Sec.section (n + 1)
                (F.closedMapSucc hF n a) -
                (a : C (n + 1)))
            =
          0
        rw [map_sub]
        rw [Sec.map_section]
        exact sub_self _⟩

  apply
    ((F.relativeComplex hF)
      .classOfClosedSucc_eq_zero_iff
        (n + 1)
        (F.connectingClosedSucc
          hF Sec n
          (F.closedMapSucc hF n a))).2

  refine ⟨r, ?_⟩
  apply Subtype.ext
  change
    A.d (n + 1)
        (Sec.section (n + 1)
            (F.closedMapSucc hF n a) -
          (a : C (n + 1)))
      =
    A.d (n + 1)
      (Sec.section (n + 1)
        (F.closedMapSucc hF n a))
  rw [map_sub]
  rw [a.2]
  simp

/-- The positive-degree cohomology map followed by the connecting
homomorphism is zero. -/
theorem connectingHSucc_comp_hSuccMap_zero
    (n : ℕ) :
    (F.connectingHSucc hF Sec n).comp
        (F.hSuccMap hF n)
      =
    0 := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ a =>
      change
        F.connectingHSucc hF Sec n
          (F.hSuccMap hF n
            (A.classOfClosedSucc n a))
          =
        0
      rw [F.hSuccMap_classOfClosed]
      rw [F.connectingHSucc_classOfClosed]
      exact
        F.connectingClosedClassSucc_eq_zero_of_source
          hF Sec n a

/-- The same complex identity in degree zero. -/
theorem connectingH0_comp_h0Map_zero :
    (F.connectingH0 hF Sec).comp
        (F.h0Map hF)
      =
    0 := by
  apply LinearMap.ext
  intro a

  apply
    ((F.relativeComplex hF)
      .classOfClosedSucc_eq_zero_iff
        0
        (F.connectingClosed0 hF Sec
          (F.h0Map hF a))).2

  let r :
      F.RelativeCochain 0 :=
    ⟨Sec.section 0 (F.h0Map hF a) -
        (a : C 0),
      by
        change
          F.map 0
              (Sec.section 0 (F.h0Map hF a) -
                (a : C 0))
            =
          0
        rw [map_sub]
        rw [Sec.map_section]
        exact sub_self _⟩

  refine ⟨r, ?_⟩
  apply Subtype.ext
  change
    A.d 0
        (Sec.section 0 (F.h0Map hF a) -
          (a : C 0))
      =
    A.d 0
      (Sec.section 0 (F.h0Map hF a))
  rw [map_sub]
  rw [a.2]
  simp

end GradedLinearTransport
end CausalGeometry
