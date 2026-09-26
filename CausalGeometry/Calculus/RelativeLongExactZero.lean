import CausalGeometry.Calculus.RelativeLongExactnessComplete
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
    (hF : F.Natural)
    (Sec : F.GradedLinearSection)

/-- Exactness at H0(A). -/
theorem range_relativeToSourceH0_eq_ker_h0Map :
    LinearMap.range
        (F.relativeToSourceH0 hF)
      =
    LinearMap.ker
        (F.h0Map hF) := by

  apply le_antisymm

  · intro x hx
    rcases hx with ⟨r, rfl⟩
    change
      F.h0Map hF
          (F.relativeToSourceH0 hF r)
        =
      0
    have h :=
      LinearMap.congr_fun
        (F.h0Map_comp_relativeToSource_zero hF)
        r
    simpa using h

  · intro x hx

    have hker :
        F.map 0 (x : C 0) = 0 := by
      exact congrArg Subtype.val hx

    let r0 :
        F.RelativeCochain 0 :=
      ⟨x, hker⟩

    let rz :
        F.RelativeH0 hF :=
      ⟨r0, by
        change A.d 0 (x : C 0) = 0
        exact x.2⟩

    refine ⟨rz, ?_⟩
    apply Subtype.ext
    rfl

/-- Exactness at H0(B). -/
theorem range_h0Map_eq_ker_connectingH0 :
    LinearMap.range
        (F.h0Map hF)
      =
    LinearMap.ker
        (F.connectingH0 hF Sec) := by

  apply le_antisymm

  · intro x hx
    rcases hx with ⟨a, rfl⟩
    change
      F.connectingH0 hF Sec
          (F.h0Map hF a)
        =
      0
    have h :=
      LinearMap.congr_fun
        (F.connectingH0_comp_h0Map_zero hF Sec)
        a
    simpa using h

  · intro z hz

    change
      F.connectingH0 hF Sec z = 0 at hz

    have hrelExact :
        ((F.connectingClosed0 hF Sec z :
          (F.relativeComplex hF).Closed 1) :
          F.RelativeCochain 1)
          ∈
        (F.relativeComplex hF).ExactSucc 0 :=
      ((F.relativeComplex hF)
        .classOfClosedSucc_eq_zero_iff
          0
          (F.connectingClosed0 hF Sec z)).1 hz

    rcases hrelExact with ⟨r, hr⟩

    let a : C 0 :=
      Sec.section 0 z -
        (r : C 0)

    have haClosed :
        A.d 0 a = 0 := by
      unfold a
      rw [map_sub]
      have hrv :
          A.d 0 (r : C 0) =
            A.d 0 (Sec.section 0 z) := by
        have hv :=
          congrArg Subtype.val hr
        exact hv
      rw [hrv]
      exact sub_self _

    let az : A.H0 :=
      ⟨a, haClosed⟩

    refine ⟨az, ?_⟩
    apply Subtype.ext

    change
      F.map 0 a =
        (z : D 0)

    unfold a
    rw [map_sub]
    rw [Sec.map_section]
    rw [r.2]
    simp

/-- The complete relative long-exact pattern available from a natural graded
restriction equipped with a degreewise linear section.

The theorem family now proves exactness at:
* H0(A),
* H0(B),
* H1(relative),
* every positive H(A),
* every positive H(B),
* every higher relative H.

This structure is only a named bundle of already-proved equalities; no new
exactness axiom is inserted. -/
structure RelativeLongExactPackage where

  exact_h0_source :
    LinearMap.range
        (F.relativeToSourceH0 hF)
      =
    LinearMap.ker
        (F.h0Map hF) :=
      F.range_relativeToSourceH0_eq_ker_h0Map
        hF Sec

  exact_h0_target :
    LinearMap.range
        (F.h0Map hF)
      =
    LinearMap.ker
        (F.connectingH0 hF Sec) :=
      F.range_h0Map_eq_ker_connectingH0
        hF Sec

  exact_h1_relative :
    LinearMap.range
        (F.connectingH0 hF Sec)
      =
    LinearMap.ker
        (F.relativeToSourceHSucc hF 0) :=
      F.range_connectingH0_eq_ker_relativeToSourceHSucc_zero
        hF Sec

  exact_positive_source :
    ∀ n,
      LinearMap.range
          (F.relativeToSourceHSucc hF n)
        =
      LinearMap.ker
          (F.hSuccMap hF n) :=
    F.range_relativeToSourceHSucc_eq_ker_hSuccMap
      hF Sec

  exact_positive_target :
    ∀ n,
      LinearMap.range
          (F.hSuccMap hF n)
        =
      LinearMap.ker
          (F.connectingHSucc hF Sec n) :=
    F.range_hSuccMap_eq_ker_connectingHSucc
      hF Sec

  exact_higher_relative :
    ∀ n,
      LinearMap.range
          (F.connectingHSucc hF Sec n)
        =
      LinearMap.ker
          (F.relativeToSourceHSucc hF (n + 1)) :=
    F.range_connectingHSucc_eq_ker_relativeToSourceHSucc
      hF Sec

/-- Canonical package constructor from the proved theorem family. -/
def relativeLongExactPackage :
    F.RelativeLongExactPackage hF Sec :=
  {}

end GradedLinearTransport
end CausalGeometry
