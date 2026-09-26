import CausalGeometry.Calculus.RelativeLongExactness
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

/-- Inclusion of a connecting class into source cohomology is zero in every
positive source degree. -/
theorem relativeToSourceHSucc_comp_connectingHSucc_zero
    (n : ℕ) :
    (F.relativeToSourceHSucc hF (n + 1)).comp
        (F.connectingHSucc hF Sec n)
      =
    0 := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ z =>
      rw [F.connectingHSucc_classOfClosed]
      change
        F.relativeToSourceHSucc hF (n + 1)
          ((F.relativeComplex hF)
            .classOfClosedSucc (n + 1)
              (F.connectingClosedSucc hF Sec n z))
          =
        0
      rw [
        (F.relativeInclusion hF)
          .hSuccMap_classOfClosed
      ]
      apply
        ((A.classOfClosedSucc_eq_zero_iff
          (n + 1)
          ((F.relativeInclusion hF)
            .closedMapSucc
              (F.relativeInclusion_natural hF)
              (n + 1)
              (F.connectingClosedSucc hF Sec n z))).2)
      change
        A.d (n + 1)
            (Sec.section (n + 1) z)
          ∈
        A.ExactSucc (n + 1)
      exact
        ⟨Sec.section (n + 1) z, rfl⟩

/-- Degree-zero connector followed by relative inclusion is also zero. -/
theorem relativeToSourceHSucc_comp_connectingH0_zero :
    (F.relativeToSourceHSucc hF 0).comp
        (F.connectingH0 hF Sec)
      =
    0 := by
  apply LinearMap.ext
  intro z
  change
    F.relativeToSourceHSucc hF 0
        ((F.relativeComplex hF)
          .classOfClosedSucc 0
            (F.connectingClosed0 hF Sec z))
      =
    0
  rw [
    (F.relativeInclusion hF)
      .hSuccMap_classOfClosed
  ]
  apply
    ((A.classOfClosedSucc_eq_zero_iff
      0
      ((F.relativeInclusion hF)
        .closedMapSucc
          (F.relativeInclusion_natural hF)
          0
          (F.connectingClosed0 hF Sec z))).2)
  change
    A.d 0 (Sec.section 0 z)
      ∈
    A.ExactSucc 0
  exact ⟨Sec.section 0 z, rfl⟩

/-- Exactness at relative cohomology in all degrees >= 2:

image(delta : H^(n+1)(B) -> H^(n+2)_rel)
=
kernel(H^(n+2)_rel -> H^(n+2)(A)). -/
theorem range_connectingHSucc_eq_ker_relativeToSourceHSucc
    (n : ℕ) :
    LinearMap.range
        (F.connectingHSucc hF Sec n)
      =
    LinearMap.ker
        (F.relativeToSourceHSucc hF (n + 1)) := by

  apply le_antisymm

  · intro x hx
    rcases hx with ⟨b, rfl⟩
    change
      F.relativeToSourceHSucc hF (n + 1)
          (F.connectingHSucc hF Sec n b)
        =
      0
    have h :=
      LinearMap.congr_fun
        (F.relativeToSourceHSucc_comp_connectingHSucc_zero
          hF Sec n) b
    simpa using h

  · intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ z =>
        change
          F.relativeToSourceHSucc hF (n + 1)
              ((F.relativeComplex hF)
                .classOfClosedSucc (n + 1) z)
            =
          0 at hx

        rw [
          (F.relativeInclusion hF)
            .hSuccMap_classOfClosed
        ] at hx

        have hAExact :
            (((z :
                (F.relativeComplex hF).Closed
                  (n + 2)) :
              F.RelativeCochain (n + 2)) :
              C (n + 2))
              ∈
            A.ExactSucc (n + 1) :=
          (A.classOfClosedSucc_eq_zero_iff
            (n + 1)
            ((F.relativeInclusion hF)
              .closedMapSucc
                (F.relativeInclusion_natural hF)
                (n + 1) z)).1 hx

        rcases hAExact with ⟨a, ha⟩

        let bz :
            B.Closed (n + 1) :=
          ⟨F.map (n + 1) a,
            by
              rw [GradedLinearTransport.map_d hF]
              rw [ha]
              exact z.1.2⟩

        let qB :
            B.HSucc n :=
          B.classOfClosedSucc n bz

        refine ⟨qB, ?_⟩

        rw [F.connectingHSucc_classOfClosed]

        apply
          (Submodule.Quotient.eq
            ((F.relativeComplex hF)
              .ExactInClosedSucc (n + 1))).2

        let r0 :
            F.RelativeCochain (n + 1) :=
          ⟨Sec.section (n + 1) bz - a,
            by
              change
                F.map (n + 1)
                    (Sec.section (n + 1) bz - a)
                  =
                0
              rw [map_sub]
              rw [Sec.map_section]
              exact sub_self _⟩

        change
          ((F.connectingClosedSucc
              hF Sec n bz :
            (F.relativeComplex hF).Closed
              (n + 2)) :
            F.RelativeCochain (n + 2))
            -
          (z :
            (F.relativeComplex hF).Closed
              (n + 2))
          ∈
          (F.relativeComplex hF)
            .ExactSucc (n + 1)

        refine ⟨r0, ?_⟩
        apply Subtype.ext
        change
          A.d (n + 1)
              (Sec.section (n + 1) bz - a)
            =
          A.d (n + 1)
              (Sec.section (n + 1) bz)
            -
          ((z.1 :
            F.RelativeCochain (n + 2)) :
              C (n + 2))
        rw [map_sub]
        rw [ha]

/-- Exactness at relative H^1, whose incoming connector starts at H^0(B). -/
theorem range_connectingH0_eq_ker_relativeToSourceHSucc_zero :
    LinearMap.range
        (F.connectingH0 hF Sec)
      =
    LinearMap.ker
        (F.relativeToSourceHSucc hF 0) := by

  apply le_antisymm

  · intro x hx
    rcases hx with ⟨b, rfl⟩
    change
      F.relativeToSourceHSucc hF 0
          (F.connectingH0 hF Sec b)
        =
      0
    have h :=
      LinearMap.congr_fun
        (F.relativeToSourceHSucc_comp_connectingH0_zero
          hF Sec) b
    simpa using h

  · intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ z =>
        change
          F.relativeToSourceHSucc hF 0
              ((F.relativeComplex hF)
                .classOfClosedSucc 0 z)
            =
          0 at hx

        rw [
          (F.relativeInclusion hF)
            .hSuccMap_classOfClosed
        ] at hx

        have hAExact :
            (((z :
                (F.relativeComplex hF).Closed 1) :
              F.RelativeCochain 1) :
              C 1)
              ∈
            A.ExactSucc 0 :=
          (A.classOfClosedSucc_eq_zero_iff
            0
            ((F.relativeInclusion hF)
              .closedMapSucc
                (F.relativeInclusion_natural hF)
                0 z)).1 hx

        rcases hAExact with ⟨a, ha⟩

        let bz : B.H0 :=
          ⟨F.map 0 a,
            by
              rw [GradedLinearTransport.map_d hF]
              rw [ha]
              exact z.1.2⟩

        refine ⟨bz, ?_⟩

        change
          F.connectingH0 hF Sec bz =
            (F.relativeComplex hF)
              .classOfClosedSucc 0 z

        apply
          (Submodule.Quotient.eq
            ((F.relativeComplex hF)
              .ExactInClosedSucc 0)).2

        let r0 :
            F.RelativeCochain 0 :=
          ⟨Sec.section 0 bz - a,
            by
              change
                F.map 0
                    (Sec.section 0 bz - a)
                  =
                0
              rw [map_sub]
              rw [Sec.map_section]
              exact sub_self _⟩

        change
          ((F.connectingClosed0 hF Sec bz :
            (F.relativeComplex hF).Closed 1) :
            F.RelativeCochain 1)
            -
          (z :
            (F.relativeComplex hF).Closed 1)
          ∈
          (F.relativeComplex hF)
            .ExactSucc 0

        refine ⟨r0, ?_⟩
        apply Subtype.ext
        change
          A.d 0 (Sec.section 0 bz - a)
            =
          A.d 0 (Sec.section 0 bz) -
            ((z.1 : F.RelativeCochain 1) : C 1)
        rw [map_sub]
        rw [ha]

end GradedLinearTransport
end CausalGeometry
