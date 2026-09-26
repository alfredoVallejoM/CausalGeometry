import CausalGeometry.Calculus.RelativeLongSequence
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

/-- Exactness at source cohomology:
the kernel of H(A)->H(B) is exactly the image of relative cohomology. -/
theorem range_relativeToSourceHSucc_eq_ker_hSuccMap
    (n : ℕ) :
    LinearMap.range
        (F.relativeToSourceHSucc hF n)
      =
    LinearMap.ker
        (F.hSuccMap hF n) := by

  apply le_antisymm

  · intro x hx
    rcases hx with ⟨r, rfl⟩
    change
      F.hSuccMap hF n
          (F.relativeToSourceHSucc hF n r)
        =
      0
    have h :=
      LinearMap.congr_fun
        (F.hSuccMap_comp_relativeToSource_zero
          hF n) r
    simpa using h

  · intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ a =>
        change
          F.hSuccMap hF n
              (A.classOfClosedSucc n a)
            =
          0 at hx

        rw [F.hSuccMap_classOfClosed] at hx

        have hexact :
            ((F.closedMapSucc hF n a :
                B.Closed (n + 1)) :
              D (n + 1))
              ∈
            B.ExactSucc n :=
          (B.classOfClosedSucc_eq_zero_iff
            n
            (F.closedMapSucc hF n a)).1 hx

        rcases hexact with ⟨b, hb⟩

        let c : C n :=
          Sec.section n b

        let r :
            F.RelativeCochain (n + 1) :=
          ⟨(a : C (n + 1)) -
              A.d n c,
            by
              change
                F.map (n + 1)
                    ((a : C (n + 1)) -
                      A.d n c)
                  =
                0
              rw [map_sub]
              rw [← GradedLinearTransport.map_d
                hF n c]
              rw [Sec.map_section]
              change
                F.map (n + 1) (a : C (n + 1)) -
                    B.d n b
                  =
                0
              rw [hb]
              exact sub_self _⟩

        let rz :
            (F.relativeComplex hF).Closed
              (n + 1) :=
          ⟨r, by
            change
              A.d (n + 1)
                  ((a : C (n + 1)) -
                    A.d n c)
                =
              0
            rw [map_sub]
            rw [a.2, A.d_d n]
            simp⟩

        let qrel :
            F.RelativeHSucc hF n :=
          (F.relativeComplex hF)
            .classOfClosedSucc n rz

        refine ⟨qrel, ?_⟩

        change
          F.relativeToSourceHSucc hF n qrel
            =
          A.classOfClosedSucc n a

        rw [
          (F.relativeInclusion hF)
            .hSuccMap_classOfClosed
        ]

        apply
          (Submodule.Quotient.eq
            (A.ExactInClosedSucc n)).2

        change
          (((r : F.RelativeCochain (n + 1)) :
              C (n + 1)) -
            (a : C (n + 1)))
            ∈
          A.ExactSucc n

        refine ⟨-c, ?_⟩
        simp [r, c]

/-- Exactness at target cohomology:
the kernel of the connecting homomorphism is exactly the image of H(A). -/
theorem range_hSuccMap_eq_ker_connectingHSucc
    (n : ℕ) :
    LinearMap.range
        (F.hSuccMap hF n)
      =
    LinearMap.ker
        (F.connectingHSucc hF Sec n) := by

  apply le_antisymm

  · intro x hx
    rcases hx with ⟨a, rfl⟩
    change
      F.connectingHSucc hF Sec n
          (F.hSuccMap hF n a)
        =
      0
    have h :=
      LinearMap.congr_fun
        (F.connectingHSucc_comp_hSuccMap_zero
          hF Sec n) a
    simpa using h

  · intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ z =>
        change
          F.connectingHSucc hF Sec n
              (B.classOfClosedSucc n z)
            =
          0 at hx

        rw [F.connectingHSucc_classOfClosed] at hx

        have hrelExact :
            ((F.connectingClosedSucc
                hF Sec n z :
              (F.relativeComplex hF).Closed
                (n + 2)) :
              F.RelativeCochain (n + 2))
              ∈
            (F.relativeComplex hF)
              .ExactSucc (n + 1) :=
          ((F.relativeComplex hF)
            .classOfClosedSucc_eq_zero_iff
              (n + 1)
              (F.connectingClosedSucc
                hF Sec n z)).1 hx

        rcases hrelExact with ⟨r, hr⟩

        let a : C (n + 1) :=
          Sec.section (n + 1) z -
            (r : C (n + 1))

        have haClosed :
            A.d (n + 1) a = 0 := by
          unfold a
          rw [map_sub]
          have hrv :
              A.d (n + 1)
                  (r : C (n + 1))
                =
              A.d (n + 1)
                (Sec.section (n + 1) z) := by
            have hv :=
              congrArg Subtype.val hr
            exact hv
          rw [hrv]
          exact sub_self _

        let az : A.Closed (n + 1) :=
          ⟨a, haClosed⟩

        refine
          ⟨A.classOfClosedSucc n az, ?_⟩

        rw [F.hSuccMap_classOfClosed]

        apply congrArg (B.classOfClosedSucc n)
        apply Subtype.ext

        change
          F.map (n + 1) a =
            (z : D (n + 1))

        unfold a
        rw [map_sub]
        rw [Sec.map_section]
        rw [r.2]
        simp

end GradedLinearTransport
end CausalGeometry
