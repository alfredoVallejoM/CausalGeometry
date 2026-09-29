import CausalGeometry.Calculus.LinearSquareDefect
import CausalGeometry.Calculus.PairedCochainTransport

/-!
# Compatibility of the existing graded defect with its own differential

The old defect and transport are consumed unchanged. On a closed cochain the
raw differential defect is exact; it is NOT by itself a nonzero cohomology
obstruction. No class is renamed Sha, curvature or global obstruction here.
-/
namespace CausalGeometry.GradedLinearTransport

universe u v w
variable {K : Type u} [Field K] {C : Nat → Type v} {D : Nat → Type w}
variable [∀ n, AddCommGroup (C n)] [∀ n, Module K (C n)]
variable [∀ n, AddCommGroup (D n)] [∀ n, Module K (D n)]
variable {A : GradedCausalCochainComplex K C} {B : GradedCausalCochainComplex K D}

/-- Exact comparison with the historical producer, rather than a replacement. -/
theorem defect_is_square (F : GradedLinearTransport A B) (n : Nat) :
    F.defect n = LinearSquare.defect (A.d n) (B.d n) (F.map n) (F.map (n+1)) := rfl

/-- d_B D_n + D_(n+1) d_A = 0 follows from the two old square-zero laws. -/
theorem differential_defect_identity (F : GradedLinearTransport A B) (n : Nat) :
    (B.d (n+1)).comp (F.defect n) + (F.defect (n+1)).comp (A.d n) = 0 := by
  ext x
  simp [defect, GradedCausalCochainComplex.d_d]

/-- A closed input has defect d_B(Fx), not a new nonzero cohomology class. -/
theorem defect_on_closed (F : GradedLinearTransport A B) (n : Nat)
    (x : C n) (hx : A.d n x = 0) : F.defect n x = B.d n (F.map n x) := by
  simp [defect, hx]

theorem defect_closed_is_exact (F : GradedLinearTransport A B) (n : Nat)
    (x : C n) (hx : A.d n x = 0) :
    F.defect n x ∈ B.ExactSucc n := by
  exact ⟨F.map n x, (defect_on_closed F n x hx).symm⟩

theorem defect_closed_is_closed (F : GradedLinearTransport A B) (n : Nat)
    (x : C n) (hx : A.d n x = 0) : B.d (n+1) (F.defect n x) = 0 := by
  rw [defect_on_closed F n x hx]
  exact B.d_d n (F.map n x)

/-- The actual existing cohomology quotient sends this exact defect to zero. -/
theorem defect_closed_class_zero (F : GradedLinearTransport A B) (n : Nat)
    (x : C n) (hx : A.d n x = 0) :
    B.classOfClosedSucc n
      ⟨F.defect n x, defect_closed_is_closed F n x hx⟩ = 0 := by
  apply (B.classOfClosedSucc_eq_zero_iff n _).mpr
  exact defect_closed_is_exact F n x hx

/-- Boundaries obey the signed differential relation; no cochain-map law is required. -/
theorem defect_on_boundary (F : GradedLinearTransport A B) (n : Nat) (x : C n) :
    F.defect (n+1) (A.d n x) = - B.d (n+1) (F.defect n x) := by
  simp [defect, GradedCausalCochainComplex.d_d]

end CausalGeometry.GradedLinearTransport
