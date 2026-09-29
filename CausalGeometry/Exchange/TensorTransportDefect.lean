import CausalGeometry.Calculus.LinearSquareDefect
import CausalGeometry.Foundation.PairedTransform
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Tensor exchange defects with independent forward/backward transports

These are genuine tensor products, not Cartesian pairs of states. No
invertibility, Yang--Baxter, finite dimension or Hilbert structure is needed.
The map F↦F⊗F is quadratic, so no false additivity in F is asserted.
-/
namespace CausalGeometry.Exchange.TensorTransport

open scoped TensorProduct
universe u
variable {K : Type u} [CommRing K]
variable {A B C : Type*}
variable [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
variable [AddCommGroup C] [Module K C]

abbrev lift (F : A →ₗ[K] B) : A ⊗[K] A →ₗ[K] B ⊗[K] B := TensorProduct.map F F

@[simp] theorem lift_comp (F : A →ₗ[K] B) (G : B →ₗ[K] C) :
    lift (G.comp F) = (lift G).comp (lift F) := TensorProduct.map_comp G G F F

@[simp] theorem lift_id : lift (LinearMap.id : A →ₗ[K] A) = LinearMap.id :=
  TensorProduct.map_id

/-- The diagonal tensor lift has cross terms; it is not additive in F. -/
theorem lift_add (F G : A →ₗ[K] B) :
    lift (F + G) = lift F + TensorProduct.map F G + TensorProduct.map G F + lift G := by
  unfold lift
  rw [TensorProduct.map_add_left, TensorProduct.map_add_right, TensorProduct.map_add_right]
  abel

/-- D_R(F)=R_B (F⊗F) - (F⊗F) R_A. -/
def defect (R : A ⊗[K] A →ₗ[K] A ⊗[K] A)
    (T : B ⊗[K] B →ₗ[K] B ⊗[K] B) (F : A →ₗ[K] B) :=
  LinearSquare.defect R T (lift F) (lift F)

theorem defect_zero_iff (R : A ⊗[K] A →ₗ[K] A ⊗[K] A)
    (T : B ⊗[K] B →ₗ[K] B ⊗[K] B) (F : A →ₗ[K] B) :
    defect R T F = 0 ↔ T.comp (lift F) = (lift F).comp R :=
  LinearSquare.defect_eq_zero_iff _ _ _ _

/-- The planned defect composition identity, derived from the generic square. -/
theorem defect_comp (R : A ⊗[K] A →ₗ[K] A ⊗[K] A)
    (T : B ⊗[K] B →ₗ[K] B ⊗[K] B) (W : C ⊗[K] C →ₗ[K] C ⊗[K] C)
    (F : A →ₗ[K] B) (G : B →ₗ[K] C) :
    defect R W (G.comp F) =
      (defect T W G).comp (lift F) + (lift G).comp (defect R T F) := by
  unfold defect
  rw [lift_comp]
  exact LinearSquare.horizontal _ _ _ _ _ _ _

/-- Linear data forget to the unchanged structural pair. -/
def toPaired (Phi : A →ₗ[K] B) (Psi : B →ₗ[K] A) : PairedTransform A B :=
  ⟨Phi, Psi⟩

@[simp] theorem sourceRoundTrip_value (Phi : A →ₗ[K] B) (Psi : B →ₗ[K] A) (x : A) :
    (toPaired Phi Psi).sourceRoundTrip x = (Psi.comp Phi) x := rfl

@[simp] theorem targetRoundTrip_value (Phi : A →ₗ[K] B) (Psi : B →ₗ[K] A) (x : B) :
    (toPaired Phi Psi).targetRoundTrip x = (Phi.comp Psi) x := rfl

theorem sourceRoundTrip_defect (R : A ⊗[K] A →ₗ[K] A ⊗[K] A)
    (T : B ⊗[K] B →ₗ[K] B ⊗[K] B) (Phi : A →ₗ[K] B) (Psi : B →ₗ[K] A) :
    defect R R (Psi.comp Phi) =
      (defect T R Psi).comp (lift Phi) + (lift Psi).comp (defect R T Phi) :=
  defect_comp R T R Phi Psi

theorem targetRoundTrip_defect (R : A ⊗[K] A →ₗ[K] A ⊗[K] A)
    (T : B ⊗[K] B →ₗ[K] B ⊗[K] B) (Phi : A →ₗ[K] B) (Psi : B →ₗ[K] A) :
    defect T T (Phi.comp Psi) =
      (defect R T Phi).comp (lift Psi) + (lift Phi).comp (defect T R Psi) :=
  defect_comp T R T Psi Phi

/-- Tensor naturality in both directions implies zero round defect, not an identity map. -/
theorem sourceRoundTrip_zero (R : A ⊗[K] A →ₗ[K] A ⊗[K] A)
    (T : B ⊗[K] B →ₗ[K] B ⊗[K] B) (Phi : A →ₗ[K] B) (Psi : B →ₗ[K] A)
    (hPhi : defect R T Phi = 0) (hPsi : defect T R Psi = 0) :
    defect R R (Psi.comp Phi) = 0 := by
  rw [sourceRoundTrip_defect, hPhi, hPsi]
  ext x
  simp

/-- Pointwise compatible tensor states, with no unproved process-invariance claim. -/
def compatibleDomain (R : A ⊗[K] A →ₗ[K] A ⊗[K] A)
    (T : B ⊗[K] B →ₗ[K] B ⊗[K] B) (F : A →ₗ[K] B) : Submodule K (A ⊗[K] A) :=
  (defect R T F).ker

end CausalGeometry.Exchange.TensorTransport
