import CausalGeometry.Exchange.Reversible

/-!
# Reversible coherence defects

The convention f ≫ g means first f, then g. Thus defect P Q is the usual
Q⁻¹ ∘ P. No interpretation as geometric curvature or correlative restriction
is asserted by naming this loop.
-/
namespace CausalGeometry.Exchange.Reversible

open CategoryTheory
universe uC vC uD vD
variable {C : Type uC} [Groupoid.{vC} C]
variable {D : Type uD} [Groupoid.{vD} D]

/-- The discrepancy between two parallel invertible transformations. -/
def defect {X Y : C} (P Q : X ⟶ Y) : X ⟶ X := P ≫ Groupoid.inv Q

theorem defect_eq_id_iff {X Y : C} (P Q : X ⟶ Y) :
    defect P Q = 𝟙 X ↔ P = Q := by
  constructor
  · intro h
    have hh := congrArg (fun a : X ⟶ X => a ≫ Q) h
    simpa [defect, Category.assoc] using hh
  · intro h
    subst P
    exact Groupoid.comp_inv Q

@[simp] theorem defect_self {X Y : C} (P : X ⟶ Y) :
    defect P P = 𝟙 X := Groupoid.comp_inv P

/-- The target change cancels; the source change acts by conjugation. -/
theorem defect_change_presentation {X' X Y Y' : C}
    (a : X' ⟶ X) (P Q : X ⟶ Y) (b : Y ⟶ Y') :
    defect (a ≫ P ≫ b) (a ≫ Q ≫ b) =
      a ≫ defect P Q ≫ Groupoid.inv a := by
  simp [defect, Groupoid.inv_eq_inv, Category.assoc]

/-- Swapping the two comparison paths inverts the discrepancy. -/
theorem defect_swap {X Y : C} (P Q : X ⟶ Y) :
    defect Q P = Groupoid.inv (defect P Q) := by
  simp [defect, Groupoid.inv_eq_inv]

@[simp] theorem map_defect (F : C ⥤ D) {X Y : C} (P Q : X ⟶ Y) :
    F.map (defect P Q) = defect (F.map P) (F.map Q) := by
  simp [defect, Groupoid.inv_eq_inv]

/-- A separating realization proves nontriviality in the source. -/
theorem defect_ne_id_of_separated (F : C ⥤ D) {X Y : C} (P Q : X ⟶ Y)
    (h : F.map P ≠ F.map Q) : defect P Q ≠ 𝟙 X := by
  intro h0
  exact h (congrArg (fun f => F.map f) ((defect_eq_id_iff P Q).mp h0))

/-- An arbitrary observer need not reflect trivial defects. -/
theorem reflects_defect_of_faithful (F : C ⥤ D) [F.Faithful]
    {X Y : C} (P Q : X ⟶ Y) :
    defect (F.map P) (F.map Q) = 𝟙 (F.obj X) ↔ defect P Q = 𝟙 X := by
  rw [defect_eq_id_iff, defect_eq_id_iff]
  exact ⟨F.map_injective, congrArg (fun f => F.map f)⟩

/-- Two individually invertible directions need not be inverse to one another. -/
theorem roundTrip_eq_id_iff {X Y : C} (Phi : X ⟶ Y) (Psi : Y ⟶ X) :
    Phi ≫ Psi = 𝟙 X ↔ Psi = Groupoid.inv Phi := by
  constructor
  · intro h
    apply (cancel_epi Phi).mp
    exact h.trans (Groupoid.comp_inv Phi).symm
  · intro h
    rw [h]
    exact Groupoid.comp_inv Phi

end CausalGeometry.Exchange.Reversible
