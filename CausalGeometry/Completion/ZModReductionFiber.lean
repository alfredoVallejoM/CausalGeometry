import CausalGeometry.Completion.ZModLocalTower
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset.Basic

namespace CausalGeometry

namespace zmodPrimeLocalTower

variable (p : ℕ) [Fact p.Prime]

/-- Additive reduction underlying the ring-hom drop. -/
def dropAdd (n : ℕ) :
    ZMod (p ^ (n + 2)) →+
      ZMod (p ^ (n + 1)) :=
  (drop p n).toAddMonoidHom

theorem dropAdd_surjective (n : ℕ) :
    Function.Surjective (dropAdd p n) :=
  drop_surjective p n

/-- The additive kernel of one modular restriction step has exactly p states. -/
theorem dropAdd_kernel_natCard (n : ℕ) :
    Nat.card (dropAdd p n).ker = p := by
  have h :=
    AddMonoidHom.card_ker_mul_card_of_surjective
      (f := dropAdd p n)
      (dropAdd_surjective p n)
  have h' :
      Nat.card (dropAdd p n).ker *
          p ^ (n + 1) =
        p * p ^ (n + 1) := by
    simpa [dropAdd, Nat.card_zmod, pow_succ,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  exact Nat.mul_right_cancel h'

/-- One explicit representative of every reduction fiber exists because drop
is surjective. -/
noncomputable def fiberRepresentative
    (n : ℕ)
    (y : ZMod (p ^ (n + 1))) :
    ZMod (p ^ (n + 2)) :=
  Classical.choose (dropAdd_surjective p n y)

@[simp] theorem fiberRepresentative_maps
    (n : ℕ)
    (y : ZMod (p ^ (n + 1))) :
    dropAdd p n (fiberRepresentative p n y) = y :=
  Classical.choose_spec (dropAdd_surjective p n y)

/-- Each nonempty fiber of the modular reduction is equivalent to the additive
kernel. -/
noncomputable def fiberEquivKernel
    (n : ℕ)
    (y : ZMod (p ^ (n + 1))) :
    {x : ZMod (p ^ (n + 2)) // dropAdd p n x = y} ≃
      (dropAdd p n).ker := by
  let a := fiberRepresentative p n y
  have ha : dropAdd p n a = y :=
    fiberRepresentative_maps p n y
  let E :=
    AddMonoidHom.fiberEquivKer (dropAdd p n) a
  have hfiber :
      {x : ZMod (p ^ (n + 2)) | dropAdd p n x = y} =
        (dropAdd p n) ⁻¹' {dropAdd p n a} := by
    ext x
    simp [ha]
  exact (Equiv.setCongr hfiber).trans E

/-- Every ring-reduction fiber contains exactly p points. -/
theorem drop_fiber_natCard
    (n : ℕ)
    (y : ZMod (p ^ (n + 1))) :
    Nat.card
        {x : ZMod (p ^ (n + 2)) //
          drop p n x = y} =
      p := by
  have hEq :
      {x : ZMod (p ^ (n + 2)) //
        drop p n x = y} =
      {x : ZMod (p ^ (n + 2)) //
        dropAdd p n x = y} := rfl
  rw [hEq, ← Nat.card_congr (fiberEquivKernel p n y)]
  exact dropAdd_kernel_natCard p n

end zmodPrimeLocalTower
end CausalGeometry
