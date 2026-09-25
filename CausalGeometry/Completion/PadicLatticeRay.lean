import CausalGeometry.Completion.RankTwoLattice
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic

namespace CausalGeometry

namespace PadicLattice

variable (p : ℕ) [Fact p.Prime]

abbrev O := ℤ_[p]
abbrev K := ℚ_[p]

/-- Standard diagonal embedding
(a,b) |-> (p^n a,b) from Z_p^2 into Q_p^2. -/
def diagonalMap
    (n : ℕ) :
    (O p × O p) →ₗ[O p]
      (K p × K p) where
  toFun := fun x =>
    (((p : K p) ^ n) *
        algebraMap (O p) (K p) x.1,
      algebraMap (O p) (K p) x.2)
  map_add' := by
    intro x y
    ext <;> simp [mul_add]
  map_smul' := by
    intro a x
    ext
    · simp [mul_assoc, mul_left_comm,
        mul_comm]
    · simp

@[simp] theorem diagonalMap_apply
    (n : ℕ)
    (x : O p × O p) :
    diagonalMap p n x =
      (((p : K p) ^ n) *
          algebraMap (O p) (K p) x.1,
        algebraMap (O p) (K p) x.2) :=
  rfl

/-- The p^n-diagonal lattice. -/
def diagonalLattice
    (n : ℕ) :
    RankTwoLattice (O p) (K p) where
  carrier :=
    LinearMap.range (diagonalMap p n)
  fg := by
    rw [LinearMap.range_eq_map]
    exact
      Submodule.FG.map _
        (Module.Finite.fg_top :
          (⊤ : Submodule
            (O p) (O p × O p)).FG)
  spans := by
    apply top_unique
    intro x hx
    rcases x with ⟨a, b⟩
    let e1 : K p × K p := (1, 0)
    let e2 : K p × K p := (0, 1)
    have hpK :
        (p : K p) ≠ 0 := by
      exact_mod_cast
        (Fact.out : Nat.Prime p).ne_zero
    have hpow :
        (p : K p) ^ n ≠ 0 :=
      pow_ne_zero n hpK
    have he1scaled :
        (((p : K p) ^ n), 0) ∈
          LinearMap.range
            (diagonalMap p n) := by
      refine ⟨(1, 0), ?_⟩
      ext <;> simp [diagonalMap]
    have he2 :
        e2 ∈
          LinearMap.range
            (diagonalMap p n) := by
      refine ⟨(0, 1), ?_⟩
      ext <;> simp [diagonalMap, e2]
    have hs1scaled :
        (((p : K p) ^ n), 0) ∈
          Submodule.span (K p)
            (LinearMap.range
              (diagonalMap p n) :
              Set (K p × K p)) :=
      Submodule.subset_span he1scaled
    have hs2 :
        e2 ∈
          Submodule.span (K p)
            (LinearMap.range
              (diagonalMap p n) :
              Set (K p × K p)) :=
      Submodule.subset_span he2
    have he1 :
        e1 ∈
          Submodule.span (K p)
            (LinearMap.range
              (diagonalMap p n) :
              Set (K p × K p)) := by
      have hsmul :=
        Submodule.smul_mem
          (Submodule.span (K p)
            (LinearMap.range
              (diagonalMap p n) :
              Set (K p × K p)))
          (((p : K p) ^ n)⁻¹)
          hs1scaled
      simpa [e1, hpow] using hsmul
    have hdecomp :
        (a, b) =
          a • e1 + b • e2 := by
      ext <;> simp [e1, e2]
    rw [hdecomp]
    exact
      Submodule.add_mem _
        (Submodule.smul_mem _ a he1)
        (Submodule.smul_mem _ b hs2)

/-- Level zero is the standard Z_p^2 lattice. -/
@[simp] theorem diagonalLattice_zero_carrier :
    (diagonalLattice p 0).carrier =
      LinearMap.range
        (fun x : O p × O p =>
          (algebraMap (O p) (K p) x.1,
           algebraMap (O p) (K p) x.2) : 
          (O p × O p) →ₗ[O p]
            (K p × K p)) := by
  ext x
  constructor <;> intro hx
  · rcases hx with ⟨y, rfl⟩
    exact ⟨y, by
      ext <;> simp [diagonalMap]⟩
  · rcases hx with ⟨y, rfl⟩
    exact ⟨y, by
      ext <;> simp [diagonalMap]⟩

/-- The diagonal ray is nested: L_(n+1) is an O-submodule of L_n. -/
theorem diagonalLattice_succ_le
    (n : ℕ) :
    (diagonalLattice p (n + 1)).carrier ≤
      (diagonalLattice p n).carrier := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  rcases y with ⟨a, b⟩
  refine
    ⟨((p : O p) * a, b), ?_⟩
  ext
  · simp [diagonalMap, pow_succ,
      mul_assoc]
  · simp [diagonalMap]

/-- Every step of the ray gives an oriented lattice inclusion independent of
any quotient-cardinality theorem. -/
structure RayStep (n : ℕ) : Prop where
  le :
    (diagonalLattice p (n + 1)).carrier ≤
      (diagonalLattice p n).carrier

def rayStep
    (n : ℕ) :
    RayStep p n :=
  ⟨diagonalLattice_succ_le p n⟩

/-- The residue map Z_p -> Z/pZ is the expected coordinate quotient controlling
one step of the diagonal ray. -/
def residue :
    O p →+* ZMod p :=
  PadicInt.toZMod

theorem residue_surjective :
    Function.Surjective
      (residue p) :=
  ZMod.ringHom_surjective
    (residue p)

theorem residue_kernel :
    RingHom.ker (residue p) =
      Ideal.span {(p : O p)} :=
  PadicInt.ker_toZMod

/-- The residue field at one diagonal step has exactly p elements. -/
theorem residue_natCard :
    Nat.card (ZMod p) = p := by
  simpa using Nat.card_zmod p

end PadicLattice
end CausalGeometry
