import CausalGeometry.Calculus.GeneralTensor
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

namespace CausalGeometry

universe u v

open scoped BigOperators

/-- Finite coordinate realization of a mixed (p,q)-tensor.

A coordinate tensor is a scalar table on p contravariant and q covariant
finite index tuples.  This is a concrete computational realization, not yet a
basis-independent identification with an intrinsic TensorProduct carrier. -/
abbrev CoordinateTensor
    (K : Type u)
    (ι : Type v)
    (p q : ℕ) :=
  (Fin p → ι) →
    (Fin q → ι) →
      K

namespace CoordinateTensor

variable
    {K : Type u}
    {ι : Type v}
    [Field K]
    [Fintype ι]

/-- Restrict a tuple on p+r slots to its first p coordinates. -/
def leftTuple
    {p r : ℕ}
    (a : Fin (p + r) → ι) :
    Fin p → ι :=
  fun i => a (Fin.castAdd r i)

/-- Restrict a tuple on p+r slots to its final r coordinates. -/
def rightTuple
    {p r : ℕ}
    (a : Fin (p + r) → ι) :
    Fin r → ι :=
  fun i => a (Fin.natAdd p i)

/-- Componentwise tensor product by concatenating contravariant and covariant
index tuples. -/
def tensor
    (p q r s : ℕ) :
    CoordinateTensor K ι p q →ₗ[K]
      CoordinateTensor K ι r s →ₗ[K]
        CoordinateTensor K ι (p + r) (q + s) where

  toFun := fun x =>
    { toFun := fun y a b =>
        x (leftTuple a) (leftTuple b) *
          y (rightTuple a) (rightTuple b)

      map_add' := by
        intro y z
        funext a b
        simp [mul_add]

      map_smul' := by
        intro c y
        funext a b
        simp [mul_assoc] }

  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    funext a b
    simp [add_mul]

  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro y
    funext a b
    simp [mul_assoc, mul_comm, mul_left_comm]

/-- Contract the final contravariant slot with the final covariant slot by a
finite diagonal sum. -/
def contract
    (p q : ℕ) :
    CoordinateTensor K ι (p + 1) (q + 1) →ₗ[K]
      CoordinateTensor K ι p q where

  toFun := fun x a b =>
    ∑ i : ι,
      x (Fin.snoc a i)
        (Fin.snoc b i)

  map_add' := by
    intro x y
    funext a b
    simp [Finset.sum_add_distrib]

  map_smul' := by
    intro c x
    funext a b
    simp [Finset.mul_sum]

/-- Reindex contravariant slots by one finite permutation. -/
def permuteContravariant
    (p q : ℕ)
    (σ : Equiv (Fin p) (Fin p)) :
    CoordinateTensor K ι p q ≃ₗ[K]
      CoordinateTensor K ι p q where

  toFun := fun x a b =>
    x (a ∘ σ) b

  invFun := fun x a b =>
    x (a ∘ σ.symm) b

  left_inv := by
    intro x
    funext a b
    congr 2
    funext i
    simp

  right_inv := by
    intro x
    funext a b
    congr 2
    funext i
    simp

  map_add' := by
    intro x y
    rfl

  map_smul' := by
    intro c x
    rfl

/-- Reindex covariant slots by one finite permutation. -/
def permuteCovariant
    (p q : ℕ)
    (σ : Equiv (Fin q) (Fin q)) :
    CoordinateTensor K ι p q ≃ₗ[K]
      CoordinateTensor K ι p q where

  toFun := fun x a b =>
    x a (b ∘ σ)

  invFun := fun x a b =>
    x a (b ∘ σ.symm)

  left_inv := by
    intro x
    funext a b
    congr 2
    funext i
    simp

  right_inv := by
    intro x
    funext a b
    congr 2
    funext i
    simp

  map_add' := by
    intro x y
    rfl

  map_smul' := by
    intro c x
    rfl

/-- Concrete realization of the abstract arbitrary-rank causal tensor
interface. -/
def calculus :
    GeneralCausalTensorCalculus
      K
      (CoordinateTensor K ι) where

  tensor :=
    tensor

  contract :=
    contract

  permuteContravariant :=
    permuteContravariant

  permuteCovariant :=
    permuteCovariant

@[simp] theorem tensor_apply
    {p q r s : ℕ}
    (x : CoordinateTensor K ι p q)
    (y : CoordinateTensor K ι r s)
    (a : Fin (p + r) → ι)
    (b : Fin (q + s) → ι) :
    tensor p q r s x y a b =
      x (leftTuple a) (leftTuple b) *
        y (rightTuple a) (rightTuple b) :=
  rfl

@[simp] theorem contract_apply
    {p q : ℕ}
    (x :
      CoordinateTensor K ι
        (p + 1) (q + 1))
    (a : Fin p → ι)
    (b : Fin q → ι) :
    contract p q x a b =
      ∑ i : ι,
        x (Fin.snoc a i)
          (Fin.snoc b i) :=
  rfl

/-- Tensoring with a zero component table annihilates the product on the
left. -/
@[simp] theorem tensor_zero_left
    (p q r s : ℕ)
    (y : CoordinateTensor K ι r s) :
    tensor p q r s
        (0 : CoordinateTensor K ι p q)
        y
      =
    0 := by
  exact
    map_zero
      ((tensor p q r s).flip y)

/-- Tensoring with zero on the right also annihilates the product. -/
@[simp] theorem tensor_zero_right
    (p q r s : ℕ)
    (x : CoordinateTensor K ι p q) :
    tensor p q r s x
        (0 : CoordinateTensor K ι r s)
      =
    0 := by
  exact
    map_zero (tensor p q r s x)

/-- Contraction is linear and sends zero to zero. -/
@[simp] theorem contract_zero
    (p q : ℕ) :
    contract (K := K) (ι := ι) p q
        (0 :
          CoordinateTensor K ι
            (p + 1) (q + 1))
      =
    0 :=
  map_zero _

/-- Identity slot permutations act trivially. -/
@[simp] theorem permuteContravariant_refl
    (p q : ℕ)
    (x : CoordinateTensor K ι p q) :
    permuteContravariant p q
        (Equiv.refl (Fin p)) x
      =
    x := by
  rfl

@[simp] theorem permuteCovariant_refl
    (p q : ℕ)
    (x : CoordinateTensor K ι p q) :
    permuteCovariant p q
        (Equiv.refl (Fin q)) x
      =
    x := by
  rfl

end CoordinateTensor
end CausalGeometry
