import CausalGeometry.Number.CommutativeLocalization

namespace CausalGeometry

universe u

namespace CausalLocalization.CommFraction

variable {α : Type u} [CancelCommMonoid α]
variable {S : Submonoid α}

/-- The cancellative commutative fraction quotient carries the expected
commutative monoid structure. The low-priority instance reuses the already
defined quotient multiplication and neutral presentation. -/
instance (priority := 100) commMonoid :
    CommMonoid (CommFraction S) where
  mul := (· * ·)
  one := 1
  mul_assoc := by
    intro x y z
    refine Quotient.inductionOn x ?_
    intro x
    rcases x with ⟨a, s⟩
    refine Quotient.inductionOn y ?_
    intro y
    rcases y with ⟨b, t⟩
    refine Quotient.inductionOn z ?_
    intro z
    rcases z with ⟨c, u⟩
    exact mk_mul_assoc a b c s t u
  one_mul := by
    intro x
    refine Quotient.inductionOn x ?_
    intro x
    rcases x with ⟨a, s⟩
    change mk (S := S) 1 1 * mk a s = mk a s
    rw [mk_mul_mk]
    simp
  mul_one := by
    intro x
    refine Quotient.inductionOn x ?_
    intro x
    rcases x with ⟨a, s⟩
    change mk (S := S) a s * mk 1 1 = mk a s
    rw [mk_mul_mk]
    simp
  mul_comm := by
    intro x y
    refine Quotient.inductionOn x ?_
    intro x
    rcases x with ⟨a, s⟩
    refine Quotient.inductionOn y ?_
    intro y
    rcases y with ⟨b, t⟩
    change mk (S := S) a s * mk b t =
      mk b t * mk a s
    rw [mk_mul_mk, mk_mul_mk]
    apply mk_eq_mk_of_cross
    simp [mul_comm]

end CausalLocalization.CommFraction
end CausalGeometry
