import CausalGeometry.Number.CommutativeLocalization
import Mathlib.Tactic

namespace CausalGeometry

universe u v

namespace CausalLocalization.CommFraction

variable {α : Type u} [CancelCommMonoid α]
variable {S : Submonoid α}
variable {G : Type v} [CommGroup G]

/-- Evaluation of a cancellative commutative causal fraction in a commutative
group target. -/
def realize
    (f : α →* G) :
    CommFraction S → G :=
  Quotient.lift
    (fun x => RightFraction.realize f x)
    (by
      intro x y h
      unfold FractionRel at h
      have hmap :
          f x.numerator * f (y.denominator : α) =
            f y.numerator * f (x.denominator : α) := by
        simpa using congrArg (fun z => f z) h
      unfold RightFraction.realize
      calc
        f x.numerator * (f (x.denominator : α))⁻¹
            =
          (f x.numerator * f (y.denominator : α)) *
            ((f (x.denominator : α))⁻¹ *
              (f (y.denominator : α))⁻¹) := by
                group
        _ =
          (f y.numerator * f (x.denominator : α)) *
            ((f (x.denominator : α))⁻¹ *
              (f (y.denominator : α))⁻¹) := by
                rw [hmap]
        _ =
          f y.numerator * (f (y.denominator : α))⁻¹ := by
                group)

@[simp] theorem realize_mk
    (f : α →* G)
    (a : α) (s : S) :
    realize f (mk (S := S) a s) =
      f a * (f (s : α))⁻¹ := rfl

@[simp] theorem realize_ofElement
    (f : α →* G)
    (a : α) :
    realize f (ofElement (S := S) a) = f a := by
  simp [ofElement, realize_mk]

/-- The quotient multiplication is sent to target multiplication. -/
theorem realize_mul
    (f : α →* G)
    (x y : CommFraction S) :
    realize f (x * y) =
      realize f x * realize f y := by
  refine Quotient.inductionOn x ?_
  intro a
  refine Quotient.inductionOn y ?_
  intro b
  simp only [mk_mul_mk, realize_mk]
  simp
  group

@[simp] theorem realize_one
    (f : α →* G) :
    realize f (1 : CommFraction S) = 1 := by
  simp [one_eq_mk, realize_mk]

/-- Every selected denominator acquires a two-sided inverse already inside the
fraction quotient. -/
def denominatorInverse (s : S) :
    CommFraction S :=
  mk 1 s

@[simp] theorem denominator_mul_inverse
    (s : S) :
    mk (S := S) (s : α) 1 * denominatorInverse s = 1 := by
  rw [mk_mul_mk]
  apply mk_eq_mk_of_cross
  simp [denominatorInverse]

@[simp] theorem inverse_mul_denominator
    (s : S) :
    denominatorInverse s * mk (S := S) (s : α) 1 = 1 := by
  rw [mk_mul_mk]
  apply mk_eq_mk_of_cross
  simp [denominatorInverse, mul_comm]

@[simp] theorem realize_denominatorInverse
    (f : α →* G) (s : S) :
    realize f (denominatorInverse s) =
      (f (s : α))⁻¹ := by
  simp [denominatorInverse, realize_mk]

/-- Two target evaluations induced by the same source morphism agree on every
fraction presentation. This is the extensional uniqueness available before
packaging the full categorical universal property. -/
theorem realize_eq_of_same_source
    (f g : α →* G)
    (h : ∀ a, f a = g a)
    (x : CommFraction S) :
    realize f x = realize g x := by
  refine Quotient.inductionOn x ?_
  intro q
  simp only [realize_mk]
  rw [h q.numerator, h (q.denominator : α)]

end CausalLocalization.CommFraction
end CausalGeometry
