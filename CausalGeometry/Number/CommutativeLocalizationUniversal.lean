import CausalGeometry.Number.CommutativeLocalizationMonoid
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
  rcases a with ⟨a, s⟩
  refine Quotient.inductionOn y ?_
  intro b
  rcases b with ⟨b, t⟩
  change
    realize f (mk (S := S) a s * mk b t) =
      realize f (mk a s) * realize f (mk b t)
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
  change mk (S := S) (s : α) 1 * mk 1 s = 1
  rw [mk_mul_mk]
  apply mk_eq_mk_of_cross
  simp

@[simp] theorem inverse_mul_denominator
    (s : S) :
    denominatorInverse s * mk (S := S) (s : α) 1 = 1 := by
  change mk (S := S) 1 s * mk (s : α) 1 = 1
  rw [mk_mul_mk]
  apply mk_eq_mk_of_cross
  simp [mul_comm]

@[simp] theorem realize_denominatorInverse
    (f : α →* G) (s : S) :
    realize f (denominatorInverse s) =
      (f (s : α))⁻¹ := by
  simp [denominatorInverse, realize_mk]


/-- The target realization is a monoid morphism after the quotient laws have
been packaged. -/
def realizeHom
    (f : α →* G) :
    CommFraction S →* G where
  toFun := realize f
  map_one' := realize_one f
  map_mul' := realize_mul f

@[simp] theorem realizeHom_apply
    (f : α →* G) (x : CommFraction S) :
    realizeHom f x = realize f x := rfl

/-- Canonical embedding of the original causal multiplicative sector into
its commutative fraction quotient. -/
def ofElementHom :
    α →* CommFraction S where
  toFun := ofElement
  map_one' := rfl
  map_mul' := by
    intro a b
    exact ofElement_mul a b

/-- Every presented fraction is the source numerator multiplied by the inverse
presentation of its selected denominator. -/
theorem mk_eq_ofElement_mul_denominatorInverse
    (a : α) (s : S) :
    mk (S := S) a s =
      ofElement a * denominatorInverse s := by
  rw [mk_mul_mk]
  rfl

/-- Any monoid morphism from the fraction quotient into a group is forced to
send the denominator-inverse presentation to the inverse of the denominator
image. -/
theorem hom_denominatorInverse
    (g : CommFraction S →* G)
    (s : S) :
    g (denominatorInverse s) =
      (g (ofElement (s : α)))⁻¹ := by
  have hmul :
      g (ofElement (s : α)) *
          g (denominatorInverse s) = 1 := by
    calc
      g (ofElement (s : α)) *
          g (denominatorInverse s)
          =
        g (ofElement (s : α) * denominatorInverse s) := by
          rw [g.map_mul]
      _ = g 1 := by
        rw [denominator_mul_inverse]
      _ = 1 := g.map_one
  calc
    g (denominatorInverse s)
        =
      (g (ofElement (s : α)))⁻¹ *
        (g (ofElement (s : α)) *
          g (denominatorInverse s)) := by
            group
    _ = (g (ofElement (s : α)))⁻¹ := by
      rw [hmul]
      simp

/-- Universal uniqueness for commutative-group targets: a morphism out of the
fraction quotient is completely determined by its values on the original
source monoid. -/
theorem hom_ext_of_source
    (f : α →* G)
    (g : CommFraction S →* G)
    (hsource : ∀ a, g (ofElement a) = f a) :
    g = realizeHom f := by
  apply MonoidHom.ext
  intro x
  refine Quotient.inductionOn x ?_
  intro q
  rcases q with ⟨a, s⟩
  change g (mk (S := S) a s) =
    realizeHom f (mk a s)
  rw [mk_eq_ofElement_mul_denominatorInverse]
  rw [g.map_mul, hsource a, hom_denominatorInverse]
  rw [hsource (s : α)]
  simp [realizeHom_apply, realize_mk]

/-- Existence half of the universal property. -/
theorem realizeHom_extends
    (f : α →* G)
    (a : α) :
    realizeHom f (ofElement a) = f a := by
  simp [realizeHom_apply, realize_ofElement]

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
  rcases q with ⟨a, s⟩
  change
    realize f (mk (S := S) a s) =
      realize g (mk a s)
  simp only [realize_mk]
  rw [h a, h (s : α)]

end CausalLocalization.CommFraction
end CausalGeometry
