import CausalGeometry.Number.OreLocalization

namespace CausalGeometry

universe u v

namespace CausalLocalization

variable {α : Type u} [Monoid α]

/-- A certified right calculus of fractions over a denominator submonoid.

The right Ore condition supplies common-denominator squares, but it is not by
itself promoted to a localization quotient.  This structure records the extra
evidence actually needed: an equivalence relation, a representative
multiplication compatible with it, monoid coherence, denominator inversion,
and a normal-form theorem. -/
structure RightFractionCalculus (S : Submonoid α) where
  rel : RightFraction S → RightFraction S → Prop
  rel_equivalence : Equivalence rel

  mulRep : RightFraction S → RightFraction S → RightFraction S

  /-- Every chosen representative product is certified by some genuine right
  Ore square.  The calculus may choose different witnesses for equivalent
  representatives. -/
  mul_from_ore :
    ∀ x y, ∃ w : RightOreSquare S y.numerator x.denominator,
      rel (mulRep x y) (RightFraction.mulWith x y w)

  mul_respects :
    ∀ {x x' y y'}, rel x x' → rel y y' →
      rel (mulRep x y) (mulRep x' y')

  mul_assoc :
    ∀ x y z,
      rel (mulRep (mulRep x y) z)
        (mulRep x (mulRep y z))

  one_mul :
    ∀ x, rel (mulRep (RightFraction.ofElement (S := S) 1) x) x
  mul_one :
    ∀ x, rel (mulRep x (RightFraction.ofElement (S := S) 1)) x

  source_mul :
    ∀ a b,
      rel
        (mulRep
          (RightFraction.ofElement (S := S) a)
          (RightFraction.ofElement (S := S) b))
        (RightFraction.ofElement (S := S) (a * b))

  denominator_right_inverse :
    ∀ s : S,
      rel
        (mulRep
          (RightFraction.ofElement (S := S) (s : α))
          ⟨1, s⟩)
        (RightFraction.ofElement (S := S) 1)

  denominator_left_inverse :
    ∀ s : S,
      rel
        (mulRep
          ⟨1, s⟩
          (RightFraction.ofElement (S := S) (s : α)))
        (RightFraction.ofElement (S := S) 1)

  /-- Every right-fraction presentation is equivalent to source numerator
  times the explicit inverse presentation of its denominator. -/
  normalForm :
    ∀ x,
      rel x
        (mulRep
          (RightFraction.ofElement (S := S) x.numerator)
          ⟨1, x.denominator⟩)

namespace RightFractionCalculus

variable {S : Submonoid α}
variable (C : RightFractionCalculus S)

def setoid : Setoid (RightFraction S) where
  r := C.rel
  iseqv := C.rel_equivalence

/-- The actual right localization carrier determined by one certified calculus. -/
def QuotientType :=
  Quotient C.setoid

def mk (x : RightFraction S) : C.QuotientType :=
  Quotient.mk _ x

def ofElement (a : α) : C.QuotientType :=
  C.mk (RightFraction.ofElement (S := S) a)

def denominatorInverse (s : S) : C.QuotientType :=
  C.mk ⟨1, s⟩

def mul (x y : C.QuotientType) : C.QuotientType :=
  Quotient.lift₂
    (fun a b => C.mk (C.mulRep a b))
    (by
      intro a a' b b' ha hb
      apply Quotient.sound
      exact C.mul_respects ha hb)
    x y

instance : Mul C.QuotientType := ⟨C.mul⟩

def one : C.QuotientType :=
  C.ofElement 1

instance : One C.QuotientType := ⟨C.one⟩

@[simp] theorem mk_mul_mk
    (x y : RightFraction S) :
    C.mk x * C.mk y = C.mk (C.mulRep x y) := rfl

@[simp] theorem one_eq :
    (1 : C.QuotientType) = C.ofElement 1 := rfl

theorem mk_eq_mk_of_rel
    {x y : RightFraction S}
    (h : C.rel x y) :
    C.mk x = C.mk y :=
  Quotient.sound h

theorem ofElement_mul
    (a b : α) :
    C.ofElement a * C.ofElement b =
      C.ofElement (a * b) := by
  change
    C.mk
        (C.mulRep
          (RightFraction.ofElement (S := S) a)
          (RightFraction.ofElement (S := S) b)) =
      C.mk (RightFraction.ofElement (S := S) (a * b))
  exact Quotient.sound (C.source_mul a b)

theorem one_mul_quot
    (x : C.QuotientType) :
    1 * x = x := by
  refine Quotient.inductionOn x ?_
  intro x
  change
    C.mk
        (C.mulRep
          (RightFraction.ofElement (S := S) 1) x) =
      C.mk x
  exact Quotient.sound (C.one_mul x)

theorem mul_one_quot
    (x : C.QuotientType) :
    x * 1 = x := by
  refine Quotient.inductionOn x ?_
  intro x
  change
    C.mk
        (C.mulRep x
          (RightFraction.ofElement (S := S) 1)) =
      C.mk x
  exact Quotient.sound (C.mul_one x)

theorem mul_assoc_quot
    (x y z : C.QuotientType) :
    (x * y) * z = x * (y * z) := by
  refine Quotient.inductionOn x ?_
  intro x
  refine Quotient.inductionOn y ?_
  intro y
  refine Quotient.inductionOn z ?_
  intro z
  change
    C.mk (C.mulRep (C.mulRep x y) z) =
      C.mk (C.mulRep x (C.mulRep y z))
  exact Quotient.sound (C.mul_assoc x y z)

instance : Monoid C.QuotientType where
  mul := (· * ·)
  one := 1
  mul_assoc := C.mul_assoc_quot
  one_mul := C.one_mul_quot
  mul_one := C.mul_one_quot

/-- Canonical source embedding. -/
def sourceHom : α →* C.QuotientType where
  toFun := C.ofElement
  map_one' := rfl
  map_mul' := C.ofElement_mul

@[simp] theorem sourceHom_apply (a : α) :
    C.sourceHom a = C.ofElement a := rfl

@[simp] theorem denominator_mul_inverse
    (s : S) :
    C.sourceHom (s : α) * C.denominatorInverse s = 1 := by
  change
    C.mk
        (C.mulRep
          (RightFraction.ofElement (S := S) (s : α))
          ⟨1, s⟩) =
      C.mk (RightFraction.ofElement (S := S) 1)
  exact Quotient.sound (C.denominator_right_inverse s)

@[simp] theorem inverse_mul_denominator
    (s : S) :
    C.denominatorInverse s * C.sourceHom (s : α) = 1 := by
  change
    C.mk
        (C.mulRep
          ⟨1, s⟩
          (RightFraction.ofElement (S := S) (s : α))) =
      C.mk (RightFraction.ofElement (S := S) 1)
  exact Quotient.sound (C.denominator_left_inverse s)

/-- Normal form inside the quotient. -/
theorem mk_normalForm
    (x : RightFraction S) :
    C.mk x =
      C.sourceHom x.numerator *
        C.denominatorInverse x.denominator := by
  change
    C.mk x =
      C.mk
        (C.mulRep
          (RightFraction.ofElement (S := S) x.numerator)
          ⟨1, x.denominator⟩)
  exact Quotient.sound (C.normalForm x)

/-- Evaluation of a right localization in a group target.  Respect for the
chosen quotient relation and multiplication are explicit obligations. -/
structure GroupRealization
    (G : Type v) [Group G]
    (f : α →* G) where
  respects :
    ∀ {x y}, C.rel x y →
      RightFraction.realize f x =
        RightFraction.realize f y
  mul_compatible :
    ∀ x y,
      RightFraction.realize f (C.mulRep x y) =
        RightFraction.realize f x *
          RightFraction.realize f y

namespace GroupRealization

variable {G : Type v} [Group G]
variable {f : α →* G}
variable (R : C.GroupRealization G f)

def realize : C.QuotientType → G :=
  Quotient.lift
    (RightFraction.realize f)
    (by
      intro x y h
      exact R.respects h)

@[simp] theorem realize_mk
    (x : RightFraction S) :
    R.realize (C.mk x) =
      RightFraction.realize f x := rfl

@[simp] theorem realize_source
    (a : α) :
    R.realize (C.sourceHom a) = f a := by
  simp [sourceHom, ofElement, realize_mk,
    RightFraction.realize_ofElement]

@[simp] theorem realize_one :
    R.realize (1 : C.QuotientType) = 1 := by
  simpa [one, ofElement] using R.realize_source (C := C) 1

theorem realize_mul
    (x y : C.QuotientType) :
    R.realize (x * y) =
      R.realize x * R.realize y := by
  refine Quotient.inductionOn x ?_
  intro x
  refine Quotient.inductionOn y ?_
  intro y
  exact R.mul_compatible x y

def realizeHom : C.QuotientType →* G where
  toFun := R.realize
  map_one' := R.realize_one
  map_mul' := R.realize_mul

@[simp] theorem realizeHom_source
    (a : α) :
    R.realizeHom (C.sourceHom a) = f a :=
  R.realize_source a

@[simp] theorem realize_denominatorInverse
    (s : S) :
    R.realizeHom (C.denominatorInverse s) =
      (f (s : α))⁻¹ := by
  change RightFraction.realize f (⟨1, s⟩ : RightFraction S) =
    (f (s : α))⁻¹
  simp [RightFraction.realize]

/-- Universal uniqueness: every monoid morphism into a group is determined by
its restriction to the source because every quotient class has the certified
right-fraction normal form. -/
theorem hom_ext_of_source
    (g : C.QuotientType →* G)
    (hsource : ∀ a, g (C.sourceHom a) = f a) :
    g = R.realizeHom := by
  apply MonoidHom.ext
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  rw [C.mk_normalForm x, g.map_mul, hsource]
  have hinv :
      g (C.denominatorInverse x.denominator) =
        (f (x.denominator : α))⁻¹ := by
    have hmul :
        g (C.sourceHom (x.denominator : α)) *
          g (C.denominatorInverse x.denominator) = 1 := by
      rw [← g.map_mul, C.denominator_mul_inverse, g.map_one]
    rw [hsource] at hmul
    exact eq_inv_of_mul_eq_one_right hmul
  rw [hinv]
  simp [realizeHom, realize, RightFraction.realize]

end GroupRealization
end RightFractionCalculus
end CausalLocalization
end CausalGeometry
