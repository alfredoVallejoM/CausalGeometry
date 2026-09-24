import Mathlib.Algebra.Group.Submonoid.Basic

namespace CausalGeometry

universe u v

namespace CausalLocalization

variable {α : Type u} [Monoid α]

/-- One right Ore square for a numerator a and denominator s.

The equation a*u = s*b is exactly the rewrite needed to move s^{-1}
past a when forming right fractions. -/
structure RightOreSquare
    (S : Submonoid α) (a : α) (s : S) where
  numerator : α
  denominator : S
  cross :
    a * (denominator : α) =
      (s : α) * numerator

/-- One left Ore square. The orientation u*a = b*s is kept separate from the
right-handed condition. -/
structure LeftOreSquare
    (S : Submonoid α) (a : α) (s : S) where
  numerator : α
  denominator : S
  cross :
    (denominator : α) * a =
      numerator * (s : α)

/-- Right Ore condition. Nonempty keeps witness choice out of the primitive
structure. -/
def RightOreCondition (S : Submonoid α) : Prop :=
  ∀ a s, Nonempty (RightOreSquare S a s)

/-- Left Ore condition. -/
def LeftOreCondition (S : Submonoid α) : Prop :=
  ∀ a s, Nonempty (LeftOreSquare S a s)

/-- A raw right fraction a*s^{-1}. This is a presentation, not yet a quotient
by the Ore equivalence relation. -/
structure RightFraction (S : Submonoid α) where
  numerator : α
  denominator : S

/-- A raw left fraction s^{-1}*a. -/
structure LeftFraction (S : Submonoid α) where
  denominator : S
  numerator : α

namespace RightFraction

variable {S : Submonoid α}

def ofElement (a : α) : RightFraction S where
  numerator := a
  denominator := 1

/-- Multiply two right-fraction presentations using an explicit Ore square
that moves the first denominator across the second numerator.

If x=a*s^{-1}, y=b*t^{-1} and b*u=s*c, then
xy=(a*c)*(t*u)^{-1}. -/
def mulWith
    (x y : RightFraction S)
    (w : RightOreSquare S y.numerator x.denominator) :
    RightFraction S where
  numerator := x.numerator * w.numerator
  denominator := y.denominator * w.denominator

/-- Evaluation of a right-fraction presentation in any target group. This does
not assert that two presentations have already been quotiented. -/
def realize {G : Type v} [Group G]
    (f : α →* G)
    (x : RightFraction S) : G :=
  f x.numerator * (f (x.denominator : α))⁻¹

@[simp] theorem realize_ofElement
    {G : Type v} [Group G]
    (f : α →* G) (a : α) :
    realize f (ofElement (S := S) a) = f a := by
  simp [realize, ofElement]

end RightFraction

namespace LeftFraction

variable {S : Submonoid α}

def ofElement (a : α) : LeftFraction S where
  denominator := 1
  numerator := a

/-- If x=s^{-1}*a, y=t^{-1}*b and u*a=c*t, then
xy=(u*s)^{-1}*(c*b). -/
def mulWith
    (x y : LeftFraction S)
    (w : LeftOreSquare S x.numerator y.denominator) :
    LeftFraction S where
  denominator := w.denominator * x.denominator
  numerator := w.numerator * y.numerator

def realize {G : Type v} [Group G]
    (f : α →* G)
    (x : LeftFraction S) : G :=
  (f (x.denominator : α))⁻¹ * f x.numerator

@[simp] theorem realize_ofElement
    {G : Type v} [Group G]
    (f : α →* G) (a : α) :
    realize f (ofElement (S := S) a) = f a := by
  simp [realize, ofElement]

end LeftFraction

/-- Every denominator system in a commutative monoid satisfies the right Ore
condition canonically. -/
theorem rightOre_of_commutative
    {α : Type u} [CommMonoid α]
    (S : Submonoid α) :
    RightOreCondition S := by
  intro a s
  exact ⟨{
    numerator := a
    denominator := s
    cross := by simpa [mul_comm]
  }⟩

/-- The left Ore condition is equally automatic in a commutative monoid. -/
theorem leftOre_of_commutative
    {α : Type u} [CommMonoid α]
    (S : Submonoid α) :
    LeftOreCondition S := by
  intro a s
  exact ⟨{
    numerator := a
    denominator := s
    cross := by simpa [mul_comm]
  }⟩

/-- Canonical right Ore square in the commutative sector. -/
def commutativeRightSquare
    {α : Type u} [CommMonoid α]
    (S : Submonoid α) (a : α) (s : S) :
    RightOreSquare S a s where
  numerator := a
  denominator := s
  cross := by simpa [mul_comm]

/-- Canonical left Ore square in the commutative sector. -/
def commutativeLeftSquare
    {α : Type u} [CommMonoid α]
    (S : Submonoid α) (a : α) (s : S) :
    LeftOreSquare S a s where
  numerator := a
  denominator := s
  cross := by simpa [mul_comm]

end CausalLocalization
end CausalGeometry
