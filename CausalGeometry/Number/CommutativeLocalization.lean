import CausalGeometry.Number.OreLocalization
import Mathlib.Tactic

namespace CausalGeometry

universe u

namespace CausalLocalization

variable {α : Type u} [CancelCommMonoid α]

/-- Cross-multiplication relation on right-fraction presentations.

Cancellation is required here because, unlike a general commutative monoid with
zero divisors, ordinary cross multiplication must actually be transitive. -/
def FractionRel
    (S : Submonoid α)
    (x y : RightFraction S) : Prop :=
  x.numerator * (y.denominator : α) =
    y.numerator * (x.denominator : α)

theorem fractionRel_refl
    (S : Submonoid α)
    (x : RightFraction S) :
    FractionRel S x x := rfl

theorem fractionRel_symm
    (S : Submonoid α)
    {x y : RightFraction S}
    (h : FractionRel S x y) :
    FractionRel S y x :=
  h.symm

theorem fractionRel_trans
    (S : Submonoid α)
    {x y z : RightFraction S}
    (hxy : FractionRel S x y)
    (hyz : FractionRel S y z) :
    FractionRel S x z := by
  unfold FractionRel at hxy hyz ⊢
  apply mul_right_cancel (b := (y.denominator : α))
  calc
    (x.numerator * (z.denominator : α)) *
        (y.denominator : α)
        =
      (x.numerator * (y.denominator : α)) *
        (z.denominator : α) := by ac_rfl
    _ =
      (y.numerator * (x.denominator : α)) *
        (z.denominator : α) := by rw [hxy]
    _ =
      (y.numerator * (z.denominator : α)) *
        (x.denominator : α) := by ac_rfl
    _ =
      (z.numerator * (y.denominator : α)) *
        (x.denominator : α) := by rw [hyz]
    _ =
      (z.numerator * (x.denominator : α)) *
        (y.denominator : α) := by ac_rfl

/-- Setoid defining the cancellative commutative fraction quotient. -/
def fractionSetoid (S : Submonoid α) :
    Setoid (RightFraction S) where
  r := FractionRel S
  iseqv := ⟨
    fractionRel_refl S,
    fractionRel_symm S,
    fractionRel_trans S
  ⟩

/-- Cancellative commutative causal fraction quotient.

This is the first genuine localization carrier in the program. It deliberately
does not claim the noncommutative Ore universal property. -/
def CommFraction (S : Submonoid α) :=
  Quotient (fractionSetoid S)

namespace CommFraction

variable {S : Submonoid α}

def mk (a : α) (s : S) :
    CommFraction S :=
  Quotient.mk _ ⟨a, s⟩

def ofElement (a : α) :
    CommFraction S :=
  mk a 1

theorem mk_eq_mk_of_cross
    {a b : α} {s t : S}
    (h : a * (t : α) = b * (s : α)) :
    mk (S := S) a s = mk b t := by
  apply Quotient.sound
  exact h

/-- Raw commutative multiplication of fraction presentations. -/
def rawMul
    (x y : RightFraction S) :
    RightFraction S where
  numerator := x.numerator * y.numerator
  denominator := x.denominator * y.denominator

theorem rawMul_rel
    {x x' y y' : RightFraction S}
    (hx : FractionRel S x x')
    (hy : FractionRel S y y') :
    FractionRel S (rawMul x y) (rawMul x' y') := by
  unfold FractionRel rawMul at hx hy ⊢
  dsimp
  calc
    (x.numerator * y.numerator) *
        ((x'.denominator : α) * (y'.denominator : α))
        =
      (x.numerator * (x'.denominator : α)) *
        (y.numerator * (y'.denominator : α)) := by ac_rfl
    _ =
      (x'.numerator * (x.denominator : α)) *
        (y'.numerator * (y.denominator : α)) := by
          rw [hx, hy]
    _ =
      (x'.numerator * y'.numerator) *
        ((x.denominator : α) * (y.denominator : α)) := by ac_rfl

/-- Multiplication descends to the quotient because raw multiplication respects
cross-equivalence in both arguments. -/
def mul
    (x y : CommFraction S) :
    CommFraction S :=
  Quotient.lift₂
    (fun a b => Quotient.mk _ (rawMul a b))
    (by
      intro a₁ b₁ a₂ b₂ ha hb
      apply Quotient.sound
      exact rawMul_rel ha hb)
    x y

instance : Mul (CommFraction S) :=
  ⟨mul⟩

@[simp] theorem mk_mul_mk
    (a b : α) (s t : S) :
    mk (S := S) a s * mk b t =
      mk (a * b) (s * t) := rfl

/-- The neutral presentation. Monoid laws on the quotient are proved in the
next closure layer rather than hidden in the carrier definition. -/
def one : CommFraction S :=
  ofElement 1

instance : One (CommFraction S) :=
  ⟨one⟩

@[simp] theorem one_eq_mk :
    (1 : CommFraction S) = mk 1 1 := rfl

@[simp] theorem ofElement_mul
    (a b : α) :
    ofElement (S := S) a * ofElement b =
      ofElement (a * b) := by
  rfl

/-- Generator-level associativity. This proves the multiplication formula is
coherent before packaging a full Monoid instance. -/
theorem mk_mul_assoc
    (a b c : α) (s t u : S) :
    (mk (S := S) a s * mk b t) * mk c u =
      mk a s * (mk b t * mk c u) := by
  simp only [mk_mul_mk]
  apply mk_eq_mk_of_cross
  simp [mul_assoc]

end CommFraction
end CausalLocalization
end CausalGeometry
