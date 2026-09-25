import CausalGeometry.Number.CentralOre
import CausalGeometry.Number.LeftFractionCalculus
import CausalGeometry.Number.RightFractionCalculus

namespace CausalGeometry

universe u

namespace CausalLocalization

variable {α : Type u} [CancelMonoid α]
variable {S : Submonoid α}
variable (hS : CentralDenominators S)

/-- Cross-multiplication relation for right fractions with central
denominators. -/
def centralRightRel
    (x y : RightFraction S) : Prop :=
  x.numerator * (y.denominator : α) =
    y.numerator * (x.denominator : α)

theorem centralRightRel_refl
    (x : RightFraction S) :
    centralRightRel x x :=
  rfl

theorem centralRightRel_symm
    {x y : RightFraction S}
    (h : centralRightRel x y) :
    centralRightRel y x :=
  h.symm

theorem centralRightRel_trans
    {x y z : RightFraction S}
    (hxy : centralRightRel x y)
    (hyz : centralRightRel y z) :
    centralRightRel x z := by
  rcases x with ⟨a, s⟩
  rcases y with ⟨b, t⟩
  rcases z with ⟨c, u⟩
  change a * (t : α) =
    b * (s : α) at hxy
  change b * (u : α) =
    c * (t : α) at hyz
  change a * (u : α) =
    c * (s : α)
  have hcancel :
      (a * (u : α)) * (t : α) =
        (c * (s : α)) * (t : α) := by
    calc
      (a * (u : α)) * (t : α)
          =
        (a * (t : α)) * (u : α) := by
          simp only [mul_assoc]
          exact congrArg (a * ·)
            (hS t (u : α)).eq.symm
      _ = (b * (s : α)) * (u : α) := by
          rw [hxy]
      _ = (b * (u : α)) * (s : α) := by
          simp only [mul_assoc]
          exact congrArg (b * ·)
            (hS s (u : α)).eq
      _ = (c * (t : α)) * (s : α) := by
          rw [hyz]
      _ = (c * (s : α)) * (t : α) := by
          simp only [mul_assoc]
          exact congrArg (c * ·)
            (hS t (s : α)).eq
  exact mul_right_cancel hcancel

theorem centralRightRel_equivalence :
    Equivalence
      (centralRightRel (S := S)) :=
  ⟨centralRightRel_refl,
    centralRightRel_symm,
    centralRightRel_trans hS⟩

/-- Canonical representative multiplication in the central-denominator
sector. -/
def centralRightMulRep
    (x y : RightFraction S) :
    RightFraction S where
  numerator := x.numerator * y.numerator
  denominator :=
    y.denominator * x.denominator

theorem centralRightMulRep_respects
    {x x' y y' : RightFraction S}
    (hx : centralRightRel x x')
    (hy : centralRightRel y y') :
    centralRightRel
      (centralRightMulRep x y)
      (centralRightMulRep x' y') := by
  rcases x with ⟨a, s⟩
  rcases x' with ⟨a', s'⟩
  rcases y with ⟨b, t⟩
  rcases y' with ⟨b', t'⟩
  change a * (s' : α) =
    a' * (s : α) at hx
  change b * (t' : α) =
    b' * (t : α) at hy
  change
    (a * b) *
        (((t' * s' : S) : α)) =
      (a' * b') *
        (((t * s : S) : α))
  simp only [Submonoid.coe_mul]
  calc
    (a * b) * ((t' : α) * (s' : α))
        =
      (a * (b * (t' : α))) *
        (s' : α) := by
          simp [mul_assoc]
    _ =
      (a * (b' * (t : α))) *
        (s' : α) := by
          rw [hy]
    _ =
      (a * (s' : α)) *
        (b' * (t : α)) := by
          rw [mul_assoc]
          rw [(hS s'
            (b' * (t : α))).eq.symm]
          simp [mul_assoc]
    _ =
      (a' * (s : α)) *
        (b' * (t : α)) := by
          rw [hx]
    _ =
      (a' * b') *
        ((t : α) * (s : α)) := by
          calc
            (a' * (s : α)) *
                (b' * (t : α))
                =
              a' *
                ((s : α) *
                  (b' * (t : α))) := by
                    simp [mul_assoc]
            _ =
              a' *
                (((s : α) * b') *
                  (t : α)) := by
                    simp [mul_assoc]
            _ =
              a' *
                ((b' * (s : α)) *
                  (t : α)) := by
                    rw [(hS s b').eq]
            _ =
              a' *
                (b' *
                  ((s : α) * (t : α))) := by
                    simp [mul_assoc]
            _ =
              a' *
                (b' *
                  ((t : α) * (s : α))) := by
                    rw [(hS s (t : α)).eq]
            _ =
              (a' * b') *
                ((t : α) * (s : α)) := by
                    simp [mul_assoc]

/-- Certified right fraction calculus for central denominators in a
cancelative noncommutative monoid. -/
def centralRightFractionCalculus :
    RightFractionCalculus S where
  rel := centralRightRel
  rel_equivalence :=
    centralRightRel_equivalence hS
  mulRep := centralRightMulRep

  mul_from_ore := by
    intro x y
    let w :=
      hS.rightSquare
        y.numerator x.denominator
    refine ⟨w, ?_⟩
    exact centralRightRel_refl _

  mul_respects := by
    intro x x' y y' hx hy
    exact
      centralRightMulRep_respects hS hx hy

  mul_assoc := by
    intro x y z
    simp [centralRightRel,
      centralRightMulRep, mul_assoc]

  one_mul := by
    intro x
    rcases x with ⟨a, s⟩
    simp [centralRightRel,
      centralRightMulRep]

  mul_one := by
    intro x
    rcases x with ⟨a, s⟩
    simp [centralRightRel,
      centralRightMulRep]

  source_mul := by
    intro a b
    simp [centralRightRel,
      centralRightMulRep,
      RightFraction.ofElement]

  denominator_right_inverse := by
    intro s
    simp [centralRightRel,
      centralRightMulRep,
      RightFraction.ofElement]

  denominator_left_inverse := by
    intro s
    simp [centralRightRel,
      centralRightMulRep,
      RightFraction.ofElement]

  normalForm := by
    intro x
    rcases x with ⟨a, s⟩
    simp [centralRightRel,
      centralRightMulRep,
      RightFraction.ofElement]

/-- Left cross relation, written in the left-fraction field order. -/
def centralLeftRel
    (x y : LeftFraction S) : Prop :=
  x.numerator * (y.denominator : α) =
    y.numerator * (x.denominator : α)

theorem centralLeftRel_refl
    (x : LeftFraction S) :
    centralLeftRel x x :=
  rfl

theorem centralLeftRel_symm
    {x y : LeftFraction S}
    (h : centralLeftRel x y) :
    centralLeftRel y x :=
  h.symm

theorem centralLeftRel_equivalence :
    Equivalence
      (centralLeftRel (S := S)) := by
  constructor
  · exact centralLeftRel_refl
  · exact centralLeftRel_symm
  · intro x y z hxy hyz
    let xr : RightFraction S :=
      ⟨x.numerator, x.denominator⟩
    let yr : RightFraction S :=
      ⟨y.numerator, y.denominator⟩
    let zr : RightFraction S :=
      ⟨z.numerator, z.denominator⟩
    exact
      centralRightRel_trans hS
        (x := xr) (y := yr) (z := zr)
        hxy hyz

def centralLeftMulRep
    (x y : LeftFraction S) :
    LeftFraction S where
  denominator :=
    y.denominator * x.denominator
  numerator :=
    x.numerator * y.numerator

theorem centralLeftMulRep_respects
    {x x' y y' : LeftFraction S}
    (hx : centralLeftRel x x')
    (hy : centralLeftRel y y') :
    centralLeftRel
      (centralLeftMulRep x y)
      (centralLeftMulRep x' y') := by
  let xr : RightFraction S :=
    ⟨x.numerator, x.denominator⟩
  let xr' : RightFraction S :=
    ⟨x'.numerator, x'.denominator⟩
  let yr : RightFraction S :=
    ⟨y.numerator, y.denominator⟩
  let yr' : RightFraction S :=
    ⟨y'.numerator, y'.denominator⟩
  exact
    centralRightMulRep_respects hS
      (x := xr) (x' := xr')
      (y := yr) (y' := yr')
      hx hy

/-- Certified left fraction calculus for the same central denominator system. -/
def centralLeftFractionCalculus :
    LeftFractionCalculus S where
  rel := centralLeftRel
  rel_equivalence :=
    centralLeftRel_equivalence hS
  mulRep := centralLeftMulRep

  mul_from_ore := by
    intro x y
    let w :=
      hS.leftSquare
        x.numerator y.denominator
    refine ⟨w, ?_⟩
    exact
      (by
        apply centralLeftRel_refl :
        centralLeftRel
          (centralLeftMulRep x y)
          (LeftFraction.mulWith x y w))

  mul_respects := by
    intro x x' y y' hx hy
    exact
      centralLeftMulRep_respects hS hx hy

  mul_assoc := by
    intro x y z
    simp [centralLeftRel,
      centralLeftMulRep, mul_assoc]

  one_mul := by
    intro x
    rcases x with ⟨s, a⟩
    simp [centralLeftRel,
      centralLeftMulRep]

  mul_one := by
    intro x
    rcases x with ⟨s, a⟩
    simp [centralLeftRel,
      centralLeftMulRep]

  source_mul := by
    intro a b
    simp [centralLeftRel,
      centralLeftMulRep,
      LeftFraction.ofElement]

  denominator_right_inverse := by
    intro s
    simp [centralLeftRel,
      centralLeftMulRep,
      LeftFraction.ofElement]

  denominator_left_inverse := by
    intro s
    simp [centralLeftRel,
      centralLeftMulRep,
      LeftFraction.ofElement]

  normalForm := by
    intro x
    rcases x with ⟨s, a⟩
    simp [centralLeftRel,
      centralLeftMulRep,
      LeftFraction.ofElement]

end CausalLocalization
end CausalGeometry
