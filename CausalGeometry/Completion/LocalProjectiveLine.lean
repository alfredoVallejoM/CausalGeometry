import Mathlib.Algebra.Group.Units.Hom
import Mathlib.RingTheory.LocalRing.Basic

namespace CausalGeometry

universe u v

/-- A projective pair in the chart system appropriate to a local ring:
at least one coordinate is a unit.

Over a local ring this is the natural unimodular-pair presentation of P¹.
The quotient by unit scaling is built below; no field hypothesis is used. -/
structure LocalProjectivePair
    (R : Type u) [CommRing R] where
  x : R
  y : R
  unit_coord : IsUnit x ∨ IsUnit y

namespace LocalProjectivePair

variable {R : Type u} [CommRing R]

@[ext] theorem ext
    {p q : LocalProjectivePair R}
    (hx : p.x = q.x)
    (hy : p.y = q.y) :
    p = q := by
  cases p
  cases q
  simp_all

/-- Scaling by a unit preserves the local-projective condition. -/
def scale (a : Rˣ) (p : LocalProjectivePair R) :
    LocalProjectivePair R where
  x := (a : R) * p.x
  y := (a : R) * p.y
  unit_coord := by
    rcases p.unit_coord with hx | hy
    · exact Or.inl (a.isUnit.mul hx)
    · exact Or.inr (a.isUnit.mul hy)

@[simp] theorem scale_x
    (a : Rˣ) (p : LocalProjectivePair R) :
    (scale a p).x = (a : R) * p.x := rfl

@[simp] theorem scale_y
    (a : Rˣ) (p : LocalProjectivePair R) :
    (scale a p).y = (a : R) * p.y := rfl

@[simp] theorem scale_one
    (p : LocalProjectivePair R) :
    scale 1 p = p := by
  ext <;> simp

theorem scale_mul
    (a b : Rˣ) (p : LocalProjectivePair R) :
    scale a (scale b p) = scale (a * b) p := by
  ext <;> simp [mul_assoc]

@[simp] theorem scale_inv_scale
    (a : Rˣ) (p : LocalProjectivePair R) :
    scale a⁻¹ (scale a p) = p := by
  rw [scale_mul]
  simp

/-- Projective equivalence: two local pairs differ by unit scaling. -/
def Equivalent
    (p q : LocalProjectivePair R) : Prop :=
  ∃ a : Rˣ, q = scale a p

theorem equivalent_refl
    (p : LocalProjectivePair R) :
    Equivalent p p :=
  ⟨1, by simp⟩

theorem equivalent_symm
    {p q : LocalProjectivePair R}
    (h : Equivalent p q) :
    Equivalent q p := by
  rcases h with ⟨a, rfl⟩
  refine ⟨a⁻¹, ?_⟩
  simp

theorem equivalent_trans
    {p q r : LocalProjectivePair R}
    (hpq : Equivalent p q)
    (hqr : Equivalent q r) :
    Equivalent p r := by
  rcases hpq with ⟨a, rfl⟩
  rcases hqr with ⟨b, rfl⟩
  refine ⟨b * a, ?_⟩
  rw [scale_mul]
  rfl

def setoid (R : Type u) [CommRing R] :
    Setoid (LocalProjectivePair R) where
  r := Equivalent
  iseqv := ⟨
    equivalent_refl,
    equivalent_symm,
    equivalent_trans
  ⟩

/-- Local projective line as unit-unimodular pairs modulo unit scaling. -/
def Line (R : Type u) [CommRing R] :=
  Quotient (setoid R)

/-- A ring homomorphism sends admissible projective pairs to admissible pairs. -/
def mapPair
    {S : Type v} [CommRing S]
    (f : R →+* S)
    (p : LocalProjectivePair R) :
    LocalProjectivePair S where
  x := f p.x
  y := f p.y
  unit_coord := by
    rcases p.unit_coord with hx | hy
    · exact Or.inl (hx.map f)
    · exact Or.inr (hy.map f)

theorem mapPair_scale
    {S : Type v} [CommRing S]
    (f : R →+* S)
    (a : Rˣ)
    (p : LocalProjectivePair R) :
    mapPair f (scale a p) =
      scale (Units.map f.toMonoidHom a) (mapPair f p) := by
  ext <;> simp [mapPair, scale]

/-- Functorial map on local projective lines induced by a ring homomorphism. -/
def map
    {S : Type v} [CommRing S]
    (f : R →+* S) :
    Line R → Line S :=
  Quotient.map
    (mapPair f)
    (by
      intro p q hpq
      rcases hpq with ⟨a, rfl⟩
      exact ⟨Units.map f.toMonoidHom a,
        (mapPair_scale f a p).symm⟩)

@[simp] theorem map_mk
    {S : Type v} [CommRing S]
    (f : R →+* S)
    (p : LocalProjectivePair R) :
    map f (Quotient.mk _ p) =
      Quotient.mk _ (mapPair f p) := rfl

end LocalProjectivePair
end CausalGeometry
