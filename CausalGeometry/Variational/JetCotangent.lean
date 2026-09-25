import CausalGeometry.Calculus.JetRestriction
import CausalGeometry.Variational.BilinearLegendre
import Mathlib.LinearAlgebra.Dual.Defs

namespace CausalGeometry

universe u v w

namespace JetCotangent

variable
    (T : JetRestrictionTower.{u, v})
    (K : Type w)
    [CommRing K]
    [∀ n, AddCommGroup (T.Jet n)]
    [∀ n, Module K (T.Jet n)]
    [∀ n, AddCommGroup (T.Restriction n)]
    [∀ n, Module K (T.Restriction n)]

/-- Linear presentation of the jet truncation maps already carried
structurally by the tower. -/
structure LinearTruncation where
  map :
    ∀ n,
      T.Jet (n + 1) →ₗ[K] T.Jet n
  agrees :
    ∀ n x,
      map n x =
        T.jetTruncate n x

/-- Optional prolongation of finite jets.

This is deliberately separate from jet truncation.  A prolongation is a
section, not an inverse: many higher jets may truncate to the same lower jet. -/
structure Prolongation
    (L : LinearTruncation T K) where
  map :
    ∀ n,
      T.Jet n →ₗ[K] T.Jet (n + 1)

  truncate_prolong :
    ∀ n x,
      L.map n (map n x) = x

/-- Bilinear/cotangent realization of every finite jet level.

Restrictions are realized as actual algebraic covectors on jets.  The forward
structural map of the tower is required to agree with the flat map under that
realization. -/
structure Realization where
  form :
    (n : Nat) →
      T.Jet n →ₗ[K] T.Jet n →ₗ[K] K

  restrictionDual :
    (n : Nat) →
      T.Restriction n ≃ₗ[K]
        Module.Dual K (T.Jet n)

  forward_flat :
    ∀ n x,
      restrictionDual n
          ((T.pair n).forward x) =
        form n x

namespace Realization

variable
    {T : JetRestrictionTower.{u, v}}
    {K : Type w}
    [CommRing K]
    [∀ n, AddCommGroup (T.Jet n)]
    [∀ n, Module K (T.Jet n)]
    [∀ n, AddCommGroup (T.Restriction n)]
    [∀ n, Module K (T.Restriction n)]
    (R : Realization T K)

def flat
    (n : Nat) :
    T.Jet n →ₗ[K]
      Module.Dual K (T.Jet n) :=
  R.form n

/-- Concrete Legendre relation at one jet order. -/
def legendre
    (n : Nat) :
    LegendreCorrespondence
      (T.Jet n)
      (Module.Dual K (T.Jet n)) where
  relates := fun x ω =>
    R.flat n x = ω

/-- Structural forward transport is a Legendre selection after realizing the
restriction as a covector. -/
theorem forward_legendre_selected
    (n : Nat)
    (x : T.Jet n) :
    (R.legendre n).relates
      x
      (R.restrictionDual n
        ((T.pair n).forward x)) := by
  exact (R.forward_flat n x).symm

end Realization

/-- Musical enhancement of a jet cotangent realization.

Backward structural transport is required to agree with sharp only after the
restriction object has been realized as a covector. -/
structure MusicalRealization
    extends Realization T K where
  sharp :
    (n : Nat) →
      Module.Dual K (T.Jet n) →ₗ[K]
        T.Jet n

  sharp_flat :
    ∀ n x,
      sharp n (toRealization.flat n x) = x

  flat_sharp :
    ∀ n ω,
      toRealization.flat n (sharp n ω) = ω

  backward_sharp :
    ∀ n r,
      (T.pair n).backward r =
        sharp n (toRealization.restrictionDual n r)

namespace MusicalRealization

variable
    {T : JetRestrictionTower.{u, v}}
    {K : Type w}
    [CommRing K]
    [∀ n, AddCommGroup (T.Jet n)]
    [∀ n, Module K (T.Jet n)]
    [∀ n, AddCommGroup (T.Restriction n)]
    [∀ n, Module K (T.Restriction n)]
    (R : MusicalRealization T K)

/-- Musical data makes every finite structural pair a genuine two-sided
equivalence, but only as a theorem of the enhanced realization. -/
theorem sourceRoundTrip_eq
    (n : Nat) (x : T.Jet n) :
    T.jetRoundTrip n x = x := by
  unfold JetRestrictionTower.jetRoundTrip
    PairedTransform.sourceRoundTrip
  change
    (T.pair n).backward
        ((T.pair n).forward x) =
      x
  rw [R.backward_sharp]
  rw [R.toRealization.forward_flat]
  exact R.sharp_flat n x

theorem targetRoundTrip_eq
    (n : Nat)
    (r : T.Restriction n) :
    T.restrictionRoundTrip n r = r := by
  apply (R.toRealization.restrictionDual n).injective
  unfold JetRestrictionTower.restrictionRoundTrip
    PairedTransform.targetRoundTrip
  change
    R.toRealization.restrictionDual n
        ((T.pair n).forward
          ((T.pair n).backward r)) =
      R.toRealization.restrictionDual n r
  rw [R.toRealization.forward_flat]
  rw [R.backward_sharp]
  exact R.flat_sharp n
    (R.toRealization.restrictionDual n r)

end MusicalRealization

namespace Realization

variable
    {T : JetRestrictionTower.{u, v}}
    {K : Type w}
    [CommRing K]
    [∀ n, AddCommGroup (T.Jet n)]
    [∀ n, Module K (T.Jet n)]
    [∀ n, AddCommGroup (T.Restriction n)]
    [∀ n, Module K (T.Restriction n)]
    (R : Realization T K)
    (L : LinearTruncation T K)
    (P : Prolongation T K L)

/-- Restriction truncation is cotangent pullback along jet prolongation. -/
def CotangentRestrictionCompatible : Prop :=
  ∀ n r,
    R.restrictionDual n
        (T.restrictionTruncate n r) =
      (R.restrictionDual (n + 1) r).comp
        (P.map n)

/-- The bilinear flat maps themselves are coherent across truncation and
prolongation. -/
def FlatTruncationCompatible : Prop :=
  ∀ n x,
    (R.flat (n + 1) x).comp
        (P.map n) =
      R.flat n (L.map n x)

/-- Cotangent compatibility plus flat compatibility derive the original
forward structural compatibility of the jet/restriction tower. -/
theorem forwardCompatible_of_cotangent
    (hCot : R.CotangentRestrictionCompatible L P)
    (hFlat : R.FlatTruncationCompatible L P) :
    T.ForwardCompatible := by
  intro n x
  apply (R.restrictionDual n).injective
  rw [hCot n ((T.pair (n + 1)).forward x)]
  rw [R.forward_flat]
  rw [hFlat n x]
  rw [← R.forward_flat]
  rw [L.agrees n x]

end Realization

namespace MusicalRealization

variable
    {T : JetRestrictionTower.{u, v}}
    {K : Type w}
    [CommRing K]
    [∀ n, AddCommGroup (T.Jet n)]
    [∀ n, Module K (T.Jet n)]
    [∀ n, AddCommGroup (T.Restriction n)]
    [∀ n, Module K (T.Restriction n)]
    (R : MusicalRealization T K)
    (L : LinearTruncation T K)
    (P : Prolongation T K L)

/-- Sharp is coherent with jet truncation when truncating a higher-order
Hamiltonian vector agrees with applying lower-order sharp to the pulled-back
covector. -/
def SharpTruncationCompatible : Prop :=
  ∀ n ω,
    L.map n (R.sharp (n + 1) ω) =
      R.sharp n (ω.comp (P.map n))

/-- Musical, cotangent and sharp coherence derive the original backward
structural compatibility of the tower. -/
theorem backwardCompatible_of_cotangent
    (hCot :
      R.toRealization.CotangentRestrictionCompatible
        L P)
    (hSharp : R.SharpTruncationCompatible L P) :
    T.BackwardCompatible := by
  intro n r
  rw [R.backward_sharp]
  rw [L.agrees]
  rw [hSharp n
    (R.toRealization.restrictionDual
      (n + 1) r)]
  rw [← hCot n r]
  rw [← R.backward_sharp]

/-- The complete tower compatibility follows from geometric cotangent/flat/
sharp compatibility; it is not an independent axiom in this realization. -/
theorem compatible_of_geometric
    (hCot :
      R.toRealization.CotangentRestrictionCompatible
        L P)
    (hFlat :
      R.toRealization.FlatTruncationCompatible
        L P)
    (hSharp :
      R.SharpTruncationCompatible L P) :
    T.Compatible :=
  ⟨
    R.toRealization.forwardCompatible_of_cotangent
      L P hCot hFlat,
    R.backwardCompatible_of_cotangent
      L P hCot hSharp
  ⟩

end MusicalRealization
end JetCotangent
end CausalGeometry
