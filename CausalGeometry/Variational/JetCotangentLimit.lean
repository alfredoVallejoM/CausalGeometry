import CausalGeometry.Calculus.JetRestrictionLimit
import CausalGeometry.Variational.JetCotangent

namespace CausalGeometry

universe u v w

namespace JetCotangent.MusicalRealization

variable
    {T : JetRestrictionTower.{u, v}}
    {K : Type w}
    [CommRing K]
    [∀ n, AddCommGroup (T.Jet n)]
    [∀ n, Module K (T.Jet n)]
    [∀ n, AddCommGroup (T.Restriction n)]
    [∀ n, Module K (T.Restriction n)]
    (R : JetCotangent.MusicalRealization T K)
    (L : JetCotangent.LinearTruncation T K)
    (P : JetCotangent.Prolongation T K L)

variable
    (hCot :
      R.toRealization.CotangentRestrictionCompatible
        L P)
    (hFlat :
      R.toRealization.FlatTruncationCompatible
        L P)
    (hSharp :
      R.SharpTruncationCompatible L P)

def derivedCompatibility :
    T.Compatible :=
  R.compatible_of_geometric
    L P hCot hFlat hSharp

/-- The geometrically derived forward map on coherent sections. -/
def forwardLimit :
    T.JetSection →
      T.RestrictionSection :=
  T.forwardSection
    (R.derivedCompatibility
      L P hCot hFlat hSharp).1

/-- The geometrically derived backward map on coherent sections. -/
def backwardLimit :
    T.RestrictionSection →
      T.JetSection :=
  T.backwardSection
    (R.derivedCompatibility
      L P hCot hFlat hSharp).2

/-- Finite-order musical inverse laws lift pointwise to the inverse limit. -/
theorem backward_forward_limit
    (J : T.JetSection) :
    R.backwardLimit L P hCot hFlat hSharp
        (R.forwardLimit L P hCot hFlat hSharp J) =
      J := by
  apply JetRestrictionTower.JetSection.ext
  funext n
  change
    (T.pair n).backward
        ((T.pair n).forward (J.value n)) =
      J.value n
  exact R.sourceRoundTrip_eq n (J.value n)

/-- And symmetrically on restriction sections. -/
theorem forward_backward_limit
    (Q : T.RestrictionSection) :
    R.forwardLimit L P hCot hFlat hSharp
        (R.backwardLimit L P hCot hFlat hSharp Q) =
      Q := by
  apply JetRestrictionTower.RestrictionSection.ext
  funext n
  change
    (T.pair n).forward
        ((T.pair n).backward (Q.value n)) =
      Q.value n
  exact R.targetRoundTrip_eq n (Q.value n)

/-- Geometric cotangent/musical coherence upgrades the inverse-limit structural
pair to an actual equivalence. -/
def limitEquiv :
    T.JetSection ≃
      T.RestrictionSection where
  toFun :=
    R.forwardLimit L P hCot hFlat hSharp
  invFun :=
    R.backwardLimit L P hCot hFlat hSharp
  left_inv :=
    R.backward_forward_limit
      L P hCot hFlat hSharp
  right_inv :=
    R.forward_backward_limit
      L P hCot hFlat hSharp

/-- The original limitPair from the structural API is exactly the pair
underlying the derived limit equivalence. -/
theorem limitPair_forward_eq
    (J : T.JetSection) :
    (T.limitPair
      (R.derivedCompatibility
        L P hCot hFlat hSharp)).forward J =
      R.limitEquiv L P hCot hFlat hSharp J :=
  rfl

theorem limitPair_backward_eq
    (Q : T.RestrictionSection) :
    (T.limitPair
      (R.derivedCompatibility
        L P hCot hFlat hSharp)).backward Q =
      (R.limitEquiv L P hCot hFlat hSharp).symm Q :=
  rfl

@[simp] theorem limitPair_sourceRoundTrip
    (J : T.JetSection) :
    (T.limitPair
      (R.derivedCompatibility
        L P hCot hFlat hSharp)).sourceRoundTrip J =
      J := by
  exact
    R.backward_forward_limit
      L P hCot hFlat hSharp J

@[simp] theorem limitPair_targetRoundTrip
    (Q : T.RestrictionSection) :
    (T.limitPair
      (R.derivedCompatibility
        L P hCot hFlat hSharp)).targetRoundTrip Q =
      Q := by
  exact
    R.forward_backward_limit
      L P hCot hFlat hSharp Q

end JetCotangent.MusicalRealization
end CausalGeometry
