import CausalGeometry.Calculus.CohomologyEquivH1
import CausalGeometry.Calculus.CohomologyEquivH2
import CausalGeometry.Realization.ECIAContract

namespace CausalGeometry

universe u v w x y

/-- First causal cohomology of one causal number/diary with coefficients K. -/
abbrev CausalNumberH1
    {A : Type u}
    (K : Type w)
    [AddCommGroup K]
    (X : CausalNumber A) :=
  CausalCohomology.H1
    (S := X.system)
    (K := K)

/-- Second causal cohomology of one causal number/diary with coefficients K. -/
abbrev CausalNumberH2
    {A : Type u}
    (K : Type w)
    [AddCommGroup K]
    (X : CausalNumber A) :=
  CausalCohomology.H2
    (S := X.system)
    (K := K)

/-- A primitive causal-system isomorphism between two causal numbers induces
cohomology equivalences automatically. -/
def causalNumberH1EquivOfSystemEquiv
    {A : Type u}
    {K : Type w} [AddCommGroup K]
    {X Y : CausalNumber A}
    (E : EventSystemEquiv
      X.system Y.system) :
    CausalNumberH1 K X ≃+
      CausalNumberH1 K Y :=
  E.h1AddEquiv

def causalNumberH2EquivOfSystemEquiv
    {A : Type u}
    {K : Type w} [AddCommGroup K]
    {X Y : CausalNumber A}
    (E : EventSystemEquiv
      X.system Y.system) :
    CausalNumberH2 K X ≃+
      CausalNumberH2 K Y :=
  E.h2AddEquiv

namespace ECIARealization

variable {A : Type u}
variable {sourceAdmissible : CausalNumber A → Prop}
variable {T : ECIAStructuralTarget.{u, v} A}

/-- ECIA preservation of causal cohomology.

The target may implement its cohomology using completely different internal
types. Preservation means additive equivalence of the actual groups, not
equality of representations or equality of chosen cocycles. -/
structure PreservesCausalCohomology
    (R : ECIARealization A sourceAdmissible T)
    (K : Type w)
    [AddCommGroup K]
    (TargetH1 : T.Target → Type x)
    (TargetH2 : T.Target → Type y)
    [∀ Y, AddCommGroup (TargetH1 Y)]
    [∀ Y, AddCommGroup (TargetH2 Y)] : Prop where

  h1Equiv :
    ∀ X : CausalNumber A,
      CausalNumberH1 K X ≃+
        TargetH1 (R.realize X)

  h2Equiv :
    ∀ X : CausalNumber A,
      CausalNumberH2 K X ≃+
        TargetH2 (R.realize X)

namespace PreservesCausalCohomology

variable
    {R : ECIARealization A sourceAdmissible T}
    {K : Type w} [AddCommGroup K]
    {TargetH1 : T.Target → Type x}
    {TargetH2 : T.Target → Type y}
    [∀ Y, AddCommGroup (TargetH1 Y)]
    [∀ Y, AddCommGroup (TargetH2 Y)]
    (h :
      R.PreservesCausalCohomology
        K TargetH1 TargetH2)

/-- Triviality of H1 is preserved and reflected. -/
theorem h1_subsingleton_iff
    (X : CausalNumber A) :
    Subsingleton (CausalNumberH1 K X) ↔
      Subsingleton
        (TargetH1 (R.realize X)) := by
  constructor
  · intro hs
    exact
      Equiv.subsingleton_congr
        (h.h1Equiv X).toEquiv
        |>.mp hs
  · intro hs
    exact
      Equiv.subsingleton_congr
        (h.h1Equiv X).toEquiv
        |>.mpr hs

/-- Same for H2. -/
theorem h2_subsingleton_iff
    (X : CausalNumber A) :
    Subsingleton (CausalNumberH2 K X) ↔
      Subsingleton
        (TargetH2 (R.realize X)) := by
  constructor
  · intro hs
    exact
      Equiv.subsingleton_congr
        (h.h2Equiv X).toEquiv
        |>.mp hs
  · intro hs
    exact
      Equiv.subsingleton_congr
        (h.h2Equiv X).toEquiv
        |>.mpr hs

/-- If source H1 is finite, target H1 has exactly the same cardinality. -/
theorem h1_natCard_eq
    (X : CausalNumber A)
    [Finite (CausalNumberH1 K X)]
    [Finite (TargetH1 (R.realize X))] :
    Nat.card
        (TargetH1 (R.realize X)) =
      Nat.card (CausalNumberH1 K X) := by
  exact
    Nat.card_congr
      (h.h1Equiv X).toEquiv.symm

/-- If source H2 is finite, target H2 has exactly the same cardinality. -/
theorem h2_natCard_eq
    (X : CausalNumber A)
    [Finite (CausalNumberH2 K X)]
    [Finite (TargetH2 (R.realize X))] :
    Nat.card
        (TargetH2 (R.realize X)) =
      Nat.card (CausalNumberH2 K X) := by
  exact
    Nat.card_congr
      (h.h2Equiv X).toEquiv.symm

/-- Zero cohomology class is preserved by the equivalence. -/
@[simp] theorem h1_zero
    (X : CausalNumber A) :
    h.h1Equiv X 0 = 0 :=
  map_zero (h.h1Equiv X)

/-- Addition of classes is preserved. -/
@[simp] theorem h1_add
    (X : CausalNumber A)
    (a b : CausalNumberH1 K X) :
    h.h1Equiv X (a + b) =
      h.h1Equiv X a +
        h.h1Equiv X b :=
  map_add (h.h1Equiv X) a b

@[simp] theorem h2_add
    (X : CausalNumber A)
    (a b : CausalNumberH2 K X) :
    h.h2Equiv X (a + b) =
      h.h2Equiv X a +
        h.h2Equiv X b :=
  map_add (h.h2Equiv X) a b

/-- Cohomology preservation is insensitive to a source-side event-system
renaming: changing the source presentation only precomposes with the canonical
causal cohomology equivalence. -/
def h1EquivAfterSourceRename
    {X Y : CausalNumber A}
    (E : EventSystemEquiv
      X.system Y.system) :
    CausalNumberH1 K X ≃+
      TargetH1 (R.realize Y) :=
  E.h1AddEquiv.trans
    (h.h1Equiv Y)

def h2EquivAfterSourceRename
    {X Y : CausalNumber A}
    (E : EventSystemEquiv
      X.system Y.system) :
    CausalNumberH2 K X ≃+
      TargetH2 (R.realize Y) :=
  E.h2AddEquiv.trans
    (h.h2Equiv Y)

end PreservesCausalCohomology
end ECIARealization
end CausalGeometry
