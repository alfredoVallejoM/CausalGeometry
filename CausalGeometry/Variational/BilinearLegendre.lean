import CausalGeometry.Calculus.HamiltonianTransport
import CausalGeometry.Variational.Legendre

namespace CausalGeometry

universe u v w x
open EventSystem

variable {Event : Type u} {Label : Type v}
variable {S : EventSystem Event Label}

namespace CausalBilinear

variable {K : Type w}
variable {Fiber : Configuration S → Type x}
variable [CommRing K]
variable [∀ C, AddCommGroup (Fiber C)]
variable [∀ C, Module K (Fiber C)]

/-- Bilinear realization of the Legendre relation at one configuration:
a vector and covector are Legendre-related precisely when the covector is
the flat image of the vector. -/
def legendreCorrespondence
    (B : Field (K := K) (S := S) (Fiber := Fiber))
    (C : Configuration S) :
    LegendreCorrespondence
      (Fiber C)
      (Module.Dual K (Fiber C)) where
  relates := fun x ω =>
    B.flat C x = ω

@[simp] theorem legendreCorrespondence_relates_iff
    (B : Field (K := K) (S := S) (Fiber := Fiber))
    (C : Configuration S)
    (x : Fiber C)
    (ω : Module.Dual K (Fiber C)) :
    (B.legendreCorrespondence C).relates x ω ↔
      B.flat C x = ω :=
  Iff.rfl

/-- Flat is always a forward selection of the bilinear Legendre
correspondence, even when the form is degenerate. -/
def legendreForwardSelection
    (B : Field (K := K) (S := S) (Fiber := Fiber))
    (C : Configuration S) :
    ForwardLegendreSelection
      (B.legendreCorrespondence C) where
  map := B.flat C
  selected := by
    intro x
    rfl

/-- A musical bridge upgrades the one-way Legendre selection to a paired
selection.  Its forward map is flat and its backward map is sharp. -/
def legendrePairedSelection
    {B : Field (K := K) (S := S) (Fiber := Fiber)}
    (M : MusicalBridge B)
    (C : Configuration S) :
    PairedLegendreSelection
      (B.legendreCorrespondence C) where
  pair where
    forward := B.flat C
    backward := M.sharp C
  forward_selected := by
    intro x
    rfl
  backward_selected := by
    intro ω
    exact M.flat_sharp C ω

@[simp] theorem legendrePairedSelection_forward
    {B : Field (K := K) (S := S) (Fiber := Fiber)}
    (M : MusicalBridge B)
    (C : Configuration S)
    (x : Fiber C) :
    (M.legendrePairedSelection C).pair.forward x =
      B.flat C x :=
  rfl

@[simp] theorem legendrePairedSelection_backward
    {B : Field (K := K) (S := S) (Fiber := Fiber)}
    (M : MusicalBridge B)
    (C : Configuration S)
    (ω : Module.Dual K (Fiber C)) :
    (M.legendrePairedSelection C).pair.backward ω =
      M.sharp C ω :=
  rfl

/-- The paired Legendre selection induced by a musical bridge is an actual
two-sided structural equivalence.  This is derived from the bridge rather
than built into LegendreCorrespondence. -/
@[simp] theorem legendrePaired_sourceRoundTrip
    {B : Field (K := K) (S := S) (Fiber := Fiber)}
    (M : MusicalBridge B)
    (C : Configuration S)
    (x : Fiber C) :
    (M.legendrePairedSelection C).pair.sourceRoundTrip x =
      x := by
  exact M.sharp_flat C x

@[simp] theorem legendrePaired_targetRoundTrip
    {B : Field (K := K) (S := S) (Fiber := Fiber)}
    (M : MusicalBridge B)
    (C : Configuration S)
    (ω : Module.Dual K (Fiber C)) :
    (M.legendrePairedSelection C).pair.targetRoundTrip ω =
      ω := by
  exact M.flat_sharp C ω

end CausalBilinear

namespace CausalHamiltonian

variable {K : Type w}
variable {Fiber : Configuration S → Type x}
variable [CommRing K]
variable [∀ C, AddCommGroup (Fiber C)]
variable [∀ C, Module K (Fiber C)]

/-- The Hamiltonian relation flat(X)=dH is exactly membership in the bilinear
Legendre correspondence. -/
theorem Pair.legendre_related
    {B : CausalBilinear.Field
      (K := K) (S := S) (Fiber := Fiber)}
    (H : Pair B)
    (C : Configuration S) :
    (B.legendreCorrespondence C).relates
      (H.vector C) (H.covector C) :=
  H.hamiltonian C

/-- Conversely, any vector/covector sections related pointwise by the
bilinear Legendre relation define a Hamiltonian pair. -/
def Pair.ofLegendreSections
    {B : CausalBilinear.Field
      (K := K) (S := S) (Fiber := Fiber)}
    (X : VectorSection (S := S) (Fiber := Fiber))
    (dH : CovectorSection
      (K := K) (S := S) (Fiber := Fiber))
    (hrel :
      ∀ C,
        (B.legendreCorrespondence C).relates
          (X C) (dH C)) :
    Pair B where
  vector := X
  covector := dH
  hamiltonian := hrel

end CausalHamiltonian

namespace CausalVariational

variable {K : Type w}
variable {Fiber : Configuration S → Type x}
variable [CommRing K]
variable [∀ C, AddCommGroup (Fiber C)]
variable [∀ C, Module K (Fiber C)]

/-- Energy data whose Legendre relation is exactly the bilinear realization at
one configuration.  The conjugacy law remains an explicit theorem field. -/
structure BilinearEnergy
    (B : CausalBilinear.Field
      (K := K) (S := S) (Fiber := Fiber))
    (C : Configuration S) where
  lagrangian : Fiber C → K
  hamiltonian : Module.Dual K (Fiber C) → K

  conjugacy :
    ∀ {x ω},
      B.flat C x = ω →
        hamiltonian ω =
          ω x - lagrangian x

namespace BilinearEnergy

variable
    {B : CausalBilinear.Field
      (K := K) (S := S) (Fiber := Fiber)}
    {C : Configuration S}
    (E : BilinearEnergy B C)

/-- Forget the bilinear presentation and expose the generic
VariationalDuality API. -/
def toVariationalDuality :
    VariationalDuality
      (Fiber C)
      (Module.Dual K (Fiber C))
      K where
  lagrangian := E.lagrangian
  hamiltonian := E.hamiltonian
  pairing := fun x ω => ω x
  legendre := B.legendreCorrespondence C
  conjugacy := by
    intro x ω h
    exact E.conjugacy h

/-- The forward Legendre selection yields the ordinary conjugacy formula
H(flat x)=flat(x)(x)-L(x). -/
theorem hamiltonian_flat
    (x : Fiber C) :
    E.hamiltonian (B.flat C x) =
      B.flat C x x - E.lagrangian x := by
  exact E.conjugacy rfl

/-- With a musical bridge, the generic paired variational selection is
available and is exactly flat/sharp. -/
def pairedSelection
    (M : CausalBilinear.MusicalBridge B) :
    PairedLegendreSelection
      E.toVariationalDuality.legendre :=
  M.legendrePairedSelection C

end BilinearEnergy
end CausalVariational
end CausalGeometry
