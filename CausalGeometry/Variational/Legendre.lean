import CausalGeometry.Foundation.PairedTransform

namespace CausalGeometry

universe u v w

/-- A possibly singular Legendre correspondence. It is a relation, not a
function, so degeneracy and multi-valued conjugate momenta remain representable. -/
structure LegendreCorrespondence (T : Type u) (P : Type v) where
  relates : T → P → Prop

namespace LegendreCorrespondence

variable {T : Type u} {P : Type v}

def opposite (L : LegendreCorrespondence T P) :
    LegendreCorrespondence P T where
  relates := fun p t => L.relates t p

end LegendreCorrespondence

/-- A one-way functional selection from a possibly singular Legendre
correspondence. -/
structure ForwardLegendreSelection
    {T : Type u} {P : Type v}
    (L : LegendreCorrespondence T P) where
  map : T → P
  selected : ∀ t, L.relates t (map t)

/-- Two structural selections of a Legendre correspondence. No round-trip law
is assumed, so the selected directions need not be inverse. -/
structure PairedLegendreSelection
    {T : Type u} {P : Type v}
    (L : LegendreCorrespondence T P) where
  pair : PairedTransform T P
  forward_selected : ∀ t, L.relates t (pair.forward t)
  backward_selected : ∀ p, L.relates (pair.backward p) p

/-- Generic Lagrangian/Hamiltonian conjugacy data over a possibly singular
Legendre relation.

The pairing is kept explicit. A target geometric realization may later
instantiate it with a tangent/cotangent, jet/restriction or other pairing. -/
structure VariationalDuality
    (T : Type u) (P : Type v) (K : Type w)
    [AddGroup K] where
  lagrangian : T → K
  hamiltonian : P → K
  pairing : T → P → K
  legendre : LegendreCorrespondence T P
  conjugacy :
    ∀ {t p}, legendre.relates t p →
      hamiltonian p = pairing t p - lagrangian t

namespace VariationalDuality

variable {T : Type u} {P : Type v} {K : Type w} [AddGroup K]

theorem hamiltonian_of_forward_selection
    (V : VariationalDuality T P K)
    (S : ForwardLegendreSelection V.legendre)
    (t : T) :
    V.hamiltonian (S.map t) =
      V.pairing t (S.map t) - V.lagrangian t :=
  V.conjugacy (S.selected t)

theorem hamiltonian_of_paired_selection
    (V : VariationalDuality T P K)
    (S : PairedLegendreSelection V.legendre)
    (t : T) :
    V.hamiltonian (S.pair.forward t) =
      V.pairing t (S.pair.forward t) - V.lagrangian t :=
  V.conjugacy (S.forward_selected t)

end VariationalDuality
end CausalGeometry
