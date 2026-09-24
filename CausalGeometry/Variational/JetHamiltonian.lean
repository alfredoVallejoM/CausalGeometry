import CausalGeometry.Calculus.JetRestriction
import CausalGeometry.Variational.Legendre

namespace CausalGeometry

universe u v w

/-- A variational system at every finite jet/restriction order.

The structural pair at each order is required only to select points of the
possibly singular Legendre correspondence. No inverse law is imposed. -/
structure JetVariationalSystem
    (T : JetRestrictionTower.{u, v})
    (K : Type w) [AddGroup K] where
  duality :
    (n : Nat) →
      VariationalDuality (T.Jet n) (T.Restriction n) K

  forward_selected :
    ∀ n t,
      (duality n).legendre.relates
        t ((T.pair n).forward t)

  backward_selected :
    ∀ n p,
      (duality n).legendre.relates
        ((T.pair n).backward p) p

namespace JetVariationalSystem

variable
    {T : JetRestrictionTower.{u, v}}
    {K : Type w} [AddGroup K]

def selection
    (V : JetVariationalSystem T K)
    (n : Nat) :
    PairedLegendreSelection (V.duality n).legendre where
  pair := T.pair n
  forward_selected := V.forward_selected n
  backward_selected := V.backward_selected n

theorem hamiltonian_forward
    (V : JetVariationalSystem T K)
    (n : Nat) (t : T.Jet n) :
    (V.duality n).hamiltonian ((T.pair n).forward t) =
      (V.duality n).pairing t ((T.pair n).forward t) -
        (V.duality n).lagrangian t :=
  (V.duality n).conjugacy (V.forward_selected n t)

/-- Optional coherence of Lagrangians under jet truncation. This is a property,
not a field of JetVariationalSystem. -/
def LagrangianTruncationCompatible
    (V : JetVariationalSystem T K) : Prop :=
  ∀ n (t : T.Jet (n + 1)),
    (V.duality n).lagrangian (T.jetTruncate n t) =
      (V.duality (n + 1)).lagrangian t

/-- Optional coherence of Hamiltonians under restriction truncation. -/
def HamiltonianTruncationCompatible
    (V : JetVariationalSystem T K) : Prop :=
  ∀ n (p : T.Restriction (n + 1)),
    (V.duality n).hamiltonian (T.restrictionTruncate n p) =
      (V.duality (n + 1)).hamiltonian p

def TruncationCompatible
    (V : JetVariationalSystem T K) : Prop :=
  V.LagrangianTruncationCompatible ∧
    V.HamiltonianTruncationCompatible

end JetVariationalSystem
end CausalGeometry
