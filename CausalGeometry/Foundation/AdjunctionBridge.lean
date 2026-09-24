import CausalGeometry.Foundation.PairedTransform
import CausalGeometry.Foundation.ExtensionRestriction

namespace CausalGeometry

universe u v

/-- Optional ordered bridge upgrading a structural pair (Phi,Psi) to an
adjunction. This is deliberately not part of PairedTransform itself. -/
structure AdjointBridge
    {α : Type u} {β : Type v}
    [Preorder α] [Preorder β]
    (P : PairedTransform α β) : Prop where
  adjunction :
    ∀ a b, P.forward a ≤ b ↔ a ≤ P.backward b

namespace AdjointBridge

variable {α : Type u} {β : Type v}
variable [Preorder α] [Preorder β]
variable {P : PairedTransform α β}

/-- An adjoint structural pair can be consumed by the pre-existing
ExtensionRestriction API without making adjunction foundational. -/
def toExtensionRestriction
    (A : AdjointBridge P) :
    ExtensionRestriction α β where
  extend := P.forward
  restrict := P.backward
  adjunction := A.adjunction

end AdjointBridge

namespace ExtensionRestriction

variable {α : Type u} {β : Type v}
variable [Preorder α] [Preorder β]

/-- Forget the adjunction law and retain only the two structural directions. -/
def toPaired (E : ExtensionRestriction α β) :
    PairedTransform α β where
  forward := E.extend
  backward := E.restrict

/-- Every existing ExtensionRestriction yields an explicit proof that its
underlying structural pair satisfies the optional adjunction bridge. -/
def toAdjointBridge (E : ExtensionRestriction α β) :
    AdjointBridge E.toPaired where
  adjunction := E.adjunction

end ExtensionRestriction
end CausalGeometry
