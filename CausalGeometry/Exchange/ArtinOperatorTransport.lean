import CausalGeometry.Exchange.ArtinPresentation
import CausalGeometry.Exchange.OperatorTransport

/-! Natural coefficient transport before and after the native Artin quotient. -/
namespace CausalGeometry.Exchange.Artin

open CategoryTheory LocalOperator OperatorTransport
universe u
variable {A B : Type u}

theorem map_word (f : A → B) (R : PairOperator A) (T : PairOperator B)
    (hf : Intertwines f R T) {n : Nat} {p q : Words n} (r : p ⟶ q)
    (xs : Sized A (n + 1)) :
    mapSized f (((wordAction R n).map r) xs) =
      ((wordAction T n).map r) (mapSized f xs) := by
  induction r with
  | nil => rfl
  | cons r i ih =>
      change mapSized f (act R i (((wordAction R n).map r) xs)) =
        act T i (((wordAction T n).map r) (mapSized f xs))
      rw [map_act f R T hf, ih]

/-- Morphism of the positive representations; both YB laws are named hypotheses. -/
def positiveTransport (f : A → B) (R : PairOperator A) (T : PairOperator B)
    (hf : Intertwines f R T) (hR : YangBaxter R) (hT : YangBaxter T) (n : Nat) :
    positiveAction R hR n ⟶ positiveAction T hT n where
  app _ := TypeCat.ofHom (mapSized f)
  naturality {p q} r := by
    refine CategoryTheory.Quotient.induction (r := Relation n) ?_ r
    intro X Y r
    apply TypeCat.homEquiv.injective
    funext xs
    exact map_word f R T hf r xs

@[simp] theorem positiveTransport_app (f : A → B) (R : PairOperator A) (T : PairOperator B)
    (hf : Intertwines f R T) (hR : YangBaxter R) (hT : YangBaxter T) (n : Nat)
    (p : Positive n) (xs : Sized A (n + 1)) :
    (positiveTransport f R T hf hR hT n).app p xs = mapSized f xs := rfl

end CausalGeometry.Exchange.Artin
