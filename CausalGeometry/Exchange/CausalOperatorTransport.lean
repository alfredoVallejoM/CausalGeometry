import CausalGeometry.Exchange.OperatorTransport
import CausalGeometry.Exchange.CausalOperator
import CausalGeometry.Foundation.PairedTransform

/-!
# Natural coefficient transport along actual causal exchange routes

The primitive PairedTransform is consumed unchanged. Forward/backward
intertwining are independent hypotheses. Compatible round trips commute with
exchanges but are not asserted to be identities or adjunctions.
-/
namespace CausalGeometry.Exchange.CausalOperatorTransport

open CategoryTheory EventSystem LocalOperator OperatorTransport
universe u v w
variable {Event : Type u} {Label : Type v} {S : EventSystem Event Label}
variable {A B C : Type w}

/-- Extending the local square to every route requires induction on the actual
exchange path, not enumeration of all event histories. -/
theorem map_route (f : A → B) (R : PairOperator A) (T : PairOperator B)
    (hf : Intertwines f R T) {U V : Configuration S} {p q : CausalPath S U V}
    (r : Route p q) (xs : Sized A p.length) :
    mapSized f (((CausalOperator.action R U V).map r) xs) =
      ((CausalOperator.action T U V).map r) (mapSized f xs) := by
  induction r with
  | nil => rfl
  | cons r s ih =>
      apply Subtype.ext
      change (stepList R s.position
        (((CausalOperator.action R U V).map r) xs).val).map f =
        stepList T s.position
          (((CausalOperator.action T U V).map r) (mapSized f xs)).val
      rw [map_stepList f R T hf]
      exact congrArg (stepList T s.position) (congrArg Subtype.val ih)

/-- A real natural transformation of the existing fiber functors. -/
def transport (f : A → B) (R : PairOperator A) (T : PairOperator B)
    (hf : Intertwines f R T) (U V : Configuration S) :
    CausalOperator.action R U V ⟶ CausalOperator.action T U V where
  app p := TypeCat.ofHom (mapSized f)
  naturality {p q} r := by
    apply TypeCat.homEquiv.injective
    funext xs
    exact map_route f R T hf r xs

@[simp] theorem transport_app (f : A → B) (R : PairOperator A) (T : PairOperator B)
    (hf : Intertwines f R T) (U V : Configuration S) (p : HistoryCategory U V)
    (xs : Sized A p.length) :
    (transport f R T hf U V).app p xs = mapSized f xs := rfl

theorem transport_id (R : PairOperator A) (U V : Configuration S) :
    transport id R R (intertwines_id R) U V = 𝟙 (CausalOperator.action R U V) := by
  apply NatTrans.ext
  funext p
  apply TypeCat.homEquiv.injective
  funext xs
  exact mapSized_id xs

theorem transport_comp (f : A → B) (g : B → C)
    (R : PairOperator A) (T : PairOperator B) (W : PairOperator C)
    (hf : Intertwines f R T) (hg : Intertwines g T W) (U V : Configuration S) :
    transport f R T hf U V ≫ transport g T W hg U V =
      transport (g ∘ f) R W (intertwines_comp f g R T W hf hg) U V := by
  apply NatTrans.ext
  funext p
  apply TypeCat.homEquiv.injective
  funext xs
  exact mapSized_comp f g xs

/-- Same-size change of coefficients as an isomorphism when an actual
coefficient equivalence is provided. This is not a global assumption on Phi. -/
def coefficientIso (e : A ≃ B) (n : Nat) : Sized A n ≅ Sized B n where
  hom := TypeCat.ofHom (mapSized e)
  inv := TypeCat.ofHom (mapSized e.symm)
  hom_inv_id := by
    apply TypeCat.homEquiv.injective
    funext xs
    apply Subtype.ext
    simp [mapSized, List.map_map, Function.comp_def]
  inv_hom_id := by
    apply TypeCat.homEquiv.injective
    funext xs
    apply Subtype.ext
    simp [mapSized, List.map_map, Function.comp_def]

def transportIso (e : A ≃ B) (R : PairOperator A) (T : PairOperator B)
    (h : Intertwines e R T) (U V : Configuration S) :
    CausalOperator.action R U V ≅ CausalOperator.action T U V :=
  NatIso.ofComponents (fun p => coefficientIso e p.length) (by
    intro p q r
    apply TypeCat.homEquiv.injective
    funext xs
    exact map_route e R T h r xs)

/-- The two laws belong to the bridge, not to PairedTransform itself. -/
structure Compatible (P : PairedTransform A B)
    (R : PairOperator A) (T : PairOperator B) : Prop where
  forward : Intertwines P.forward R T
  backward : Intertwines P.backward T R

def forward (P : PairedTransform A B) (R : PairOperator A) (T : PairOperator B)
    (h : Compatible P R T) (U V : Configuration S) :
    CausalOperator.action R U V ⟶ CausalOperator.action T U V :=
  transport P.forward R T h.forward U V

def backward (P : PairedTransform A B) (R : PairOperator A) (T : PairOperator B)
    (h : Compatible P R T) (U V : Configuration S) :
    CausalOperator.action T U V ⟶ CausalOperator.action R U V :=
  transport P.backward T R h.backward U V

theorem compatible_comp (P : PairedTransform A B) (Q : PairedTransform B C)
    (R : PairOperator A) (T : PairOperator B) (W : PairOperator C)
    (hP : Compatible P R T) (hQ : Compatible Q T W) : Compatible (P.comp Q) R W where
  forward := intertwines_comp P.forward Q.forward R T W hP.forward hQ.forward
  backward := intertwines_comp Q.backward P.backward W T R hQ.backward hP.backward

theorem sourceRoundTrip_intertwines (P : PairedTransform A B)
    (R : PairOperator A) (T : PairOperator B) (h : Compatible P R T) :
    Intertwines P.sourceRoundTrip R R :=
  intertwines_comp P.forward P.backward R T R h.forward h.backward

theorem targetRoundTrip_intertwines (P : PairedTransform A B)
    (R : PairOperator A) (T : PairOperator B) (h : Compatible P R T) :
    Intertwines P.targetRoundTrip T T :=
  intertwines_comp P.backward P.forward T R T h.backward h.forward

/-- Both rounds commute with the action; they remain potentially nonidentity. -/
theorem sourceRoundTrip_route (P : PairedTransform A B)
    (R : PairOperator A) (T : PairOperator B) (h : Compatible P R T)
    {U V : Configuration S} {p q : CausalPath S U V}
    (r : Route p q) (xs : Sized A p.length) :
    mapSized P.sourceRoundTrip (((CausalOperator.action R U V).map r) xs) =
      ((CausalOperator.action R U V).map r) (mapSized P.sourceRoundTrip xs) :=
  map_route _ R R (sourceRoundTrip_intertwines P R T h) r xs

theorem targetRoundTrip_route (P : PairedTransform A B)
    (R : PairOperator A) (T : PairOperator B) (h : Compatible P R T)
    {U V : Configuration S} {p q : CausalPath S U V}
    (r : Route p q) (xs : Sized B p.length) :
    mapSized P.targetRoundTrip (((CausalOperator.action T U V).map r) xs) =
      ((CausalOperator.action T U V).map r) (mapSized P.targetRoundTrip xs) :=
  map_route _ T T (targetRoundTrip_intertwines P R T h) r xs

end CausalGeometry.Exchange.CausalOperatorTransport
