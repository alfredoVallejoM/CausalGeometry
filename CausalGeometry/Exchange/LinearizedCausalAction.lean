import CausalGeometry.Calculus.LinearSquareDefect
import CausalGeometry.Exchange.CausalOperatorTransport
import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-!
# Canonical free-module linearization of actual causal actions

ModuleCat.free is used unchanged. A basis element is an observed state of an
existing CausalPath, not a primitive event and not an arbitrary coordinate.
This makes noncommutation measurable without assuming local intertwining.
-/
namespace CausalGeometry.Exchange.LinearizedAction

open CategoryTheory EventSystem LocalOperator OperatorTransport
noncomputable section
universe u v w
variable {K : Type u} [CommRing K]
variable {A B C X Y Z : Type u}
variable {Event : Type v} {Label : Type w} {S : EventSystem Event Label}

/-- The native free functor on a function, exposed as its underlying linear map. -/
def freeMap (K : Type u) [CommRing K] {X Y : Type u} (f : X → Y) :
    (X →₀ K) →ₗ[K] (Y →₀ K) :=
  ((ModuleCat.free K).map (TypeCat.ofHom f)).hom

@[simp] theorem freeMap_basis (f : X → Y) (x : X) :
    freeMap K f (ModuleCat.freeMk x) = ModuleCat.freeMk (f x) :=
  ModuleCat.free_map_apply (TypeCat.ofHom f) x

@[simp] theorem freeMap_id : freeMap K (id : X → X) = LinearMap.id :=
  congrArg (fun h : (ModuleCat.free K).obj X ⟶ (ModuleCat.free K).obj X => h.hom)
    ((ModuleCat.free K).map_id X)

theorem freeMap_comp (f : X → Y) (g : Y → Z) :
    freeMap K (g ∘ f) = (freeMap K g).comp (freeMap K f) :=
  congrArg (fun h : (ModuleCat.free K).obj X ⟶ (ModuleCat.free K).obj Z => h.hom)
    ((ModuleCat.free K).map_comp (TypeCat.ofHom f) (TypeCat.ofHom g))

/-- Free basis observation does not erase distinctions when 1≠0. -/
theorem basis_injective [Nontrivial K] :
    Function.Injective (ModuleCat.freeMk (R := K) : X → (X →₀ K)) := by
  classical
  intro x y h
  by_contra hxy
  have hv := congrArg (fun a : X →₀ K => a x) h
  simp [ModuleCat.freeMk, hxy, Ne.symm hxy] at hv

theorem freeMap_injective [Nontrivial K] :
    Function.Injective (freeMap K : (X → Y) → ((X →₀ K) →ₗ[K] (Y →₀ K))) := by
  intro f g h
  funext x
  apply basis_injective (K := K)
  have hx := LinearMap.congr_fun h (ModuleCat.freeMk x)
  simpa only [freeMap_basis] using hx

/-- Linearize the independently constructed causal action, not its Artin image. -/
def action (K : Type u) [CommRing K] (R : PairOperator A) (U V : Configuration S) :=
  CausalOperator.action R U V ⋙ ModuleCat.free K

def routeMap (R : PairOperator A) {U V : Configuration S}
    {p q : CausalPath S U V} (r : Route p q) :
    (Sized A p.length →₀ K) →ₗ[K] (Sized A q.length →₀ K) :=
  ((action K R U V).map r).hom

@[simp] theorem routeMap_basis (R : PairOperator A) {U V : Configuration S}
    {p q : CausalPath S U V} (r : Route p q) (x : Sized A p.length) :
    routeMap (K := K) R r (ModuleCat.freeMk x) =
      ModuleCat.freeMk (((CausalOperator.action R U V).map r) x) :=
  ModuleCat.free_map_apply ((CausalOperator.action R U V).map r) x

@[simp] theorem routeMap_nil (R : PairOperator A) {U V : Configuration S}
    (p : CausalPath S U V) :
    routeMap (K := K) R (Quiver.Path.nil : Route p p) = LinearMap.id :=
  congrArg (fun h : (action K R U V).obj p ⟶ (action K R U V).obj p => h.hom)
    ((action K R U V).map_id p)

theorem routeMap_comp (R : PairOperator A) {U V : Configuration S}
    {p q s : CausalPath S U V} (r : Route p q) (t : Route q s) :
    routeMap (K := K) R (r.comp t) = (routeMap R t).comp (routeMap R r) :=
  congrArg (fun h : (action K R U V).obj p ⟶ (action K R U V).obj s => h.hom)
    ((action K R U V).map_comp r t)

/-- Coefficient transport may be noninjective and fail to intertwine. -/
def coefficient (K : Type u) [CommRing K] (f : A → B) (n : Nat) :=
  freeMap K (mapSized (n := n) f)

@[simp] theorem coefficient_basis (f : A → B) (n : Nat) (x : Sized A n) :
    coefficient K f n (ModuleCat.freeMk x) = ModuleCat.freeMk (mapSized f x) :=
  freeMap_basis (K := K) (mapSized f) x

/-- Two coefficient changes compose without any operator compatibility assumption. -/
theorem coefficient_comp (f : A → B) (g : B → C) (n : Nat) :
    coefficient K (g ∘ f) n = (coefficient K g n).comp (coefficient K f n) := by
  unfold coefficient
  rw [← freeMap_comp]
  apply congrArg (freeMap K)
  funext x
  exact (mapSized_comp f g x).symm

/-- Defect on a WHOLE causal route; the two endpoint transports are explicit. -/
def defect (f : A → B) (R : PairOperator A) (T : PairOperator B)
    {U V : Configuration S} {p q : CausalPath S U V} (r : Route p q) :=
  LinearSquare.defect (routeMap (K := K) R r) (routeMap T r)
    (coefficient K f p.length) (coefficient K f q.length)

@[simp] theorem defect_nil (f : A → B) (R : PairOperator A) (T : PairOperator B)
    {U V : Configuration S} (p : CausalPath S U V) :
    defect (K := K) f R T (Quiver.Path.nil : Route p p) = 0 := by
  simp only [defect, routeMap_nil, LinearSquare.identity_edges]

@[simp] theorem defect_basis (f : A → B) (R : PairOperator A) (T : PairOperator B)
    {U V : Configuration S} {p q : CausalPath S U V} (r : Route p q)
    (x : Sized A p.length) :
    defect (K := K) f R T r (ModuleCat.freeMk x) =
      ModuleCat.freeMk (((CausalOperator.action T U V).map r) (mapSized f x)) -
      ModuleCat.freeMk (mapSized f (((CausalOperator.action R U V).map r) x)) := by
  simp only [defect, LinearSquare.defect_apply, routeMap_basis, coefficient_basis]

/-- The defect is the difference of the free images of two independently computed functions. -/
theorem defect_as_difference (f : A → B) (R : PairOperator A) (T : PairOperator B)
    {U V : Configuration S} {p q : CausalPath S U V} (r : Route p q) :
    defect (K := K) f R T r =
      freeMap K (fun x => ((CausalOperator.action T U V).map r) (mapSized f x)) -
      freeMap K (fun x => mapSized f (((CausalOperator.action R U V).map r) x)) := by
  change (freeMap K (fun x => ((CausalOperator.action T U V).map r) x)).comp
      (freeMap K (mapSized f)) - (freeMap K (mapSized f)).comp
      (freeMap K (fun x => ((CausalOperator.action R U V).map r) x)) = _
  rw [← freeMap_comp, ← freeMap_comp]
  rfl

/-- Exact converse: nontrivial free coefficients retain all state-level discrepancies. -/
theorem defect_zero_iff [Nontrivial K] (f : A → B)
    (R : PairOperator A) (T : PairOperator B)
    {U V : Configuration S} {p q : CausalPath S U V} (r : Route p q) :
    defect (K := K) f R T r = 0 ↔ ∀ x : Sized A p.length,
      ((CausalOperator.action T U V).map r) (mapSized f x) =
        mapSized f (((CausalOperator.action R U V).map r) x) := by
  rw [defect_as_difference, sub_eq_zero]
  constructor
  · intro h x
    exact congrFun (freeMap_injective (K := K) h) x
  · intro h
    exact congrArg (freeMap K) (funext h)

/-- Recover I5 exactly as the zero-defect sector, without weakening I5. -/
theorem defect_zero_of_intertwines (f : A → B)
    (R : PairOperator A) (T : PairOperator B) (hf : Intertwines f R T)
    {U V : Configuration S} {p q : CausalPath S U V} (r : Route p q) :
    defect (K := K) f R T r = 0 := by
  rw [defect_as_difference]
  have h : (fun x => ((CausalOperator.action T U V).map r) (mapSized f x)) =
      (fun x => mapSized f (((CausalOperator.action R U V).map r) x)) :=
    funext (fun x => (CausalOperatorTransport.map_route f R T hf r x).symm)
  rw [h, sub_self]

/-- Exact composition of coefficient changes; no compatibility assumption. -/
theorem defect_comp_coefficient (f : A → B) (g : B → C)
    (R : PairOperator A) (T : PairOperator B) (W : PairOperator C)
    {U V : Configuration S} {p q : CausalPath S U V} (r : Route p q) :
    defect (K := K) (g ∘ f) R W r =
      (defect g T W r).comp (coefficient K f p.length) +
        (coefficient K g q.length).comp (defect f R T r) := by
  unfold defect
  rw [coefficient_comp, coefficient_comp]
  exact LinearSquare.horizontal _ _ _ _ _ _ _

/-- Exact propagation along causal routes: local failures may cancel, not only accumulate. -/
theorem defect_comp_route (f : A → B) (R : PairOperator A) (T : PairOperator B)
    {U V : Configuration S} {p q s : CausalPath S U V}
    (r : Route p q) (t : Route q s) :
    defect (K := K) f R T (r.comp t) =
      (routeMap T t).comp (defect f R T r) +
        (defect f R T t).comp (routeMap R r) := by
  unfold defect
  rw [routeMap_comp, routeMap_comp]
  exact LinearSquare.vertical _ _ _ _ _ _ _

/-- The original pair is consumed directly; its backward law remains independent. -/
theorem sourceRoundTrip_defect (P : PairedTransform A B)
    (R : PairOperator A) (T : PairOperator B)
    {U V : Configuration S} {p q : CausalPath S U V} (r : Route p q) :
    defect (K := K) P.sourceRoundTrip R R r =
      (defect P.backward T R r).comp (coefficient K P.forward p.length) +
        (coefficient K P.backward q.length).comp (defect P.forward R T r) :=
  defect_comp_coefficient P.forward P.backward R T R r

theorem targetRoundTrip_defect (P : PairedTransform A B)
    (R : PairOperator A) (T : PairOperator B)
    {U V : Configuration S} {p q : CausalPath S U V} (r : Route p q) :
    defect (K := K) P.targetRoundTrip T T r =
      (defect P.forward R T r).comp (coefficient K P.backward p.length) +
        (coefficient K P.forward q.length).comp (defect P.backward T R r) :=
  defect_comp_coefficient P.backward P.forward T R T r

/-- Forget the state label and retain total coefficient only. This is not a
probability assumption: coefficients may be negative. -/
def augmentation (K : Type u) [CommRing K] (X : Type u) : (X →₀ K) →ₗ[K] K :=
  (ModuleCat.freeDesc (M := ModuleCat.of K K) (TypeCat.ofHom (fun _ : X => (1 : K)))).hom

@[simp] theorem augmentation_basis (x : X) :
    augmentation K X (ModuleCat.freeMk x) = 1 :=
  ModuleCat.freeDesc_apply (TypeCat.ofHom (fun _ : X => (1 : K))) x

/-- The scalar total erases EVERY such naturality defect, even nonzero ones. -/
theorem augmentation_defect (f : A → B) (R : PairOperator A) (T : PairOperator B)
    {U V : Configuration S} {p q : CausalPath S U V} (r : Route p q) :
    (augmentation K (Sized B q.length)).comp (defect (K := K) f R T r) = 0 := by
  have h : ModuleCat.ofHom
      ((augmentation K (Sized B q.length)).comp (defect (K := K) f R T r)) =
      ModuleCat.ofHom (0 : (Sized A p.length →₀ K) →ₗ[K] K) := by
    apply ModuleCat.free_hom_ext
    intro x
    change augmentation K (Sized B q.length)
      (defect (K := K) f R T r (ModuleCat.freeMk x)) = 0
    rw [defect_basis, map_sub, augmentation_basis, augmentation_basis, sub_self]
  exact congrArg
    (fun h : (ModuleCat.free K).obj (Sized A p.length) ⟶ ModuleCat.of K K => h.hom) h

end CausalGeometry.Exchange.LinearizedAction
