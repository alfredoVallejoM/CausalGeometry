import CausalGeometry.Calculus.LinearInvariantPaths
import CausalGeometry.Exchange.LinearizedCausalAction

/-!
# Persistent domains of the independently constructed causal actions

Here a continuation is a further admitted EXCHANGE route with the same causal
frontiers. Adding new events/changing frontiers is not silently quantified.
No Artin quotient, inverse, YB law or compatibility hypothesis is required.
-/
namespace CausalGeometry.Exchange.Persistent

open CategoryTheory EventSystem LocalOperator OperatorTransport LinearizedAction
noncomputable section
universe u v w
variable {K : Type u} [CommRing K] {A B C : Type u}
variable {Event : Type v} {Label : Type w} {S : EventSystem Event Label}

/-- Native persistent submodule over each old CausalPath. -/
abbrev domain (f : A → B) (R : PairOperator A) (T : PairOperator B)
    {U V : Configuration S} (p : CausalPath S U V) :=
  PersistentLinear.domain (action K R U V) (action K T U V)
    (fun q => coefficient K f q.length) p

@[simp] theorem mem_domain (f : A → B) (R : PairOperator A) (T : PairOperator B)
    {U V : Configuration S} (p : CausalPath S U V) (x : Sized A p.length →₀ K) :
    x ∈ domain (K := K) f R T p ↔
      ∀ (q : CausalPath S U V) (r : Route p q), LinearizedAction.defect f R T r x = 0 :=
  Iff.rfl

theorem stable (f : A → B) (R : PairOperator A) (T : PairOperator B)
    {U V : Configuration S} {p q : CausalPath S U V} (r : Route p q)
    {x : Sized A p.length →₀ K} (hx : x ∈ domain (K := K) f R T p) :
    routeMap R r x ∈ domain (K := K) f R T q :=
  PersistentLinear.domain_stable _ _ _ r hx

abbrev generatorDomain (f : A → B) (R : PairOperator A) (T : PairOperator B)
    {U V : Configuration S} (p : CausalPath S U V) :=
  LinearInvariant.Paths.generatorDomain (action K R U V) (action K T U V)
    (fun q => coefficient K f q.length) p

/-- The constructed domain is precisely the largest stable part of the local kernels. -/
theorem domain_eq_core (f : A → B) (R : PairOperator A) (T : PairOperator B)
    {U V : Configuration S} (p : CausalPath S U V) :
    domain (K := K) f R T p =
      LinearInvariant.core (action K R U V) (generatorDomain f R T) p :=
  LinearInvariant.Paths.persistent_eq_core_generators _ _ _ p

abbrev restrictedAction (f : A → B) (R : PairOperator A) (T : PairOperator B)
    (U V : Configuration S) :=
  PersistentLinear.restricted (action K R U V) (action K T U V)
    (fun p => coefficient K f p.length)

/-- Actual natural transport on the new domain; it need not be invertible. -/
abbrev transport (f : A → B) (R : PairOperator A) (T : PairOperator B)
    (U V : Configuration S) :=
  PersistentLinear.transport (action K R U V) (action K T U V)
    (fun p => coefficient K f p.length)

/-- I5's globally compatible sector is recovered without changing its producer. -/
theorem domain_top_of_intertwines (f : A → B) (R : PairOperator A) (T : PairOperator B)
    (hf : Intertwines f R T) {U V : Configuration S} (p : CausalPath S U V) :
    domain (K := K) f R T p = ⊤ := by
  apply top_unique
  intro x _ q r
  simpa using LinearMap.congr_fun
    (LinearizedAction.defect_zero_of_intertwines (K := K) f R T hf r) x

/-- This safe intersection can be smaller than the domain of the composite. -/
theorem composition_safe (f : A → B) (g : B → C)
    (R : PairOperator A) (T : PairOperator B) (W : PairOperator C)
    {U V : Configuration S} (p : CausalPath S U V) :
    domain (K := K) f R T p ⊓ (domain g T W p).comap (coefficient K f p.length) ≤
      domain (K := K) (g ∘ f) R W p := by
  intro x hx q r
  rw [LinearizedAction.defect_comp_coefficient]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, hx.2 q r, hx.1 q r, map_zero, add_zero]

/-- The two directions are checked separately, using the original PairedTransform. -/
theorem sourceRoundTrip_safe (P : PairedTransform A B)
    (R : PairOperator A) (T : PairOperator B)
    {U V : Configuration S} (p : CausalPath S U V) :
    domain (K := K) P.forward R T p ⊓
      (domain P.backward T R p).comap (coefficient K P.forward p.length) ≤
      domain (K := K) P.sourceRoundTrip R R p :=
  composition_safe P.forward P.backward R T R p

theorem targetRoundTrip_safe (P : PairedTransform A B)
    (R : PairOperator A) (T : PairOperator B)
    {U V : Configuration S} (p : CausalPath S U V) :
    domain (K := K) P.backward T R p ⊓
      (domain P.forward R T p).comap (coefficient K P.backward p.length) ≤
      domain (K := K) P.targetRoundTrip T T p :=
  composition_safe P.backward P.forward T R T p

/-- Individual-state compatibility is distinct from cancellations in a linear combination. -/
def stateDomain (f : A → B) (R : PairOperator A) (T : PairOperator B)
    {U V : Configuration S} (p : CausalPath S U V) : Set (Sized A p.length) :=
  {x | ∀ (q : CausalPath S U V) (r : Route p q),
    (CausalOperator.action T U V).map r (mapSized f x) =
      mapSized f ((CausalOperator.action R U V).map r x)}

theorem basis_mem_iff [Nontrivial K] (f : A → B) (R : PairOperator A) (T : PairOperator B)
    {U V : Configuration S} (p : CausalPath S U V) (x : Sized A p.length) :
    ModuleCat.freeMk x ∈ domain (K := K) f R T p ↔ x ∈ stateDomain f R T p := by
  constructor
  · intro h q r
    have hd := h q r
    rw [LinearizedAction.defect_basis, sub_eq_zero] at hd
    exact LinearizedAction.basis_injective (K := K) hd
  · intro h q r
    rw [LinearizedAction.defect_basis, h q r, sub_self]

/-- Only inclusion is justified. Persistent formal sums can cancel even when
none of their individual basis states is compatible. -/
theorem span_states_le [Nontrivial K] (f : A → B) (R : PairOperator A) (T : PairOperator B)
    {U V : Configuration S} (p : CausalPath S U V) :
    Submodule.span K ((ModuleCat.freeMk (R := K)) '' stateDomain f R T p) ≤
      domain (K := K) f R T p := by
  apply Submodule.span_le.mpr
  rintro z ⟨x, hx, rfl⟩
  exact (basis_mem_iff f R T p x).mpr hx

/-- A constant fiber is derived from a history length, not an extra event. -/
def constantState (a : A) (n : Nat) : Sized A n := ⟨List.replicate n a, by simp⟩

theorem step_constant (R : PairOperator A) (a : A) (ha : R (a,a) = (a,a))
    (i n : Nat) : stepList R i (List.replicate n a) = List.replicate n a := by
  induction i generalizing n with
  | zero => cases n with
    | zero => rfl
    | succ n => cases n <;> simp [stepList, List.replicate_succ, ha]
  | succ i ih => cases n <;> simp [stepList, List.replicate_succ, ih]

@[simp] theorem map_constant (f : A → B) (a : A) (n : Nat) :
    mapSized f (constantState a n) = constantState (f a) n := by
  apply Subtype.ext
  simp [mapSized, constantState]

theorem route_constant (R : PairOperator A) (a : A) (ha : R (a,a) = (a,a))
    {U V : Configuration S} {p q : CausalPath S U V} (r : Route p q) :
    (CausalOperator.action R U V).map r (constantState a p.length) =
      constantState a q.length := by
  induction r with
  | nil => rfl
  | @cons q z r s ih =>
      apply Subtype.ext
      change stepList R s.position
        (((CausalOperator.action R U V).map r) (constantState a p.length)).val =
        (constantState a z.length).val
      rw [ih]
      simp only [constantState, step_constant R a ha, s.length_eq]

/-- A reusable positive producer, valid even when f does not globally intertwine. -/
theorem constant_basis_mem [Nontrivial K] (f : A → B)
    (R : PairOperator A) (T : PairOperator B) (a : A)
    (hR : R (a,a) = (a,a)) (hT : T (f a,f a) = (f a,f a))
    {U V : Configuration S} (p : CausalPath S U V) :
    ModuleCat.freeMk (constantState a p.length) ∈ domain (K := K) f R T p := by
  apply (basis_mem_iff f R T p _).mpr
  intro q r
  rw [map_constant, route_constant T (f a) hT, route_constant R a hR, map_constant]

end CausalGeometry.Exchange.Persistent
