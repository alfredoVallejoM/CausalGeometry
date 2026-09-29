import CausalGeometry.Calculus.LinearInvariantCore
import CausalGeometry.Calculus.LinearSquareDefect

/-!
# Persistent compatibility without assuming naturality

The component maps tau may fail to intertwine. Their maximal persistent
subdomain is constructed, proved stable, and made into an actual functor.
Compatibility is required at every finite prefix, not only at a final output.
-/
namespace CausalGeometry.PersistentLinear

open CategoryTheory
universe u v w
variable {K : Type u} [CommRing K] {C : Type v} [Category.{w} C]
variable (F G : C ⥤ ModuleCat.{u} K)
variable (tau : ∀ X, F.obj X →ₗ[K] G.obj X)

/-- This is the heterogeneous square defect already defined in I6. -/
def defect {X Y : C} (r : X ⟶ Y) : F.obj X →ₗ[K] G.obj Y :=
  LinearSquare.defect (F.map r).hom (G.map r).hom (tau X) (tau Y)

@[simp] theorem defect_apply {X Y : C} (r : X ⟶ Y) (x : F.obj X) :
    defect F G tau r x = G.map r (tau X x) - tau Y (F.map r x) := rfl

/-- Simultaneous compatibility with every admitted finite continuation. -/
def domain (X : C) : Submodule K (F.obj X) where
  carrier := {x | ∀ (Y : C) (r : X ⟶ Y), defect F G tau r x = 0}
  zero_mem' := by intro Y r; exact map_zero _
  add_mem' := by
    intro x y hx hy Y r
    rw [map_add, hx Y r, hy Y r, add_zero]
  smul_mem' := by
    intro a x hx Y r
    rw [map_smul, hx Y r, smul_zero]

@[simp] theorem mem_domain (X : C) (x : F.obj X) :
    x ∈ domain F G tau X ↔
      ∀ (Y : C) (r : X ⟶ Y), G.map r (tau X x) = tau Y (F.map r x) := by
  constructor
  · intro h Y r; exact sub_eq_zero.mp (h Y r)
  · intro h Y r; exact sub_eq_zero.mpr (h Y r)

/-- A prefix and its composite with every tail supply exactly the needed cancellation. -/
theorem domain_stable : LinearInvariant.Stable F (domain F G tau) := by
  intro X Y r x hx
  apply (mem_domain F G tau Y _).mpr
  intro Z t
  have hr := (mem_domain F G tau X x).mp hx Y r
  have hrt := (mem_domain F G tau X x).mp hx Z (r ≫ t)
  simpa only [Functor.map_comp, ModuleCat.comp_apply, hr] using hrt

/-- Taking the invariant interior no longer changes the persistent domain. -/
theorem domain_core (X : C) :
    LinearInvariant.core F (domain F G tau) X = domain F G tau X :=
  LinearInvariant.core_eq_of_stable F _ (domain_stable F G tau) X

/-- Maximality is pointwise among all submodule families satisfying every square. -/
theorem domain_maximal (L : LinearInvariant.Family F) :
    (∀ X, L X ≤ domain F G tau X) ↔
      ∀ (X Y : C) (r : X ⟶ Y) (x : F.obj X),
        x ∈ L X → G.map r (tau X x) = tau Y (F.map r x) := by
  constructor
  · intro h X Y r x hx; exact (mem_domain F G tau X x).mp (h X hx) Y r
  · intro h X x hx; exact (mem_domain F G tau X x).mpr (fun Y r => h X Y r x hx)

abbrev restricted : C ⥤ ModuleCat.{u} K :=
  LinearInvariant.restrict F (domain F G tau) (domain_stable F G tau)

/-- Restricting to the constructed domain repairs naturality, not invertibility. -/
def transport : restricted F G tau ⟶ G where
  app X := ModuleCat.ofHom ((tau X).comp (domain F G tau X).subtype)
  naturality {X Y} r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change tau Y (F.map r x.val) = G.map r (tau X x.val)
    exact ((mem_domain F G tau X x.val).mp x.property Y r).symm

theorem domain_eq_top_of_natural
    (h : ∀ (X Y : C) (r : X ⟶ Y) (x : F.obj X),
      G.map r (tau X x) = tau Y (F.map r x)) (X : C) :
    domain F G tau X = ⊤ := by
  apply top_unique
  intro x _
  exact (mem_domain F G tau X x).mpr (fun Y r => h X Y r x)

/-- Sequential coefficient changes are safe on this intersection. The reverse
inclusion is not asserted: nonzero intermediate defects can cancel. -/
theorem composition_domain (H : C ⥤ ModuleCat.{u} K)
    (sigma : ∀ X, G.obj X →ₗ[K] H.obj X) (X : C) :
    domain F G tau X ⊓ (domain G H sigma X).comap (tau X) ≤
      domain F H (fun Y => (sigma Y).comp (tau Y)) X := by
  intro x hx
  apply (mem_domain F H _ X x).mpr
  intro Y r
  have ht := (mem_domain F G tau X x).mp hx.1 Y r
  have hs := (mem_domain G H sigma X (tau X x)).mp hx.2 Y r
  change H.map r (sigma X (tau X x)) = sigma Y (tau Y (F.map r x))
  rw [hs, ht]

/-- A compatible but information-losing observation can only enlarge the safe domain. -/
theorem observation_domain (H : C ⥤ ModuleCat.{u} K) (sigma : G ⟶ H) (X : C) :
    domain F G tau X ≤ domain F H (fun Y => (sigma.app Y).hom.comp (tau Y)) X := by
  intro x hx
  apply (mem_domain F H _ X x).mpr
  intro Y r
  have ht := (mem_domain F G tau X x).mp hx Y r
  have hs := congrArg (fun h : G.obj X ⟶ H.obj Y => h (tau X x)) (sigma.naturality r)
  change H.map r (sigma.app X (tau X x)) = sigma.app Y (tau Y (F.map r x))
  exact hs.symm.trans (congrArg (fun y => sigma.app Y y) ht)

end CausalGeometry.PersistentLinear
