import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Tactic

/-!
# The invariant interior of a family of linear constraints

The construction uses the given functor and native submodules. It neither
chooses coordinates nor enumerates paths. All quantifiers refer to morphisms
of the specified category, not to arbitrary physical futures.
-/
namespace CausalGeometry.LinearInvariant

open CategoryTheory
universe u v w
variable {K : Type u} [CommRing K] {C : Type v} [Category.{w} C]
variable (F : C ⥤ ModuleCat.{u} K)

abbrev Family := (X : C) → Submodule K (F.obj X)

/-- Stability under the actual process maps of F. -/
def Stable (L : Family F) : Prop :=
  ∀ ⦃X Y : C⦄ (r : X ⟶ Y) ⦃x : F.obj X⦄, x ∈ L X → F.map r x ∈ L Y

/-- States which satisfy the specified constraints after EVERY admitted continuation. -/
def core (L : Family F) (X : C) : Submodule K (F.obj X) where
  carrier := {x | ∀ (Y : C) (r : X ⟶ Y), F.map r x ∈ L Y}
  zero_mem' := by intro Y r; simpa using (L Y).zero_mem
  add_mem' := by
    intro x y hx hy Y r
    simpa only [map_add] using (L Y).add_mem (hx Y r) (hy Y r)
  smul_mem' := by
    intro a x hx Y r
    simpa only [map_smul] using (L Y).smul_mem a (hx Y r)

@[simp] theorem mem_core (L : Family F) (X : C) (x : F.obj X) :
    x ∈ core F L X ↔ ∀ (Y : C) (r : X ⟶ Y), F.map r x ∈ L Y := Iff.rfl

/-- The identity continuation makes the invariant core an interior, not a closure. -/
theorem core_le (L : Family F) (X : C) : core F L X ≤ L X := by
  intro x hx
  simpa using hx X (𝟙 X)

theorem core_stable (L : Family F) : Stable F (core F L) := by
  intro X Y r x hx Z t
  simpa only [Functor.map_comp, ModuleCat.comp_apply] using hx Z (r ≫ t)

/-- Maximality among stable families contained in the original constraints. -/
theorem le_core (L M : Family F) (hM : Stable F M)
    (hML : ∀ X, M X ≤ L X) (X : C) : M X ≤ core F L X := by
  intro x hx Y r
  exact hML Y (hM r hx)

theorem core_mono (L M : Family F) (h : ∀ X, L X ≤ M X) (X : C) :
    core F L X ≤ core F M X := by
  intro x hx Y r
  exact h Y (hx Y r)

theorem core_eq_of_stable (L : Family F) (hL : Stable F L) (X : C) :
    core F L X = L X :=
  le_antisymm (core_le F L X) (le_core F L L hL (fun _ => le_rfl) X)

theorem stable_iff_core_eq (L : Family F) :
    Stable F L ↔ ∀ X, core F L X = L X := by
  constructor
  · exact fun h X => core_eq_of_stable F L h X
  · intro h X Y r x hx
    have hx' : x ∈ core F L X := by rw [h X]; exact hx
    have hy := core_stable F L r hx'
    rwa [h Y] at hy

@[simp] theorem core_idempotent (L : Family F) (X : C) :
    core F (core F L) X = core F L X :=
  core_eq_of_stable F _ (core_stable F L) X

/-- Stable restrictions are native module functors with actual restricted maps. -/
def restrict (L : Family F) (hL : Stable F L) : C ⥤ ModuleCat.{u} K where
  obj X := ModuleCat.of K (L X)
  map {X Y} r := ModuleCat.ofHom
    { toFun := fun x => ⟨F.map r x.val, hL r x.property⟩
      map_add' := by intro x y; apply Subtype.ext; exact (F.map r).hom.map_add _ _
      map_smul' := by intro a x; apply Subtype.ext; exact (F.map r).hom.map_smul _ _ }
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change F.map (𝟙 X) x.val = x.val
    simp
  map_comp r t := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change F.map (r ≫ t) x.val = F.map t (F.map r x.val)
    simp only [Functor.map_comp, ModuleCat.comp_apply]

/-- The restriction is included naturally in the old functor, not a replacement. -/
def inclusion (L : Family F) (hL : Stable F L) : restrict F L hL ⟶ F where
  app X := ModuleCat.ofHom (L X).subtype
  naturality r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

@[simp] theorem restrict_map_val (L : Family F) (hL : Stable F L)
    {X Y : C} (r : X ⟶ Y) (x : L X) :
    ((restrict F L hL).map r x).val = F.map r x.val := rfl

/-- Filtering twice adds no hidden dynamics. No finite stabilization is assumed. -/
abbrev coreFunctor (L : Family F) : C ⥤ ModuleCat.{u} K :=
  restrict F (core F L) (core_stable F L)

end CausalGeometry.LinearInvariant
