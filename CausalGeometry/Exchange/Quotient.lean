import CausalGeometry.Exchange.Path

/-!
# Coherence quotients: native construction and exact descent criteria

The category and its hom quotient are mathlib's, not a second implementation.
Relations are on PARALLEL exchange routes. No object, event or history quotient
is silently introduced. Causal-history contexts are added in ContextRelation.
-/
namespace CausalGeometry.Exchange.Coherence

open CategoryTheory

universe uC vC uD vD uE vE
variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {E : Type uE} [Category.{vE} E]

/-- Exact, strict preservation of the specified generating equations. -/
def Respects (r : HomRel C) (F : C ⥤ D) : Prop :=
  ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), r f g → F.map f = F.map g

/-- The actual least congruence, observed through the native quotient functor. -/
def Generated (r : HomRel C) : HomRel C :=
  (CategoryTheory.Quotient.functor r).homRel

instance generatedCongruence (r : HomRel C) : CategoryTheory.Congruence (Generated r) :=
  inferInstanceAs (CategoryTheory.Congruence (CategoryTheory.Quotient.functor r).homRel)

/-- Equality in the quotient is exactly equivalence closure after composition
closure. In particular, adding one equation does not collapse the whole hom-set. -/
theorem generated_iff (r : HomRel C) {X Y : C} (f g : X ⟶ Y) :
    Generated r f g ↔ Relation.EqvGen (@HomRel.CompClosure C _ r X Y) f g :=
  CategoryTheory.Quotient.functor_homRel_eq_compClosure_eqvGen r f g

theorem of_generator (r : HomRel C) {X Y : C} {f g : X ⟶ Y}
    (h : r f g) : Generated r f g :=
  CategoryTheory.Quotient.sound r h

/-- Concrete descent, constructed by Quotient.lift. -/
def descend (r : HomRel C) (F : C ⥤ D) (h : Respects r F) :
    CategoryTheory.Quotient r ⥤ D :=
  CategoryTheory.Quotient.lift r F (fun _ _ f g w => h f g w)

@[simp] theorem descend_spec (r : HomRel C) (F : C ⥤ D) (h : Respects r F) :
    CategoryTheory.Quotient.functor r ⋙ descend r F h = F :=
  CategoryTheory.Quotient.lift_spec r F _

@[simp] theorem descend_map (r : HomRel C) (F : C ⥤ D) (h : Respects r F)
    {X Y : C} (f : X ⟶ Y) :
    (descend r F h).map ((CategoryTheory.Quotient.functor r).map f) = F.map f :=
  rfl

theorem descend_unique (r : HomRel C) (F : C ⥤ D) (h : Respects r F)
    (G : CategoryTheory.Quotient r ⥤ D)
    (hG : CategoryTheory.Quotient.functor r ⋙ G = F) : G = descend r F h :=
  CategoryTheory.Quotient.lift_unique r F _ G hG

/-- Necessity and sufficiency, not merely a record containing a possible lift. -/
theorem respects_iff_factors (r : HomRel C) (F : C ⥤ D) :
    Respects r F ↔ ∃ G : CategoryTheory.Quotient r ⥤ D,
      CategoryTheory.Quotient.functor r ⋙ G = F := by
  constructor
  · intro h
    exact ⟨descend r F h, descend_spec r F h⟩
  · rintro ⟨G, hG⟩
    rw [← hG]
    intro X Y f g hfg
    change G.map ((CategoryTheory.Quotient.functor r).map f) =
      G.map ((CategoryTheory.Quotient.functor r).map g)
    exact congrArg (fun a => G.map a) (CategoryTheory.Quotient.sound r hfg)

/-- Allowing a natural isomorphism instead of strict equality does not let an
interpretation distinguish an equation that the quotient has already imposed. -/
theorem respects_iff_factorsUpToIso (r : HomRel C) (F : C ⥤ D) :
    Respects r F ↔ ∃ G : CategoryTheory.Quotient r ⥤ D,
      Nonempty (CategoryTheory.Quotient.functor r ⋙ G ≅ F) := by
  constructor
  · intro h
    exact ⟨descend r F h, ⟨eqToIso (descend_spec r F h)⟩⟩
  · rintro ⟨G, ⟨e⟩⟩
    intro X Y f g hfg
    have he : (CategoryTheory.Quotient.functor r ⋙ G).map f =
        (CategoryTheory.Quotient.functor r ⋙ G).map g :=
      congrArg (fun a => G.map a) (CategoryTheory.Quotient.sound r hfg)
    have hn : e.hom.app X ≫ F.map f = e.hom.app X ≫ F.map g := by
      calc
        e.hom.app X ≫ F.map f =
            (CategoryTheory.Quotient.functor r ⋙ G).map f ≫ e.hom.app Y :=
          (e.hom.naturality f).symm
        _ = (CategoryTheory.Quotient.functor r ⋙ G).map g ≫ e.hom.app Y := by rw [he]
        _ = e.hom.app X ≫ F.map g := e.hom.naturality g
    exact (cancel_epi (e.hom.app X)).mp hn

/-- A respecting interpretation respects every generated equation. -/
theorem respects_generated (r : HomRel C) (F : C ⥤ D) (h : Respects r F) :
    Respects (Generated r) F := by
  intro X Y f g hfg
  have hh := congrArg (fun a => (descend r F h).map a) hfg
  exact hh

theorem respects_generated_iff (r : HomRel C) (F : C ⥤ D) :
    Respects (Generated r) F ↔ Respects r F := by
  constructor
  · intro h X Y f g w
    exact h f g (of_generator r w)
  · exact respects_generated r F

/-- Initiality among congruences follows from the native exact quotient law. -/
theorem generated_le (r s : HomRel C) [CategoryTheory.Congruence s]
    (h : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), r f g → s f g)
    {X Y : C} {f g : X ⟶ Y} (w : Generated r f g) : s f g := by
  have hs : Respects r (CategoryTheory.Quotient.functor s) := by
    intro A B a b hab
    exact CategoryTheory.Quotient.sound s (h a b hab)
  exact (CategoryTheory.Quotient.functor_map_eq_iff s f g).mp
    (respects_generated r _ hs f g w)

/-- A functor carries a generated congruence into a second one when it carries
its generators into that congruence. Useful for genuine causal contexts. -/
def mapQuotient (r : HomRel C) (s : HomRel D) (F : C ⥤ D)
    (h : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), r f g → Generated s (F.map f) (F.map g)) :
    CategoryTheory.Quotient r ⥤ CategoryTheory.Quotient s :=
  descend r (F ⋙ CategoryTheory.Quotient.functor s) (fun f g w => h f g w)

@[simp] theorem mapQuotient_spec (r : HomRel C) (s : HomRel D) (F : C ⥤ D)
    (h : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), r f g → Generated s (F.map f) (F.map g)) :
    CategoryTheory.Quotient.functor r ⋙ mapQuotient r s F h =
      F ⋙ CategoryTheory.Quotient.functor s :=
  descend_spec r _ _

theorem map_generated (r : HomRel C) (s : HomRel D) (F : C ⥤ D)
    (h : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), r f g → Generated s (F.map f) (F.map g))
    {X Y : C} {f g : X ⟶ Y} (w : Generated r f g) :
    Generated s (F.map f) (F.map g) :=
  respects_generated r (F ⋙ CategoryTheory.Quotient.functor s)
    (fun f g w => h f g w) f g w

/-- More generating equations give a canonical information-forgetting functor. -/
def compare (r s : HomRel C)
    (h : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), r f g → s f g) :
    CategoryTheory.Quotient r ⥤ CategoryTheory.Quotient s :=
  descend r (CategoryTheory.Quotient.functor s)
    (fun f g w => CategoryTheory.Quotient.sound s (h f g w))

@[simp] theorem compare_spec (r s : HomRel C)
    (h : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), r f g → s f g) :
    CategoryTheory.Quotient.functor r ⋙ compare r s h =
      CategoryTheory.Quotient.functor s :=
  descend_spec r _ _

theorem compare_id (r : HomRel C) :
    compare r r (fun _ _ h => h) = 𝟭 (CategoryTheory.Quotient r) := by
  apply CategoryTheory.Quotient.lift_unique' r
  simp only [compare_spec, Functor.comp_id]

theorem compare_comp (r s t : HomRel C)
    (h : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), r f g → s f g)
    (k : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), s f g → t f g) :
    compare r s h ⋙ compare s t k = compare r t (fun f g w => k f g (h f g w)) := by
  apply CategoryTheory.Quotient.lift_unique' r
  rw [← Functor.assoc, compare_spec, compare_spec, compare_spec]

/-- A certified separating observation forbids equality in the generated quotient. -/
theorem separated_not_generated (r : HomRel C) (F : C ⥤ D) (h : Respects r F)
    {X Y : C} {f g : X ⟶ Y} (hne : F.map f ≠ F.map g) : ¬ Generated r f g := by
  intro w
  exact hne (respects_generated r F h f g w)

end CausalGeometry.Exchange.Coherence
