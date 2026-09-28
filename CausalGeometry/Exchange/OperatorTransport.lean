import CausalGeometry.Exchange.LocalOperator

/-!
# Changes of coefficients for local exchange operators

A map may intertwine two operators without being invertible, injective or
surjective. Those hypotheses are separate and used only for the corresponding
reflection/transfer results. No global braid law is imposed on causal events.
-/
namespace CausalGeometry.Exchange.OperatorTransport

open LocalOperator
universe u v w
variable {A : Type u} {B : Type v} {C : Type w}

/-- Componentwise transport on a pair. -/
def pairMap (f : A → B) (x : A × A) : B × B := (f x.1, f x.2)

/-- Transport after the source exchange equals exchange after transport. -/
def Intertwines (f : A → B) (R : PairOperator A) (T : PairOperator B) : Prop :=
  ∀ x, pairMap f (R x) = T (pairMap f x)

theorem intertwines_id (R : PairOperator A) : Intertwines id R R := by
  intro x
  rfl

theorem intertwines_comp (f : A → B) (g : B → C)
    (R : PairOperator A) (T : PairOperator B) (U : PairOperator C)
    (hf : Intertwines f R T) (hg : Intertwines g T U) :
    Intertwines (g ∘ f) R U := by
  intro x
  change pairMap g (pairMap f (R x)) = U (pairMap g (pairMap f x))
  rw [hf, hg]

/-- Map coefficients without changing the certified number of slots. -/
def mapSized (f : A → B) {n : Nat} (xs : Sized A n) : Sized B n :=
  ⟨xs.val.map f, by simpa using xs.property⟩

@[simp] theorem mapSized_val (f : A → B) {n : Nat} (xs : Sized A n) :
    (mapSized f xs).val = xs.val.map f := rfl

@[simp] theorem mapSized_id {n : Nat} (xs : Sized A n) : mapSized id xs = xs := by
  apply Subtype.ext
  simp [mapSized]

@[simp] theorem mapSized_comp (f : A → B) (g : B → C) {n : Nat} (xs : Sized A n) :
    mapSized g (mapSized f xs) = mapSized (g ∘ f) xs := by
  apply Subtype.ext
  simp [mapSized, List.map_map, Function.comp_def]

/-- The one-pair comparison suffices at every position, including the total
helper's out-of-range identity cases; no YB or bijectivity is needed. -/
theorem map_stepList (f : A → B) (R : PairOperator A) (T : PairOperator B)
    (hf : Intertwines f R T) (i : Nat) (xs : List A) :
    (stepList R i xs).map f = stepList T i (xs.map f) := by
  induction i generalizing xs with
  | zero =>
      cases xs with
      | nil => rfl
      | cons a xs => cases xs with
        | nil => rfl
        | cons b xs =>
            have h := hf (a, b)
            have h₁ := congrArg Prod.fst h
            have h₂ := congrArg Prod.snd h
            change f (R (a, b)).1 :: f (R (a, b)).2 :: xs.map f =
              (T (f a, f b)).1 :: (T (f a, f b)).2 :: xs.map f
            rw [h₁, h₂]
  | succ i ih => cases xs <;> simp [stepList, ih]

theorem map_act (f : A → B) (R : PairOperator A) (T : PairOperator B)
    (hf : Intertwines f R T) {n : Nat} (i : Fin n) (xs : Sized A (n + 1)) :
    mapSized f (act R i xs) = act T i (mapSized f xs) :=
  Subtype.ext (map_stepList f R T hf i.val xs.val)

/-- Used for reflecting a ternary equation, not for claiming route fidelity. -/
def tripleMap (f : A → B) (x : A × A × A) : B × B × B :=
  (f x.1, f x.2.1, f x.2.2)

theorem triple_left (f : A → B) (R : PairOperator A) (T : PairOperator B)
    (hf : Intertwines f R T) (x : A × A × A) :
    tripleMap f (leftTriple R x) = leftTriple T (tripleMap f x) := by
  have h := hf (x.1, x.2.1)
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  apply Prod.ext
  · exact h₁
  · exact Prod.ext h₂ rfl

theorem triple_right (f : A → B) (R : PairOperator A) (T : PairOperator B)
    (hf : Intertwines f R T) (x : A × A × A) :
    tripleMap f (rightTriple R x) = rightTriple T (tripleMap f x) := by
  have h := hf (x.2.1, x.2.2)
  exact Prod.ext rfl h

theorem tripleMap_injective (f : A → B) (hf : Function.Injective f) :
    Function.Injective (tripleMap f) := by
  intro x y h
  apply Prod.ext
  · exact hf (congrArg Prod.fst h)
  · apply Prod.ext
    · exact hf (congrArg (fun t => t.2.1) h)
    · exact hf (congrArg (fun t => t.2.2) h)

/-- A faithful change of COEFFICIENTS reflects YB; this says nothing about
faithfulness of the representation of exchange routes. -/
theorem yb_reflects_of_injective (f : A → B) (R : PairOperator A) (T : PairOperator B)
    (hf : Intertwines f R T) (hinj : Function.Injective f)
    (hT : YangBaxter T) : YangBaxter R := by
  intro x
  apply tripleMap_injective f hinj
  simp only [triple_left f R T hf, triple_right f R T hf]
  exact hT (tripleMap f x)

/-- A surjective intertwiner carries YB to its entire target, rather than
only to the image of its source. -/
theorem yb_descends_of_surjective (f : A → B) (R : PairOperator A) (T : PairOperator B)
    (hf : Intertwines f R T) (hsurj : Function.Surjective f)
    (hR : YangBaxter R) : YangBaxter T := by
  rintro ⟨a, b, c⟩
  obtain ⟨x, rfl⟩ := hsurj a
  obtain ⟨y, rfl⟩ := hsurj b
  obtain ⟨z, rfl⟩ := hsurj c
  have h := congrArg (tripleMap f) (hR (x, y, z))
  simpa only [triple_left f R T hf, triple_right f R T hf] using h

/-- An equivalence reverses the intertwining square; a general Psi cannot. -/
theorem intertwines_symm (e : A ≃ B) (R : PairOperator A) (T : PairOperator B)
    (h : Intertwines e R T) : Intertwines e.symm T R := by
  intro x
  have he := congrArg (pairMap e.symm) (h (pairMap e.symm x))
  simpa [pairMap] using he.symm

end CausalGeometry.Exchange.OperatorTransport
