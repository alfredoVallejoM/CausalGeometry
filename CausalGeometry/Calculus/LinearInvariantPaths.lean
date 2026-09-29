import CausalGeometry.Calculus.PersistentLinearCompatibility
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Generator criteria and certified finite-horizon stopping

The category is the native free path category. Stability is checked on its
actual quiver generators, not inferred from a sample of terminal outcomes.
No universal finite convergence or word-problem algorithm is asserted.
-/
namespace CausalGeometry.LinearInvariant.Paths

open CategoryTheory
universe u v w
variable {K : Type u} [CommRing K] {V : Type v} [Quiver.{w} V]
variable (F : CategoryTheory.Paths V ⥤ ModuleCat.{u} K)

/-- Generator stability suffices on a freely generated path category. -/
theorem stable_of_steps (L : LinearInvariant.Family F)
    (h : ∀ (X Y : V) (s : X ⟶ Y) (x : F.obj X),
      x ∈ L X → F.map s.toPath x ∈ L Y) : LinearInvariant.Stable F L := by
  intro X Y r x hx
  induction r with
  | nil => simpa using hx
  | @cons Y Z r s ih =>
      change F.map (r ≫ s.toPath) x ∈ L Z
      simpa only [Functor.map_comp, ModuleCat.comp_apply] using h Y Z s _ ih

variable (G : CategoryTheory.Paths V ⥤ ModuleCat.{u} K)
variable (tau : ∀ X, F.obj X →ₗ[K] G.obj X)

/-- The intersection of all outgoing one-generator defect kernels. -/
def generatorDomain (X : CategoryTheory.Paths V) : Submodule K (F.obj X) where
  carrier := {x | ∀ (Y : V) (s : (X : V) ⟶ Y),
    PersistentLinear.defect F G tau s.toPath x = 0}
  zero_mem' := by intro Y s; exact map_zero _
  add_mem' := by
    intro x y hx hy Y s
    rw [map_add, hx Y s, hy Y s, add_zero]
  smul_mem' := by
    intro a x hx Y s
    rw [map_smul, hx Y s, smul_zero]

/-- The all-continuation domain is exactly the invariant interior of the
one-step compatibility family. This proves the source-level construction. -/
theorem persistent_eq_core_generators (X : CategoryTheory.Paths V) :
    PersistentLinear.domain F G tau X =
      LinearInvariant.core F (generatorDomain F G tau) X := by
  apply le_antisymm
  · apply LinearInvariant.le_core F _ _ (PersistentLinear.domain_stable F G tau)
    intro Y x hx Z s
    exact hx Z s.toPath
  · intro x hx
    apply (PersistentLinear.mem_domain F G tau X x).mpr
    intro Y r
    induction r with
    | nil => simp
    | @cons Y Z r s ih =>
        have hs := sub_eq_zero.mp (hx Y r Z s)
        change G.map (r ≫ s.toPath) (tau X x) = tau Z (F.map (r ≫ s.toPath) x)
        simp only [Functor.map_comp, ModuleCat.comp_apply]
        rw [ih]
        exact hs

/-- Maximality can be established using only generators plus stability. -/
theorem le_persistent_of_steps (L : LinearInvariant.Family F)
    (hstable : ∀ (X Y : V) (s : X ⟶ Y) (x : F.obj X),
      x ∈ L X → F.map s.toPath x ∈ L Y)
    (hlocal : ∀ X, L X ≤ generatorDomain F G tau X) (X : CategoryTheory.Paths V) :
    L X ≤ PersistentLinear.domain F G tau X := by
  rw [persistent_eq_core_generators]
  exact LinearInvariant.le_core F _ L (stable_of_steps F L hstable) hlocal X

/-- One simultaneous backward-preimage refinement, using ALL admitted edges. -/
def prune (L M : LinearInvariant.Family F) (X : CategoryTheory.Paths V) :
    Submodule K (F.obj X) where
  carrier := {x | x ∈ L X ∧ ∀ (Y : V) (s : (X : V) ⟶ Y), F.map s.toPath x ∈ M Y}
  zero_mem' := by
    refine ⟨(L X).zero_mem, ?_⟩
    intro Y s
    simpa using (M Y).zero_mem
  add_mem' := by
    intro x y hx hy
    refine ⟨(L X).add_mem hx.1 hy.1, ?_⟩
    intro Y s
    simpa only [map_add] using (M Y).add_mem (hx.2 Y s) (hy.2 Y s)
  smul_mem' := by
    intro a x hx
    refine ⟨(L X).smul_mem a hx.1, ?_⟩
    intro Y s
    simpa only [map_smul] using (M Y).smul_mem a (hx.2 Y s)

theorem prune_le (L M : LinearInvariant.Family F) (X : CategoryTheory.Paths V) :
    prune F L M X ≤ L X := fun _ hx => hx.1

theorem prune_mono (L M N : LinearInvariant.Family F) (h : ∀ X, M X ≤ N X)
    (X : CategoryTheory.Paths V) : prune F L M X ≤ prune F L N X := by
  intro x hx
  exact ⟨hx.1, fun Y s => h Y (hx.2 Y s)⟩

/-- Finite horizons begin with the local constraint, not with an assumed fixed point. -/
def horizon (L : LinearInvariant.Family F) : Nat → LinearInvariant.Family F
  | 0 => L
  | n + 1 => prune F L (horizon F L n)

theorem horizon_le (L : LinearInvariant.Family F) (n : Nat) (X : CategoryTheory.Paths V) :
    horizon F L n X ≤ L X := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact prune_le F L _ X

theorem horizon_descending (L : LinearInvariant.Family F) (n : Nat)
    (X : CategoryTheory.Paths V) : horizon F L (n+1) X ≤ horizon F L n X := by
  induction n generalizing X with
  | zero => exact prune_le F L L X
  | succ n ih =>
      exact prune_mono F L _ _ ih X

/-- No finite truncation removes a truly persistent state. -/
theorem core_le_horizon (L : LinearInvariant.Family F) (n : Nat)
    (X : CategoryTheory.Paths V) : LinearInvariant.core F L X ≤ horizon F L n X := by
  induction n generalizing X with
  | zero => exact LinearInvariant.core_le F L X
  | succ n ih =>
      intro x hx
      exact ⟨LinearInvariant.core_le F L X hx,
        fun Y s => ih Y (LinearInvariant.core_stable F L s.toPath hx)⟩

/-- A globally stationary refinement is a certificate of exactness. Checking
one vertex, one sample, or hitting a budget is NOT this hypothesis. -/
theorem horizon_fixed_eq_core (L : LinearInvariant.Family F) (n : Nat)
    (hfix : ∀ X, horizon F L (n+1) X = horizon F L n X)
    (X : CategoryTheory.Paths V) :
    horizon F L n X = LinearInvariant.core F L X := by
  apply le_antisymm
  · apply LinearInvariant.le_core F L (horizon F L n)
    · apply stable_of_steps F
      intro Y Z s x hx
      have hx' : x ∈ horizon F L (n+1) Y := by rw [hfix Y]; exact hx
      exact hx'.2 Z s
    · exact fun Y => horizon_le F L n Y
  · exact core_le_horizon F L n X

end CausalGeometry.LinearInvariant.Paths
