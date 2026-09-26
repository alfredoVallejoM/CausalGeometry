import CausalGeometry.Number.CanonicalAtomicDomain
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic

namespace CausalGeometry
namespace Models
namespace CausalLengthAtomic

open CausalDivisibility
open CausalPrime
open CausalFactorization

/-- Free commutative causal composition monoid on one primitive direction.

Multiplication is addition of causal lengths; it is not ordinary arithmetic
multiplication on natural numbers. -/
abbrev CausalLength :=
  Multiplicative ℕ

/-- The unique structural atom: one primitive causal step. -/
def atom : CausalLength :=
  Multiplicative.ofAdd 1

@[simp] theorem atom_toAdd :
    atom.toAdd = 1 :=
  rfl

/-- One is exactly zero causal length. -/
theorem eq_one_iff_toAdd_zero
    (x : CausalLength) :
    x = 1 ↔ x.toAdd = 0 := by
  rw [Multiplicative.ext_iff]
  simp

/-- Causal units are exactly zero-length elements. -/
theorem isCausalUnit_iff_toAdd_zero
    (x : CausalLength) :
    IsCausalUnit x ↔
      x.toAdd = 0 := by

  constructor

  · rintro ⟨y, hxy, _⟩

    have h :=
      congrArg Multiplicative.toAdd hxy

    simp only [
      Multiplicative.toAdd_mul
    ] at h

    simpa using
      Nat.eq_zero_of_add_eq_zero_left h

  · intro hx

    have hx1 :
        x = 1 :=
      (eq_one_iff_toAdd_zero x).2 hx

    subst x

    exact one_isCausalUnit

/-- Product of n primitive causal steps has causal length n. -/
@[simp] theorem prod_replicate_atom
    (n : ℕ) :
    (List.replicate n atom).prod =
      Multiplicative.ofAdd n := by

  induction n with

  | zero =>
      rfl

  | succ n ih =>
      simp only [
        List.replicate_succ,
        List.prod_cons,
        ih
      ]

      rw [Multiplicative.ext_iff]

      simp [atom, Nat.succ_eq_add_one,
        Nat.add_comm]

/-- The one-step element is compositionally irreducible. -/
theorem atom_irreducible :
    Irreducible atom := by

  constructor

  · rw [isCausalUnit_iff_toAdd_zero]
    norm_num

  · intro a b hab

    have h :=
      congrArg Multiplicative.toAdd hab

    simp only [
      Multiplicative.toAdd_mul,
      atom_toAdd
    ] at h

    have hor :
        a.toAdd = 0 ∨
          b.toAdd = 0 := by
      omega

    rcases hor with ha | hb

    · exact Or.inl
        ((isCausalUnit_iff_toAdd_zero a).2 ha)

    · exact Or.inr
        ((isCausalUnit_iff_toAdd_zero b).2 hb)

/-- Every irreducible element is the unique one-step atom. -/
theorem irreducible_eq_atom
    {x : CausalLength}
    (hx : Irreducible x) :
    x = atom := by

  have hxpos :
      0 < x.toAdd := by

    have hne :
        x.toAdd ≠ 0 := by
      intro hz
      exact hx.1
        ((isCausalUnit_iff_toAdd_zero x).2 hz)

    omega

  by_contra hxa

  have hneOne :
      x.toAdd ≠ 1 := by
    intro h1
    apply hxa
    rw [Multiplicative.ext_iff]
    simpa [atom] using h1

  have htwo :
      2 ≤ x.toAdd := by
    omega

  let y : CausalLength :=
    Multiplicative.ofAdd (x.toAdd - 1)

  have hypos :
      0 < y.toAdd := by
    dsimp [y]
    omega

  have hfactor :
      atom * y = x := by
    rw [Multiplicative.ext_iff]
    simp [atom, y]
    omega

  rcases hx.2 atom y hfactor with
    hunit | hunit

  · have hz :=
      (isCausalUnit_iff_toAdd_zero atom).1
        hunit
    norm_num at hz

  · have hz :=
      (isCausalUnit_iff_toAdd_zero y).1
        hunit
    exact (Nat.ne_of_gt hypos) hz

/-- Strong classification: irreducible iff equal to the unique causal atom. -/
theorem irreducible_iff_eq_atom
    (x : CausalLength) :
    Irreducible x ↔ x = atom := by
  constructor
  · exact irreducible_eq_atom
  · intro h
    subst x
    exact atom_irreducible

/-- Canonical atomic word for one causal length. -/
def factors
    (x : CausalLength) :
    List CausalLength :=
  List.replicate x.toAdd atom

/-- The canonical factor word evaluates exactly to the source element. -/
theorem factors_eval
    (x : CausalLength) :
    eval (factors x) = x := by

  unfold factors eval

  rw [prod_replicate_atom]

  rw [Multiplicative.ext_iff]

  rfl

/-- Every entry of the canonical factor word is irreducible. -/
theorem factors_atomic
    (x : CausalLength) :
    ∀ p ∈ factors x,
      Irreducible p := by

  intro p hp

  have hpAtom :
      p = atom := by
    simpa [factors] using
      (List.eq_of_mem_replicate hp)

  subst p

  exact atom_irreducible

/-- Canonical word is an atomic factorization. -/
theorem factors_spec
    (x : CausalLength) :
    IsAtomicFactorization
      (factors x) x :=
  ⟨factors_eval x,
    factors_atomic x⟩

/-- Any list consisting only of irreducibles is literally a repetition of the
unique atom. -/
theorem list_eq_replicate_atom_of_irreducible
    (xs : List CausalLength)
    (hxs :
      ∀ p ∈ xs,
        Irreducible p) :
    xs =
      List.replicate xs.length atom := by

  induction xs with

  | nil =>
      rfl

  | cons x xs ih =>

      have hx :
          x = atom :=
        irreducible_eq_atom
          (hxs x (by simp))

      have htail :
          ∀ p ∈ xs,
            Irreducible p := by
        intro p hp
        exact hxs p (by simp [hp])

      rw [hx, ih htail]

      simp

/-- Strong uniqueness theorem: every atomic factorization word of x is exactly
the canonical word, not merely profile-equivalent. -/
theorem atomicFactorization_word_unique
    {x : CausalLength}
    {xs : List CausalLength}
    (hxs :
      IsAtomicFactorization xs x) :
    xs = factors x := by

  have hrep :=
    list_eq_replicate_atom_of_irreducible
      xs hxs.2

  have heval :
      (List.replicate xs.length atom).prod =
        x := by
    simpa [eval, hrep] using hxs.1

  rw [prod_replicate_atom] at heval

  have hlen :
      xs.length = x.toAdd := by
    exact congrArg
      Multiplicative.toAdd heval

  simpa [factors, hlen] using hrep

/-- In particular, every atomic factorization has the same multiplicity
profile. -/
theorem profile_unique
    {x : CausalLength}
    {xs : List CausalLength}
    (hxs :
      IsAtomicFactorization xs x) :
    profile xs =
      profile (factors x) := by
  rw [atomicFactorization_word_unique hxs]

/-- Certified canonical atomic domain on a genuinely nonclassical causal
composition monoid. -/
def domain :
    CanonicalAtomicDomain
      (α := CausalLength) where

  factors :=
    factors

  factors_spec :=
    factors_spec

  profile_unique :=
    profile_unique

/-- Nontrivial regression: causal length three has a genuine three-atom
factorization. -/
theorem length_three_factorization :
    factors (Multiplicative.ofAdd 3 :
      CausalLength)
      =
    [atom, atom, atom] := by
  rfl

theorem length_three_atomic :
    IsAtomicFactorization
      [atom, atom, atom]
      (Multiplicative.ofAdd 3 :
        CausalLength) := by
  simpa [length_three_factorization] using
    factors_spec
      (Multiplicative.ofAdd 3 :
        CausalLength)

end CausalLengthAtomic
end Models
end CausalGeometry
