import CausalGeometry.Number.Factorization
import Mathlib.Data.Finsupp.Basic

namespace CausalGeometry

universe u

namespace CausalFactorization

variable {α : Type u} [Monoid α] [DecidableEq α]

/-- Multiplicity profile of an ordered causal factorization.  It forgets order
but not multiplicity, so it is an explicit decategorification step. -/
def profile : List α → α →₀ ℕ
  | [] => 0
  | x :: xs => Finsupp.single x 1 + profile xs

@[simp] theorem profile_nil :
    profile ([] : List α) = 0 := rfl

@[simp] theorem profile_cons (x : α) (xs : List α) :
    profile (x :: xs) = Finsupp.single x 1 + profile xs := rfl

theorem profile_append (xs ys : List α) :
    profile (xs ++ ys) = profile xs + profile ys := by
  induction xs with
  | nil =>
      simp [profile]
  | cons x xs ih =>
      simp [profile, ih, add_assoc]

/-- Multiplicity of one causal factor inside an ordered factorization. -/
def multiplicity (p : α) (xs : List α) : ℕ :=
  profile xs p

@[simp] theorem multiplicity_cons_self (p : α) (xs : List α) :
    multiplicity p (p :: xs) = multiplicity p xs + 1 := by
  simp [multiplicity, profile, Nat.add_comm]

theorem multiplicity_append (p : α) (xs ys : List α) :
    multiplicity p (xs ++ ys) =
      multiplicity p xs + multiplicity p ys := by
  simp [multiplicity, profile_append]

theorem profile_apply_eq_count (xs : List α) (p : α) :
    profile xs p = xs.count p := by
  induction xs with
  | nil =>
      simp [profile]
  | cons x xs ih =>
      by_cases hxp : x = p
      · subst x
        simp [profile, ih]
      · simp [profile, ih, hxp]

theorem multiplicity_eq_count (p : α) (xs : List α) :
    multiplicity p xs = xs.count p := by
  exact profile_apply_eq_count xs p

end CausalFactorization
end CausalGeometry
