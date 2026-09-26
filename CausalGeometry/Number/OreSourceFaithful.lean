import CausalGeometry.Number.BilateralOreNormalForm
import Mathlib.Tactic

namespace CausalGeometry

universe u

namespace CausalLocalization

variable {α : Type u} [Monoid α]
variable {S : Submonoid α}

section Left

variable [OreLocalization.OreSet S]

/-- Exact source-identification criterion for the canonical left Ore
localization.

Two source elements become equal exactly when one selected denominator
equalizes them by left multiplication. -/
theorem canonicalLeftSource_eq_iff
    (a b : α) :
    canonicalLeftSourceHom
        (α := α) (S := S) a
      =
    canonicalLeftSourceHom
        (α := α) (S := S) b
      ↔
    ∃ s : S,
      (s : α) * a =
        (s : α) * b := by
  change
    OreLocalization.oreDiv a (1 : S) =
        OreLocalization.oreDiv b (1 : S)
      ↔
    _
  rw [OreLocalization.oreDiv_eq_iff]
  constructor
  · rintro ⟨u, v, hnum, hden⟩
    have huv : (u : α) = v := by
      simpa using hden
    subst v
    refine ⟨u, ?_⟩
    simpa [Submonoid.smul_def] using hnum.symm
  · rintro ⟨s, hs⟩
    refine ⟨s, (s : α), ?_, ?_⟩
    · simpa [Submonoid.smul_def] using hs.symm
    · simp

/-- Exact condition for a selected denominator to be left-cancellative. -/
def SelectedLeftCancellative : Prop :=
  ∀ s : S,
    Function.Injective
      (fun a : α => (s : α) * a)

/-- Faithfulness of the left localization source embedding is equivalent to
left cancellation by every selected denominator. -/
theorem canonicalLeftSource_injective_iff :
    Function.Injective
        (canonicalLeftSourceHom
          (α := α) (S := S))
      ↔
    SelectedLeftCancellative
      (α := α) S := by
  constructor
  · intro hinj s a b hab
    apply hinj
    apply
      (canonicalLeftSource_eq_iff
        (α := α) (S := S) a b).2
    exact ⟨s, hab⟩
  · intro hcancel a b hab
    rcases
        (canonicalLeftSource_eq_iff
          (α := α) (S := S) a b).1 hab with
      ⟨s, hs⟩
    exact hcancel s hs

end Left

section Right

variable [OreLocalization.OreSet S.op]

/-- Exact source-identification criterion for the canonical right Ore
localization. -/
theorem canonicalRightSource_eq_iff
    (a b : α) :
    canonicalRightSourceHom
        (α := α) (S := S) a
      =
    canonicalRightSourceHom
        (α := α) (S := S) b
      ↔
    ∃ s : S,
      a * (s : α) =
        b * (s : α) := by
  constructor
  · intro h
    have hop :
        canonicalLeftSourceHom
            (α := αᵐᵒᵖ)
            (S := S.op)
            (MulOpposite.op a)
          =
        canonicalLeftSourceHom
            (α := αᵐᵒᵖ)
            (S := S.op)
            (MulOpposite.op b) := by
      exact congrArg MulOpposite.unop h
    rcases
        (canonicalLeftSource_eq_iff
          (α := αᵐᵒᵖ)
          (S := S.op)
          (MulOpposite.op a)
          (MulOpposite.op b)).1 hop with
      ⟨t, ht⟩
    refine ⟨unopDenominator t, ?_⟩
    have hu := congrArg MulOpposite.unop ht
    simpa [unopDenominator] using hu
  · rintro ⟨s, hs⟩
    apply MulOpposite.unop_injective
    apply
      (canonicalLeftSource_eq_iff
        (α := αᵐᵒᵖ)
        (S := S.op)
        (MulOpposite.op a)
        (MulOpposite.op b)).2
    refine ⟨opDenominator s, ?_⟩
    have hop := congrArg MulOpposite.op hs
    simpa [opDenominator] using hop

def SelectedRightCancellative : Prop :=
  ∀ s : S,
    Function.Injective
      (fun a : α => a * (s : α))

/-- Faithfulness of the right localization source embedding is equivalent to
right cancellation by every selected denominator. -/
theorem canonicalRightSource_injective_iff :
    Function.Injective
        (canonicalRightSourceHom
          (α := α) (S := S))
      ↔
    SelectedRightCancellative
      (α := α) S := by
  constructor
  · intro hinj s a b hab
    apply hinj
    apply
      (canonicalRightSource_eq_iff
        (α := α) (S := S) a b).2
    exact ⟨s, hab⟩
  · intro hcancel a b hab
    rcases
        (canonicalRightSource_eq_iff
          (α := α) (S := S) a b).1 hab with
      ⟨s, hs⟩
    exact hcancel s hs

end Right

section Bilateral

variable [OreLocalization.OreSet S]
variable [OreLocalization.OreSet S.op]

/-- Under simultaneous left/right Ore localizations the two source embeddings
have the same faithfulness status, because the canonical bilateral equivalence
intertwines them. -/
theorem leftSource_injective_iff_rightSource_injective :
    Function.Injective
        (canonicalLeftSourceHom
          (α := α) (S := S))
      ↔
    Function.Injective
        (canonicalRightSourceHom
          (α := α) (S := S)) := by
  constructor
  · intro hL a b hab
    apply hL
    apply
      (canonicalBilateralOreEquiv
        (α := α) (S := S)).injective
    simpa using hab
  · intro hR a b hab
    apply hR
    simpa using
      congrArg
        (canonicalBilateralOreEquiv
          (α := α) (S := S))
        hab

/-- Consequently, whenever both localization orientations exist, selected left
cancellation and selected right cancellation are equivalent properties of the
denominator system.  This is not asserted before the bilateral comparison
exists. -/
theorem selectedLeftCancellative_iff_selectedRightCancellative :
    SelectedLeftCancellative
        (α := α) S
      ↔
    SelectedRightCancellative
        (α := α) S := by
  rw [
    ← canonicalLeftSource_injective_iff
      (α := α) (S := S),
    ← canonicalRightSource_injective_iff
      (α := α) (S := S)
  ]
  exact
    leftSource_injective_iff_rightSource_injective
      (α := α) (S := S)

end Bilateral
end CausalLocalization
end CausalGeometry
