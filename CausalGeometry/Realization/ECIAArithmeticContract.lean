import CausalGeometry.Process.EndComposition
import CausalGeometry.Realization.ECIAProcessContract

namespace CausalGeometry

universe u v

/-- Multiplicative natural shadow for a weak enddiary composition system.

The source process composition need not be strict. Invariance under the chosen
source equivalence is therefore part of the shadow contract. -/
structure EndDiaryNatShadow
    {A : Type u}
    (C : EndDiaryCompositionSystem A) where
  toNat : EndDiary A → ℕ
  equivalent_invariant :
    ∀ {X Y}, C.equivalent X Y → toNat X = toNat Y
  unit :
    toNat C.unit = 1
  compose :
    ∀ X Y,
      toNat (C.compose X Y) =
        toNat X * toNat Y

namespace EndDiaryNatShadow

variable {A : Type u}
variable {C : EndDiaryCompositionSystem A}

instance : CoeFun (EndDiaryNatShadow C)
    (fun _ => EndDiary A → ℕ) :=
  ⟨EndDiaryNatShadow.toNat⟩

@[simp] theorem unit_apply
    (S : EndDiaryNatShadow C) :
    S C.unit = 1 :=
  S.unit

@[simp] theorem compose_apply
    (S : EndDiaryNatShadow C)
    (X Y : EndDiary A) :
    S (C.compose X Y) = S X * S Y :=
  S.compose X Y

end EndDiaryNatShadow

namespace ECIARealization

variable {A : Type u}
variable {sourceAdmissible : CausalNumber A → Prop}
variable {T : ECIAStructuralTarget.{u, v} A}

/-- Preservation of one weak causal arithmetic shadow. -/
def PreservesNatShadow
    (R : ECIARealization A sourceAdmissible T)
    {C : EndDiaryCompositionSystem A}
    (S : EndDiaryNatShadow C)
    (targetShadow : T.Target → ℕ) : Prop :=
  ∀ X, targetShadow (R.realize X) = S X

/-- Preservation of every product selected by one weak source composition
system. -/
def PreservesCompositionSystem
    (R : ECIARealization A sourceAdmissible T)
    (C : EndDiaryCompositionSystem A)
    (targetCompose : T.Target → T.Target → T.Target) : Prop :=
  ∀ X Y,
    R.PreservesComposite targetCompose (C.composeData X Y)

/-- If ECIA preserves both the chosen weak composition and the source natural
shadow, the target shadow is multiplicative on realized causal numbers. -/
theorem targetShadow_comp
    (R : ECIARealization A sourceAdmissible T)
    (C : EndDiaryCompositionSystem A)
    (S : EndDiaryNatShadow C)
    (targetCompose : T.Target → T.Target → T.Target)
    (targetShadow : T.Target → ℕ)
    (hcomp : R.PreservesCompositionSystem C targetCompose)
    (hshadow : R.PreservesNatShadow S targetShadow)
    (X Y : CausalNumber A) :
    targetShadow
        (targetCompose (R.realize X) (R.realize Y)) =
      targetShadow (R.realize X) *
        targetShadow (R.realize Y) := by
  calc
    targetShadow
        (targetCompose (R.realize X) (R.realize Y))
        =
      targetShadow (R.realize (C.compose X Y)) := by
        exact congrArg targetShadow (hcomp X Y).symm
    _ = S (C.compose X Y) := hshadow _
    _ = S X * S Y := S.compose X Y
    _ =
      targetShadow (R.realize X) *
        targetShadow (R.realize Y) := by
          rw [← hshadow X, ← hshadow Y]

/-- If the selected ECIA target unit is the realization of the source unit,
shadow preservation also recovers the target unit value one. -/
theorem targetShadow_unit
    (R : ECIARealization A sourceAdmissible T)
    (C : EndDiaryCompositionSystem A)
    (S : EndDiaryNatShadow C)
    (targetUnit : T.Target)
    (targetShadow : T.Target → ℕ)
    (hunit : R.realize C.unit = targetUnit)
    (hshadow : R.PreservesNatShadow S targetShadow) :
    targetShadow targetUnit = 1 := by
  rw [← hunit, hshadow]
  exact S.unit

end ECIARealization
end CausalGeometry
