import CausalGeometry.Process.Composition

namespace CausalGeometry

universe u w

/-- A chosen weak composition system for enddiaries over one boundary.

The gluing witness remains part of the data for every product. Associativity and
unit laws hold only up to an explicit source equivalence relation; strict
equality is not imposed on causal processes. -/
structure EndDiaryCompositionSystem
    (A : Type u) where
  composeData :
    (X Y : EndDiary.{u, w} A) →
      DiaryCompositionData.{u, u, u, w} X Y

  equivalent :
    EndDiary.{u, w} A → EndDiary.{u, w} A → Prop
  equivalent_refl :
    ∀ X, equivalent X X
  equivalent_symm :
    ∀ {X Y}, equivalent X Y → equivalent Y X
  equivalent_trans :
    ∀ {X Y Z}, equivalent X Y → equivalent Y Z → equivalent X Z

  unit : EndDiary.{u, w} A

  associator :
    ∀ X Y Z,
      equivalent
        ((composeData (composeData X Y).result Z).result)
        ((composeData X (composeData Y Z).result).result)

  left_unitor :
    ∀ X, equivalent (composeData unit X).result X

  right_unitor :
    ∀ X, equivalent (composeData X unit).result X

namespace EndDiaryCompositionSystem

variable {A : Type u}

def compose
    (C : EndDiaryCompositionSystem.{u, w} A)
    (X Y : EndDiary.{u, w} A) :
    EndDiary.{u, w} A :=
  (C.composeData X Y).result


theorem assoc
    (C : EndDiaryCompositionSystem.{u, w} A)
    (X Y Z : EndDiary.{u, w} A) :
    C.equivalent (C.compose (C.compose X Y) Z)
      (C.compose X (C.compose Y Z)) :=
  C.associator X Y Z

theorem one_comp
    (C : EndDiaryCompositionSystem.{u, w} A)
    (X : EndDiary.{u, w} A) :
    C.equivalent (C.compose C.unit X) X :=
  C.left_unitor X

theorem comp_one
    (C : EndDiaryCompositionSystem.{u, w} A)
    (X : EndDiary.{u, w} A) :
    C.equivalent (C.compose X C.unit) X :=
  C.right_unitor X

end EndDiaryCompositionSystem
end CausalGeometry
