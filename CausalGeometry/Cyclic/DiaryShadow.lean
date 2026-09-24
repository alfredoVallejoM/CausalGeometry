import CausalGeometry.Process.Composition
import CausalGeometry.Process.EndComposition

namespace CausalGeometry

universe u v w

/-- A cyclic shadow target for endodiaries over one boundary.

The shadow carries its own equivalence relation. Cyclicity is not built into the
carrier: it is a theorem obligation for chosen composites. -/
structure DiaryCyclicShadow
    (A : Type u) where
  Cycle : Type v
  equivalent : Cycle → Cycle → Prop
  equivalent_refl : ∀ c, equivalent c c
  equivalent_symm : ∀ {c d}, equivalent c d → equivalent d c
  equivalent_trans :
    ∀ {c d e}, equivalent c d → equivalent d e → equivalent c e
  close : EndDiary A → Cycle

namespace DiaryCyclicShadow

variable {A : Type u}

/-- Cyclicity for one chosen pair of opposite-order gluing witnesses. -/
def CyclicFor
    (S : DiaryCyclicShadow.{u, v} A)
    {X Y : EndDiary A}
    (GXY : DiaryCompositionData.{u, u, u, w} X Y)
    (GYX : DiaryCompositionData.{u, u, u, w} Y X) : Prop :=
  S.equivalent
    (S.close GXY.result)
    (S.close GYX.result)


/-- Global cyclicity of a shadow relative to one chosen weak enddiary
composition system. This does not assert source commutativity. -/
def CyclicOn
    (S : DiaryCyclicShadow.{u, v} A)
    (C : EndDiaryCompositionSystem.{u, w} A) : Prop :=
  ∀ X Y,
    S.equivalent
      (S.close (C.compose X Y))
      (S.close (C.compose Y X))

/-- Source noncommutativity is measured in the source equivalence, independently
of what the cyclic shadow forgets. -/
def SourceNoncommutative
    (C : EndDiaryCompositionSystem.{u, w} A) : Prop :=
  ∃ X Y,
    ¬ C.equivalent (C.compose X Y) (C.compose Y X)

/-- The intended ECIA discriminator: cyclic shadow together with genuinely
noncommutative source composition. -/
def CyclicButNoncommutative
    (S : DiaryCyclicShadow.{u, v} A)
    (C : EndDiaryCompositionSystem.{u, w} A) : Prop :=
  S.CyclicOn C ∧ C.SourceNoncommutative

/-- The identity relation gives the strictest possible shadow equivalence. -/
def strict
    (close : EndDiary A → EndDiary A) :
    DiaryCyclicShadow.{u, u} A where
  Cycle := EndDiary A
  equivalent := Eq
  equivalent_refl := by intro c; rfl
  equivalent_symm := by intro c d h; exact h.symm
  equivalent_trans := by intro c d e h₁ h₂; exact h₁.trans h₂
  close := close

end DiaryCyclicShadow
end CausalGeometry
