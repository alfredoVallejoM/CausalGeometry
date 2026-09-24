import CausalGeometry.Process.Composition

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
