namespace CausalGeometry

universe u

/-- Minimal inverse tower used by primary causal completions. -/
structure InverseTower where
  Obj : ℕ → Type u
  drop : ∀ n, Obj (n + 1) → Obj n

namespace InverseTower

variable (T : InverseTower)

/-- An infinite coherent history through all finite restriction levels. -/
structure CompatibleHistory where
  at : ∀ n, T.Obj n
  compatible : ∀ n, T.drop n (at (n + 1)) = at n

/-- Observation of a completed history at a finite level. -/
def CompatibleHistory.truncate (x : T.CompatibleHistory) (n : ℕ) :
    T.Obj n :=
  x.at n

@[simp] theorem CompatibleHistory.drop_truncate
    (x : T.CompatibleHistory) (n : ℕ) :
    T.drop n (x.truncate (n + 1)) = x.truncate n :=
  x.compatible n

/-- Two compatible histories are equal once all finite observations agree. -/
theorem CompatibleHistory.eq_of_at_eq
    {x y : T.CompatibleHistory}
    (h : ∀ n, x.at n = y.at n) :
    x = y := by
  cases x with
  | mk xa hx =>
      cases y with
      | mk ya hy =>
          have hfun : xa = ya := funext h
          subst ya
          rfl

end InverseTower
end CausalGeometry
