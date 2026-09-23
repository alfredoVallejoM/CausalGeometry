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

end InverseTower
end CausalGeometry
