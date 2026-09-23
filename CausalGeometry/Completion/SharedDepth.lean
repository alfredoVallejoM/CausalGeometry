import CausalGeometry.Completion.InverseTower

namespace CausalGeometry

universe u

namespace InverseTower

variable (T : InverseTower)

/-- Two completed histories agree at one finite restriction level. -/
def AgreeAt (x y : T.CompatibleHistory) (n : ℕ) : Prop :=
  x.at n = y.at n

/-- Agreement through every level up to n. -/
def AgreeThrough (x y : T.CompatibleHistory) (n : ℕ) : Prop :=
  ∀ k, k ≤ n → x.at k = y.at k

theorem agreeAt_refl (x : T.CompatibleHistory) (n : ℕ) :
    T.AgreeAt x x n := rfl

theorem agreeAt_symm {x y : T.CompatibleHistory} {n : ℕ}
    (h : T.AgreeAt x y n) :
    T.AgreeAt y x n :=
  h.symm

theorem agreeAt_trans {x y z : T.CompatibleHistory} {n : ℕ}
    (hxy : T.AgreeAt x y n)
    (hyz : T.AgreeAt y z n) :
    T.AgreeAt x z n :=
  hxy.trans hyz

/-- Agreement at level n+1 forces agreement one level earlier by applying the
restriction map. -/
theorem agreeAt_prev {x y : T.CompatibleHistory} {n : ℕ}
    (h : T.AgreeAt x y (n + 1)) :
    T.AgreeAt x y n := by
  unfold AgreeAt at h ⊢
  have hdrop := congrArg (T.drop n) h
  simpa [x.compatible n, y.compatible n] using hdrop

/-- Finite observations are nested: agreement at a deeper level implies
agreement at every shallower level. -/
theorem agreeAt_of_le {x y : T.CompatibleHistory} {m n : ℕ}
    (hmn : m ≤ n) (h : T.AgreeAt x y n) :
    T.AgreeAt x y m := by
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      exact h
  | succ n ih =>
      rcases Nat.eq_or_lt_of_le hmn with hEq | hLt
      · subst m
        exact h
      · have hprev : T.AgreeAt x y n := by
          exact T.agreeAt_prev h
        exact ih (Nat.le_of_lt_succ hLt) hprev

theorem agreeThrough_refl (x : T.CompatibleHistory) (n : ℕ) :
    T.AgreeThrough x x n := by
  intro k hk
  rfl

theorem agreeThrough_symm {x y : T.CompatibleHistory} {n : ℕ}
    (h : T.AgreeThrough x y n) :
    T.AgreeThrough y x n := by
  intro k hk
  exact (h k hk).symm

theorem agreeThrough_trans {x y z : T.CompatibleHistory} {n : ℕ}
    (hxy : T.AgreeThrough x y n)
    (hyz : T.AgreeThrough y z n) :
    T.AgreeThrough x z n := by
  intro k hk
  exact (hxy k hk).trans (hyz k hk)

theorem agreeThrough_mono {x y : T.CompatibleHistory} {m n : ℕ}
    (h : T.AgreeThrough x y n) (hmn : m ≤ n) :
    T.AgreeThrough x y m := by
  intro k hk
  exact h k (hk.trans hmn)

/-- Because histories are coherent, agreement through depth n is equivalent to
agreement at the deepest observed level n. -/
theorem agreeThrough_iff_agreeAt
    {x y : T.CompatibleHistory} {n : ℕ} :
    T.AgreeThrough x y n ↔ T.AgreeAt x y n := by
  constructor
  · intro h
    exact h n le_rfl
  · intro h k hk
    exact T.agreeAt_of_le hk h

/-- Truncation indistinguishability at depth n is an honest equivalence
relation. -/
def truncationSetoid (n : ℕ) : Setoid T.CompatibleHistory where
  r := fun x y => T.AgreeThrough x y n
  iseqv := ⟨
    fun x => T.agreeThrough_refl x n,
    fun h => T.agreeThrough_symm h,
    fun hxy hyz => T.agreeThrough_trans hxy hyz⟩

/-- The finite observational quotient at depth n. -/
def TruncationQuotient (n : ℕ) :=
  Quotient (T.truncationSetoid n)

/-- The strong ultrametric-ball law appears already before assigning any
numerical distance: two depth-n correlations compose transitively. -/
theorem strong_ball_law
    {x y z : T.CompatibleHistory} {n : ℕ}
    (hxy : T.AgreeThrough x y n)
    (hyz : T.AgreeThrough y z n) :
    T.AgreeThrough x z n :=
  T.agreeThrough_trans hxy hyz

end InverseTower
end CausalGeometry
