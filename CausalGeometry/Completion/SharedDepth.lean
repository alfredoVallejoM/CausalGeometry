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

/-- Evaluation of a truncation class at its deepest visible level. -/
def quotientEval (n : ℕ) :
    T.TruncationQuotient n → T.Obj n :=
  Quotient.lift
    (fun x : T.CompatibleHistory => x.at n)
    (by
      intro x y hxy
      exact hxy n le_rfl)

/-- The depth-n quotient retains exactly the level-n observation: evaluation
is always injective because coherence propagates equality to all shallower
levels. -/
theorem quotientEval_injective (n : ℕ) :
    Function.Injective (T.quotientEval n) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro x y hxy
  apply Quotient.sound
  apply (T.agreeThrough_iff_agreeAt).2
  exact hxy

/-- Every finite observation at level n extends to a complete compatible
history. -/
def LevelExtendable (n : ℕ) : Prop :=
  Function.Surjective
    (fun x : T.CompatibleHistory => x.at n)

/-- When all level-n states extend to complete histories, the finite
observational quotient is exactly the level-n state space. -/
noncomputable def truncationQuotientEquivLevel
    (n : ℕ) (h : T.LevelExtendable n) :
    T.TruncationQuotient n ≃ T.Obj n :=
  Equiv.ofBijective (T.quotientEval n)
    ⟨T.quotientEval_injective n, h⟩

/-- Deeper truncation quotients canonically forget to shallower quotients. -/
def truncateQuotient {m n : ℕ} (hmn : m ≤ n) :
    T.TruncationQuotient n → T.TruncationQuotient m :=
  Quotient.map id (by
    intro x y hxy
    exact T.agreeThrough_mono hxy hmn)

@[simp] theorem truncateQuotient_refl
    (n : ℕ) (q : T.TruncationQuotient n) :
    T.truncateQuotient (le_refl n) q = q := by
  refine Quotient.inductionOn q ?_
  intro x
  rfl

theorem truncateQuotient_comp
    {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n)
    (q : T.TruncationQuotient n) :
    T.truncateQuotient hlm
        (T.truncateQuotient hmn q) =
      T.truncateQuotient (hlm.trans hmn) q := by
  refine Quotient.inductionOn q ?_
  intro x
  rfl

/-- Evaluation commutes with forgetting one causal depth. -/
theorem quotientEval_truncate_succ
    (n : ℕ) (q : T.TruncationQuotient (n + 1)) :
    T.quotientEval n
        (T.truncateQuotient (Nat.le_succ n) q) =
      T.drop n (T.quotientEval (n + 1) q) := by
  refine Quotient.inductionOn q ?_
  intro x
  exact (x.compatible n).symm

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
