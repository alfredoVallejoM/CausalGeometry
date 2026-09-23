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

end InverseTower
end CausalGeometry
