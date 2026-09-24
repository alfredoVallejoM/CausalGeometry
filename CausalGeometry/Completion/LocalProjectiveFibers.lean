import CausalGeometry.Completion.LocalProjectiveMapCharts

namespace CausalGeometry

universe u v

namespace LocalProjectivePair

variable
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S]

/-- Underlying ring coordinate of one canonical projective chart. -/
def chartValue : Chart S → S
  | Sum.inl y => y
  | Sum.inr u => u.1

/-- The fiber over an affine target chart is exactly a fiber of the ring hom. -/
noncomputable def affineChartFiberEquiv
    (f : R →+* S) [IsLocalHom f]
    (y : S) :
    {c : Chart R // chartMap f c = Sum.inl y} ≃
      {x : R // f x = y} where
  toFun := fun c => by
    rcases c with ⟨c, hc⟩
    cases c with
    | inl x =>
        exact ⟨x, Sum.inl.inj hc⟩
    | inr u =>
        cases hc
  invFun := fun x =>
    ⟨Sum.inl x.1, congrArg Sum.inl x.2⟩
  left_inv := by
    intro c
    rcases c with ⟨c, hc⟩
    cases c with
    | inl x =>
        apply Subtype.ext
        rfl
    | inr u =>
        cases hc
  right_inv := by
    intro x
    apply Subtype.ext
    rfl

/-- The fiber over an infinity target chart is also exactly a fiber of the
ring hom. Locality guarantees that every lift of a target non-unit is itself a
non-unit. -/
noncomputable def infinityChartFiberEquiv
    (f : R →+* S) [IsLocalHom f]
    (u : Nonunit S) :
    {c : Chart R // chartMap f c = Sum.inr u} ≃
      {x : R // f x = u.1} where
  toFun := fun c => by
    rcases c with ⟨c, hc⟩
    cases c with
    | inl x =>
        cases hc
    | inr v =>
        have hv :
            mapNonunit f v = u :=
          Sum.inr.inj hc
        exact ⟨v.1, congrArg Subtype.val hv⟩
  invFun := fun x => by
    have hx_nonunit : ¬ IsUnit x.1 := by
      intro hx
      apply u.2
      rw [← x.2]
      exact hx.map f
    let v : Nonunit R := ⟨x.1, hx_nonunit⟩
    refine ⟨Sum.inr v, ?_⟩
    apply congrArg Sum.inr
    apply Subtype.ext
    exact x.2
  left_inv := by
    intro c
    rcases c with ⟨c, hc⟩
    cases c with
    | inl x =>
        cases hc
    | inr v =>
        apply Subtype.ext
        rfl
  right_inv := by
    intro x
    apply Subtype.ext
    rfl

/-- Every chart-map fiber is a ring-hom fiber, whichever chart contains the
target. -/
noncomputable def chartFiberEquivRingFiber
    (f : R →+* S) [IsLocalHom f]
    (q : Chart S) :
    {c : Chart R // chartMap f c = q} ≃
      {x : R // f x = chartValue q} := by
  cases q with
  | inl y =>
      exact affineChartFiberEquiv f y
  | inr u =>
      exact infinityChartFiberEquiv f u

/-- Strong fiber theorem: projectivization along a local ring hom does not
change the size/type of individual fibers. The projective fiber is equivalent
to a ring fiber over the canonical chart coordinate of the target point. -/
noncomputable def projectiveFiberEquivRingFiber
    (f : R →+* S) [IsLocalHom f]
    (q : Line S) :
    {x : Line R // map f x = q} ≃
      {x : R //
        f x = chartValue ((chartEquiv (R := S)).symm q)} :=
  (mapFiberEquivChartFiber f q).trans
    (chartFiberEquivRingFiber f
      ((chartEquiv (R := S)).symm q))

end LocalProjectivePair
end CausalGeometry
