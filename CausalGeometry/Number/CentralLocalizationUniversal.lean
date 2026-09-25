import CausalGeometry.Number.CentralBilateralLocalization
import Mathlib.Algebra.Group.Commute.Hom

namespace CausalGeometry

universe u v

namespace CausalLocalization

variable {α : Type u} [CancelMonoid α]
variable {S : Submonoid α}
variable (hS : CentralDenominators S)

namespace CentralUniversal

variable {G : Type v} [Group G]
variable (f : α →* G)

/-- Centrality survives under every multiplicative target map, at least on the
image of the ambient monoid. -/
theorem denominator_commutes_image
    (s : S) (a : α) :
    Commute
      (f (s : α)) (f a) :=
  (hS s a).map f

/-- Cross multiplication of central fractions is respected by the usual
group-valued right-fraction evaluation. -/
theorem right_realize_respects
    {x y : RightFraction S}
    (h : centralRightRel x y) :
    RightFraction.realize f x =
      RightFraction.realize f y := by
  rcases x with ⟨a, s⟩
  rcases y with ⟨b, t⟩
  change
    a * (t : α) =
      b * (s : α) at h
  have hm := congrArg f h
  simp only [map_mul] at hm
  change
    f a * (f (s : α))⁻¹ =
      f b * (f (t : α))⁻¹
  have hst :
      Commute
        (f (s : α))
        (f (t : α)) :=
    hS.denominator_commutes_image f
      s (t : α)
  calc
    f a * (f (s : α))⁻¹
        =
      ((f a * f (t : α)) *
        (f (t : α))⁻¹) *
          (f (s : α))⁻¹ := by
            simp [mul_assoc]
    _ =
      ((f b * f (s : α)) *
        (f (t : α))⁻¹) *
          (f (s : α))⁻¹ := by
            rw [hm]
    _ =
      (f b *
        (f (s : α) *
          (f (t : α))⁻¹)) *
            (f (s : α))⁻¹ := by
              simp [mul_assoc]
    _ =
      (f b *
        ((f (t : α))⁻¹ *
          f (s : α))) *
            (f (s : α))⁻¹ := by
              rw [hst.inv_right.eq]
    _ =
      f b * (f (t : α))⁻¹ := by
            simp [mul_assoc]

/-- Representative multiplication evaluates multiplicatively. -/
theorem right_mul_compatible
    (x y : RightFraction S) :
    RightFraction.realize f
        (centralRightMulRep x y) =
      RightFraction.realize f x *
        RightFraction.realize f y := by
  rcases x with ⟨a, s⟩
  rcases y with ⟨b, t⟩
  have hsb :
      Commute
        (f (s : α)) (f b) :=
    hS.denominator_commutes_image f s b
  change
    f (a * b) *
        (f (((t * s : S) : α)))⁻¹ =
      (f a * (f (s : α))⁻¹) *
        (f b * (f (t : α))⁻¹)
  simp only [map_mul, Submonoid.coe_mul,
    mul_inv_rev]
  calc
    (f a * f b) *
        ((f (s : α))⁻¹ *
          (f (t : α))⁻¹)
        =
      (f a *
        (f b * (f (s : α))⁻¹)) *
          (f (t : α))⁻¹ := by
            simp [mul_assoc]
    _ =
      (f a *
        ((f (s : α))⁻¹ * f b)) *
          (f (t : α))⁻¹ := by
            rw [hsb.inv_left.eq.symm]
    _ =
      (f a * (f (s : α))⁻¹) *
        (f b * (f (t : α))⁻¹) := by
          simp [mul_assoc]

/-- Any monoid morphism into a group automatically realizes the certified
right central localization. -/
def rightRealization :
    (centralRightFractionCalculus hS).GroupRealization
      G f where
  respects := by
    intro x y h
    exact hS.right_realize_respects f h
  mul_compatible :=
    hS.right_mul_compatible f

/-- Canonical universal extension through the right localization quotient. -/
def rightExtension :
    (centralRightFractionCalculus hS).QuotientType →* G :=
  (hS.rightRealization f).realizeHom

@[simp] theorem rightExtension_source
    (a : α) :
    hS.rightExtension f
        ((centralRightFractionCalculus hS).sourceHom a) =
      f a :=
  (hS.rightRealization f).realizeHom_source a

/-- Uniqueness of the right universal extension. -/
theorem rightExtension_unique
    (g :
      (centralRightFractionCalculus hS).QuotientType →* G)
    (hsource :
      ∀ a,
        g ((centralRightFractionCalculus hS).sourceHom a) =
          f a) :
    g = hS.rightExtension f :=
  (hS.rightRealization f).hom_ext_of_source
    g hsource

/-- Left and right presentation evaluations coincide because denominators are
central in the source and hence commute with source numerators after mapping. -/
theorem left_realize_eq_right
    (x : LeftFraction S) :
    LeftFraction.realize f x =
      RightFraction.realize f
        ((centralPresentationEquiv
          (S := S)).symm x) := by
  rcases x with ⟨s, a⟩
  change
    (f (s : α))⁻¹ * f a =
      f a * (f (s : α))⁻¹
  exact
    (hS.denominator_commutes_image f
      s a).inv_left.eq

/-- Any monoid morphism into a group also realizes the left central
localization automatically. -/
def leftRealization :
    (centralLeftFractionCalculus hS).GroupRealization
      G f where
  respects := by
    intro x y hxy
    rw [hS.left_realize_eq_right f x,
      hS.left_realize_eq_right f y]
    exact
      hS.right_realize_respects f hxy
  mul_compatible := by
    intro x y
    rw [hS.left_realize_eq_right f
      (centralLeftMulRep x y),
      hS.left_realize_eq_right f x,
      hS.left_realize_eq_right f y]
    simpa [centralLeftMulRep,
      centralRightMulRep] using
      hS.right_mul_compatible f
        ((centralPresentationEquiv
          (S := S)).symm x)
        ((centralPresentationEquiv
          (S := S)).symm y)

/-- Canonical universal extension through the left localization quotient. -/
def leftExtension :
    (centralLeftFractionCalculus hS).QuotientType →* G :=
  (hS.leftRealization f).realizeHom

@[simp] theorem leftExtension_source
    (a : α) :
    hS.leftExtension f
        ((centralLeftFractionCalculus hS).sourceHom a) =
      f a :=
  (hS.leftRealization f).realizeHom_source a

theorem leftExtension_unique
    (g :
      (centralLeftFractionCalculus hS).QuotientType →* G)
    (hsource :
      ∀ a,
        g ((centralLeftFractionCalculus hS).sourceHom a) =
          f a) :
    g = hS.leftExtension f :=
  (hS.leftRealization f).hom_ext_of_source
    g hsource

/-- The bilateral comparison intertwines the two canonical universal
extensions. -/
theorem bilateral_extension_compat
    (q :
      (centralRightFractionCalculus hS).QuotientType) :
    hS.leftExtension f
        ((centralBilateralComparison hS).equivalence q) =
      hS.rightExtension f q := by
  let g :
      (centralRightFractionCalculus hS).QuotientType →* G :=
    (hS.leftExtension f).comp
      (centralBilateralComparison hS).equivalence.toMonoidHom
  have hg :
      g = hS.rightExtension f := by
    apply hS.rightExtension_unique f
    intro a
    change
      hS.leftExtension f
          ((centralBilateralComparison hS).equivalence
            ((centralRightFractionCalculus hS).sourceHom a)) =
        f a
    rw [(centralBilateralComparison hS).equivalence_source]
    exact hS.leftExtension_source f a
  exact MonoidHom.congr_fun hg q

end CentralUniversal
end CausalLocalization
end CausalGeometry
