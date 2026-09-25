import Mathlib.Algebra.Group.Conj

namespace CausalGeometry

universe g

namespace PrimitiveConjugacy

variable {Γ : Type g} [Group Γ]

/-- A proper power uses an exponent at least two. -/
def IsProperPower (γ : Γ) : Prop :=
  ∃ δ : Γ, ∃ n : ℕ,
    2 ≤ n ∧
      δ ^ n = γ

/-- Primitive nontrivial group element: not the identity and not a proper
positive power. -/
def IsPrimitive (γ : Γ) : Prop :=
  γ ≠ 1 ∧ ¬ IsProperPower γ

/-- Proper-power status is invariant under every group automorphism. -/
theorem isProperPower_map_iff
    (φ : Γ ≃* Γ)
    (γ : Γ) :
    IsProperPower (φ γ) ↔
      IsProperPower γ := by
  constructor
  · rintro ⟨δ, n, hn, hδ⟩
    refine ⟨φ.symm δ, n, hn, ?_⟩
    have hmap :=
      congrArg φ.symm hδ
    simpa using hmap
  · rintro ⟨δ, n, hn, hδ⟩
    refine ⟨φ δ, n, hn, ?_⟩
    simpa [← map_pow] using
      congrArg φ hδ

/-- Primitivity is invariant under every group automorphism. -/
theorem isPrimitive_map_iff
    (φ : Γ ≃* Γ)
    (γ : Γ) :
    IsPrimitive (φ γ) ↔
      IsPrimitive γ := by
  unfold IsPrimitive
  constructor
  · rintro ⟨hne, hpow⟩
    constructor
    · intro h1
      apply hne
      simpa [h1]
    · intro hp
      exact hpow
        ((isProperPower_map_iff φ γ).2 hp)
  · rintro ⟨hne, hpow⟩
    constructor
    · intro h1
      apply hne
      apply φ.injective
      simpa using h1
    · intro hp
      exact hpow
        ((isProperPower_map_iff φ γ).1 hp)

/-- Conjugation preserves proper-power status. -/
theorem isProperPower_conjugate_iff
    (δ γ : Γ) :
    IsProperPower
        ((MulAut.conj δ) γ) ↔
      IsProperPower γ :=
  isProperPower_map_iff
    (MulAut.conj δ) γ

/-- Conjugation preserves primitive status. -/
theorem isPrimitive_conjugate_iff
    (δ γ : Γ) :
    IsPrimitive
        ((MulAut.conj δ) γ) ↔
      IsPrimitive γ :=
  isPrimitive_map_iff
    (MulAut.conj δ) γ

/-- Primitive predicate on a conjugacy class, expressed by existence of one
primitive representative. Conjugacy invariance proves below that this is
equivalent to every representative being primitive. -/
def IsPrimitiveClass
    (C : ConjClasses Γ) : Prop :=
  ∃ γ : Γ,
    ConjClasses.mk γ = C ∧
      IsPrimitive γ

theorem primitive_of_mk_eq_primitiveClass
    {γ : Γ}
    (hC :
      IsPrimitiveClass
        (ConjClasses.mk γ)) :
    IsPrimitive γ := by
  rcases hC with
    ⟨δ, hδclass, hδprim⟩
  have hconj :
      IsConj δ γ :=
    ConjClasses.mk_eq_mk_iff_isConj.mp
      hδclass
  rcases isConj_iff.mp hconj with
    ⟨c, hc⟩
  have hmap :
      (MulAut.conj c) δ = γ := by
    simpa [MulAut.conj_apply] using hc
  rw [← hmap]
  exact
    (isPrimitive_conjugate_iff c δ).2
      hδprim

theorem primitiveClass_mk_iff
    (γ : Γ) :
    IsPrimitiveClass
        (ConjClasses.mk γ) ↔
      IsPrimitive γ := by
  constructor
  · exact primitive_of_mk_eq_primitiveClass
  · intro h
    exact ⟨γ, rfl, h⟩

end PrimitiveConjugacy
end CausalGeometry
