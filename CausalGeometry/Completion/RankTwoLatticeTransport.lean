import CausalGeometry.Completion.LatticeGraph
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.LinearAlgebra.Quotient.Basic

namespace CausalGeometry

universe u v

namespace RankTwoLattice

variable
    {O : Type u} {K : Type v}
    [CommRing O] [Field K] [Algebra O K]

/-- O-linear shadow of a K-linear ambient equivalence. -/
def ambientRestrict
    (E : (K × K) ≃ₗ[K] (K × K)) :
    (K × K) ≃ₗ[O] (K × K) :=
  E.restrictScalars O

/-- Transport a rank-two lattice by an ambient K-linear automorphism. -/
def mapLinearEquiv
    (E : (K × K) ≃ₗ[K] (K × K))
    (L : RankTwoLattice O K) :
    RankTwoLattice O K where
  carrier :=
    L.carrier.map
      (ambientRestrict
        (O := O) E).toLinearMap
  fg :=
    L.fg.map
      (ambientRestrict
        (O := O) E).toLinearMap
  spans := by
    have hcarrier :
        (((L.carrier.map
          (ambientRestrict
            (O := O) E).toLinearMap :
              Submodule O (K × K)) :
            Set (K × K))) =
          E '' (L.carrier : Set (K × K)) := by
      ext x
      simp [ambientRestrict]
    rw [hcarrier]
    rw [← Submodule.map_span]
    rw [L.spans]
    simp

@[simp] theorem mapLinearEquiv_carrier
    (E : (K × K) ≃ₗ[K] (K × K))
    (L : RankTwoLattice O K) :
    (L.mapLinearEquiv E).carrier =
      L.carrier.map
        (ambientRestrict
          (O := O) E).toLinearMap :=
  rfl

/-- Equivalence between a lattice carrier and its transported carrier. -/
def carrierEquiv
    (E : (K × K) ≃ₗ[K] (K × K))
    (L : RankTwoLattice O K) :
    L.carrier ≃ₗ[O]
      (L.mapLinearEquiv E).carrier :=
  LinearEquiv.submoduleMap
    (ambientRestrict
      (O := O) E)
    L.carrier

@[simp] theorem carrierEquiv_apply_coe
    (E : (K × K) ≃ₗ[K] (K × K))
    (L : RankTwoLattice O K)
    (x : L.carrier) :
    ((L.carrierEquiv E x :
      (L.mapLinearEquiv E).carrier) :
      K × K) =
      E x.1 := by
  rfl

@[simp] theorem mapLinearEquiv_refl
    (L : RankTwoLattice O K) :
    L.mapLinearEquiv
        (LinearEquiv.refl K (K × K)) =
      L := by
  apply RankTwoLattice.ext
  ext x
  simp [mapLinearEquiv,
    ambientRestrict]

theorem mapLinearEquiv_trans
    (E F : (K × K) ≃ₗ[K] (K × K))
    (L : RankTwoLattice O K) :
    (L.mapLinearEquiv E).mapLinearEquiv F =
      L.mapLinearEquiv (E.trans F) := by
  apply RankTwoLattice.ext
  ext x
  simp [mapLinearEquiv,
    ambientRestrict,
    Submodule.mem_map]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact
      ⟨E z, ⟨z, hz, rfl⟩, rfl⟩

/-- A sublattice inclusion is carried to the corresponding inclusion after an
ambient equivalence. -/
theorem mapLinearEquiv_mono
    (E : (K × K) ≃ₗ[K] (K × K))
    {L M : RankTwoLattice O K}
    (h : M.carrier ≤ L.carrier) :
    (M.mapLinearEquiv E).carrier ≤
      (L.mapLinearEquiv E).carrier :=
  Submodule.map_mono h

/-- The carrier equivalence sends the relative child submodule exactly to the
relative child submodule after transport. -/
theorem carrierEquiv_map_submoduleOf
    (E : (K × K) ≃ₗ[K] (K × K))
    {L M : RankTwoLattice O K}
    (h : M.carrier ≤ L.carrier) :
    (M.carrier.submoduleOf L.carrier).map
        (L.carrierEquiv E).toLinearMap =
      (M.mapLinearEquiv E).carrier.submoduleOf
        (L.mapLinearEquiv E).carrier := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    let z :
        (L.mapLinearEquiv E).carrier := x
    let y : L.carrier :=
      (L.carrierEquiv E).symm z
    refine ⟨y, ?_, ?_⟩
    · change
        y.1 ∈ M.carrier
      have hz :
          z.1 ∈
            (M.mapLinearEquiv E).carrier :=
        hx
      rcases hz with ⟨m, hm, hmE⟩
      have hEq :
          E y.1 = E m := by
        simpa [y, z] using hmE.symm
      have : y.1 = m :=
        E.injective hEq
      simpa [this] using hm
    · apply Subtype.ext
      simp [y, z]

/-- Quotient modules of an inclusion are linearly equivalent after ambient
transport. -/
noncomputable def quotientEquiv
    (E : (K × K) ≃ₗ[K] (K × K))
    {L M : RankTwoLattice O K}
    (h : M.carrier ≤ L.carrier) :
    (L.carrier ⧸
      M.carrier.submoduleOf L.carrier) ≃ₗ[O]
      ((L.mapLinearEquiv E).carrier ⧸
        (M.mapLinearEquiv E).carrier.submoduleOf
          (L.mapLinearEquiv E).carrier) :=
  Submodule.Quotient.equiv
    (M.carrier.submoduleOf L.carrier)
    ((M.mapLinearEquiv E).carrier.submoduleOf
      (L.mapLinearEquiv E).carrier)
    (L.carrierEquiv E)
    (L.carrierEquiv_map_submoduleOf E h)

/-- Index-q lattice steps are invariant under ambient linear equivalence. -/
theorem IndexStep.mapLinearEquiv
    {q : ℕ}
    {L M : RankTwoLattice O K}
    (h : IndexStep q L M)
    (E : (K × K) ≃ₗ[K] (K × K)) :
    IndexStep q
      (L.mapLinearEquiv E)
      (M.mapLinearEquiv E) where
  le :=
    mapLinearEquiv_mono E h.le
  quotient_card := by
    rw [← h.quotient_card]
    exact
      Nat.card_congr
        (quotientEquiv E h.le).toEquiv

/-- Transporting by the inverse equivalence recovers the original lattice. -/
@[simp] theorem mapLinearEquiv_symm_map
    (E : (K × K) ≃ₗ[K] (K × K))
    (L : RankTwoLattice O K) :
    (L.mapLinearEquiv E).mapLinearEquiv E.symm =
      L := by
  rw [mapLinearEquiv_trans]
  simp

/-- Homothety classes are functorial under ambient linear equivalence. -/
def classMap
    (E : (K × K) ≃ₗ[K] (K × K)) :
    HomothetyClass (O := O) (K := K) →
      HomothetyClass (O := O) (K := K) :=
  Quotient.map
    (mapLinearEquiv E)
    (by
      intro L M h
      rcases h with ⟨u, rfl⟩
      refine ⟨u, ?_⟩
      apply RankTwoLattice.ext
      ext x
      simp [
        mapLinearEquiv,
        scale,
        ambientRestrict,
        Submodule.mem_map
      ]
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        exact
          ⟨E z, ⟨z, hz, rfl⟩, by
            simp [smul_comm]⟩
      · rintro ⟨y, ⟨z, hz, hzE⟩, hy⟩
        subst y
        refine
          ⟨u • z, ?_, ?_⟩
        · exact
            ⟨z, hz, rfl⟩
        · simp [smul_comm])


/-- Ambient transport specializes exactly to scalar homothety. -/
theorem mapLinearEquiv_scaleEquivK
    (u : Kˣ)
    (L : RankTwoLattice O K) :
    L.mapLinearEquiv
        (scaleEquivK (O := O) u) =
      L.scale u := by
  apply RankTwoLattice.ext
  rfl

@[simp] theorem classMap_classOf
    (E : (K × K) ≃ₗ[K] (K × K))
    (L : RankTwoLattice O K) :
    classMap E (classOf L) =
      classOf (L.mapLinearEquiv E) :=
  rfl

/-- Ambient linear equivalence acts invertibly on homothety classes. -/
def classEquiv
    (E : (K × K) ≃ₗ[K] (K × K)) :
    HomothetyClass (O := O) (K := K) ≃
      HomothetyClass (O := O) (K := K) where
  toFun :=
    classMap E
  invFun :=
    classMap E.symm
  left_inv := by
    intro x
    refine Quotient.inductionOn x ?_
    intro L
    simp [classMap]
  right_inv := by
    intro x
    refine Quotient.inductionOn x ?_
    intro L
    simp [classMap]

@[simp] theorem classEquiv_apply
    (E : (K × K) ≃ₗ[K] (K × K))
    (L : RankTwoLattice O K) :
    classEquiv E (classOf L) =
      classOf (L.mapLinearEquiv E) :=
  rfl

@[simp] theorem classEquiv_symm_apply
    (E : (K × K) ≃ₗ[K] (K × K))
    (L : RankTwoLattice O K) :
    (classEquiv E).symm (classOf L) =
      classOf (L.mapLinearEquiv E.symm) :=
  rfl

/-- q-adjacency of homothety classes is invariant under ambient change of
basis. -/
theorem classAdjacent_map
    (E : (K × K) ≃ₗ[K] (K × K))
    {q : ℕ}
    {x y : HomothetyClass (O := O) (K := K)}
    (h : ClassAdjacent q x y) :
    ClassAdjacent q
      (classEquiv E x)
      (classEquiv E y) := by
  rcases h with
    ⟨L, M, hx, hy, hLM | hML⟩
  · refine
      ⟨L.mapLinearEquiv E,
        M.mapLinearEquiv E,
        ?_, ?_, Or.inl
          (hLM.mapLinearEquiv E)⟩
    · rw [← hx]
      rfl
    · rw [← hy]
      rfl
  · refine
      ⟨L.mapLinearEquiv E,
        M.mapLinearEquiv E,
        ?_, ?_, Or.inr
          (hML.mapLinearEquiv E)⟩
    · rw [← hx]
      rfl
    · rw [← hy]
      rfl

/-- Exact equivalence form of adjacency invariance. -/
theorem classAdjacent_map_iff
    (E : (K × K) ≃ₗ[K] (K × K))
    {q : ℕ}
    {x y : HomothetyClass (O := O) (K := K)} :
    ClassAdjacent q
        (classEquiv E x)
        (classEquiv E y) ↔
      ClassAdjacent q x y := by
  constructor
  · intro h
    have h' :=
      classAdjacent_map
        E.symm h
    simpa using h'
  · exact classAdjacent_map E


end RankTwoLattice
end CausalGeometry
