import CausalGeometry.Calculus.HodgeComplex
import Mathlib.Tactic

namespace CausalGeometry.Models

/-- d0(a)=(a,0). -/
def hodgeControl_d0 :
    ℚ →ₗ[ℚ] (ℚ × ℚ) where
  toFun := fun a => (a, 0)
  map_add' := by
    intro a b
    rfl
  map_smul' := by
    intro a b
    ext <;> simp

/-- d1=0, so every degree-one cochain is closed. -/
def hodgeControl_d1 :
    (ℚ × ℚ) →ₗ[ℚ] ℚ :=
  0

/-- Concrete cochain complex with one nontrivial H1 direction. -/
def hodgeControlComplex :
    CausalCochainComplex
      ℚ ℚ (ℚ × ℚ) ℚ where
  d0 := hodgeControl_d0
  d1 := hodgeControl_d1
  d_sq := by
    ext a
    rfl

/-- δ0 is horizontal projection. -/
def hodgeControl_codiff0 :
    (ℚ × ℚ) →ₗ[ℚ] ℚ where
  toFun := fun x => x.1
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro a x
    rfl

def hodgeControl_codiff1 :
    ℚ →ₗ[ℚ] (ℚ × ℚ) :=
  0

def hodgeControl_pairing0 :
    ℚ →ₗ[ℚ] ℚ →ₗ[ℚ] ℚ :=
  LinearMap.mul ℚ ℚ

def hodgeControl_pairing1 :
    (ℚ × ℚ) →ₗ[ℚ]
      (ℚ × ℚ) →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ
    (fun x y =>
      x.1 * y.1 +
        x.2 * y.2)
    (by
      intro x y z
      simp
      ring)
    (by
      intro a x y
      simp
      ring)
    (by
      intro x y z
      simp
      ring)
    (by
      intro a x y
      simp
      ring)

def hodgeControl_pairing2 :
    ℚ →ₗ[ℚ] ℚ →ₗ[ℚ] ℚ :=
  LinearMap.mul ℚ ℚ

/-- Standard algebraic Hodge data. -/
def hodgeControlData :
    CausalHodgeData
      hodgeControlComplex where
  codiff0 :=
    hodgeControl_codiff0
  codiff1 :=
    hodgeControl_codiff1
  pairing0 :=
    hodgeControl_pairing0
  pairing1 :=
    hodgeControl_pairing1
  pairing2 :=
    hodgeControl_pairing2

  adjoint0 := by
    intro x y
    rcases y with ⟨a, b⟩
    simp [
      hodgeControlComplex,
      hodgeControl_d0,
      hodgeControl_codiff0,
      hodgeControl_pairing0,
      hodgeControl_pairing1
    ]

  adjoint1 := by
    intro x y
    simp [
      hodgeControlComplex,
      hodgeControl_d1,
      hodgeControl_codiff1,
      hodgeControl_pairing1,
      hodgeControl_pairing2
    ]

/-- Degree-one Laplacian is horizontal projection (x,y)↦(x,0). -/
theorem hodgeControl_laplacian1_apply
    (x : ℚ × ℚ) :
    hodgeControlData.laplacian1 x =
      (x.1, 0) := by
  rfl

/-- Harmonic iff horizontal coordinate vanishes. -/
theorem hodgeControl_harmonic_iff
    (x : ℚ × ℚ) :
    x ∈ hodgeControlData.Harmonic1 ↔
      x.1 = 0 := by
  change
    hodgeControlData.laplacian1 x = 0 ↔
      _
  rw [hodgeControl_laplacian1_apply]
  constructor
  · intro h
    exact congrArg Prod.fst h
  · intro h
    ext <;> simp [h]

/-- Every degree-one cochain is closed. -/
theorem hodgeControl_closed_all
    (x : ℚ × ℚ) :
    x ∈ hodgeControlComplex.Closed1 := by
  rfl

/-- Exact degree-one cochains are precisely the horizontal axis. -/
theorem hodgeControl_exact_iff
    (x : ℚ × ℚ) :
    x ∈ hodgeControlComplex.Exact1 ↔
      x.2 = 0 := by
  constructor
  · rintro ⟨a, ha⟩
    have h := congrArg Prod.snd ha
    simpa [hodgeControlComplex,
      hodgeControl_d0] using h
  · intro hx
    refine ⟨x.1, ?_⟩
    ext <;> simp [
      hodgeControlComplex,
      hodgeControl_d0,
      hx
    ]

/-- Explicit Hodge representation theorem for the control complex. -/
def hodgeControlRepresentation :
    CausalHodgeRepresentation
      hodgeControlData where

  harmonic_closed := by
    intro x hx
    exact hodgeControl_closed_all x

  closed_decompose := by
    intro z

    let e :
        hodgeControlComplex.Exact1 :=
      ⟨((z : ℚ × ℚ).1, 0),
        (hodgeControl_exact_iff
          ((z : ℚ × ℚ).1, 0)).2 rfl⟩

    let h :
        hodgeControlData.Harmonic1 :=
      ⟨(0, (z : ℚ × ℚ).2),
        (hodgeControl_harmonic_iff
          (0, (z : ℚ × ℚ).2)).2 rfl⟩

    refine ⟨e, h, ?_⟩
    ext <;> simp [e, h]

  exact_harmonic_disjoint := by
    apply Submodule.disjoint_def.mpr
    intro x hxExact hxHarm
    have hx2 :
        x.2 = 0 :=
      (hodgeControl_exact_iff x).1
        hxExact
    have hx1 :
        x.1 = 0 :=
      (hodgeControl_harmonic_iff x).1
        hxHarm
    ext <;> simp [hx1, hx2]

/-- Concrete Hodge theorem: vertical harmonic line is linearly equivalent to
the nontrivial H1 quotient. -/
noncomputable def hodgeControl_harmonicEquivH1 :
    hodgeControlData.Harmonic1 ≃ₗ[ℚ]
      hodgeControlComplex.H1 :=
  hodgeControlRepresentation.harmonicEquivH1

/-- The vertical unit cochain is a nonzero harmonic representative. -/
def hodgeControl_verticalHarmonic :
    hodgeControlData.Harmonic1 :=
  ⟨(0, 1),
    (hodgeControl_harmonic_iff
      (0, 1)).2 rfl⟩

theorem hodgeControl_verticalHarmonic_ne_zero :
    hodgeControl_verticalHarmonic ≠ 0 := by
  intro h
  have hs :=
    congrArg
      (fun x :
        hodgeControlData.Harmonic1 =>
        (x : ℚ × ℚ).2)
      h
  norm_num [
    hodgeControl_verticalHarmonic
  ] at hs

/-- Hence its H1 class is nonzero by injectivity of the Hodge equivalence. -/
theorem hodgeControl_nontrivial_H1 :
    hodgeControl_harmonicEquivH1
        hodgeControl_verticalHarmonic
      ≠
    0 := by
  intro h
  have hz :
      hodgeControl_verticalHarmonic =
        0 := by
    apply
      hodgeControl_harmonicEquivH1.injective
    simpa using h
  exact
    hodgeControl_verticalHarmonic_ne_zero
      hz

end CausalGeometry.Models
