import CausalGeometry.Completion.BruhatTitsConcreteIhara
import CausalGeometry.Completion.BruhatTitsArithmeticConcreteIhara
import CausalGeometry.Cyclic.IharaSignature

namespace CausalGeometry

universe u v g

/-- Stable provenance profile for a finite Ihara realization coming from a
prime-power Bruhat--Tits quotient.

Unlike FiniteIharaSignature, this retains the local arithmetic geometry
needed to interpret the transfer object:
- residue prime p;
- residue degree f;
- q=p^f;
- quotient vertex count;
- Hashimoto state and sparse-NNZ counts;
- the complete presentation-independent Ihara signature.

No graph labels, matrix basis, or quotient representatives are retained. -/
structure BruhatTitsIharaProfile where
  p : ℕ
  f : ℕ
  q : ℕ

  p_prime : p.Prime
  f_pos : 0 < f
  q_eq : q = p ^ f

  vertexCount : ℕ
  edgeCount : ℕ
  nnzCount : ℕ

  edgeCount_law :
    edgeCount =
      vertexCount * (q + 1)

  nnzCount_law :
    nnzCount =
      vertexCount * (q + 1) * q

  ihara : FiniteIharaSignature

  determinantNormalized :
    ihara.DeterminantNormalized

  satisfiesIhara :
    ihara.SatisfiesIhara
      determinantNormalized

namespace BruhatTitsIharaProfile

theorem q_ge_two
    (P : BruhatTitsIharaProfile) :
    2 ≤ P.q := by
  rw [P.q_eq]
  have hp : 2 ≤ P.p :=
    P.p_prime.two_le
  have hf : P.f ≠ 0 :=
    Nat.ne_of_gt P.f_pos
  exact hp.trans
    (Nat.le_pow hf)

/-- Hashimoto state count derived from the local profile. -/
theorem edgeCount_eq
    (P : BruhatTitsIharaProfile) :
    P.edgeCount =
      P.vertexCount * (P.q + 1) :=
  P.edgeCount_law

/-- Exact sparse NNZ count derived from the local profile. -/
theorem nnzCount_eq
    (P : BruhatTitsIharaProfile) :
    P.nnzCount =
      P.vertexCount *
        (P.q + 1) * P.q :=
  P.nnzCount_law

/-- Average number of nonzero transitions per Hashimoto state is exactly q
whenever the state set is nonempty. The division-free multiplicative law is
kept as the primary invariant. -/
theorem nnz_eq_edge_mul_q
    (P : BruhatTitsIharaProfile) :
    P.nnzCount =
      P.edgeCount * P.q := by
  rw [P.nnzCount_law,
    P.edgeCount_law]
  ac_rfl

/-- The stable determinant reciprocal attached to the profile. -/
def determinantZeta
    (P : BruhatTitsIharaProfile) :
    PowerSeries ℚ :=
  P.ihara.determinantReciprocal
    P.determinantNormalized

/-- The stable primitive Euler zeta attached to the same profile. -/
def primitiveZeta
    (P : BruhatTitsIharaProfile) :
    PowerSeries ℚ :=
  P.ihara.eulerZetaSeries

/-- Ihara equality is part of the proved profile, not a new target-specific
field. -/
theorem determinantZeta_eq_primitiveZeta
    (P : BruhatTitsIharaProfile) :
    P.determinantZeta =
      P.primitiveZeta :=
  P.satisfiesIhara

/-- Complete profile equality is determined by the actual stable data.
Proof fields are propositionally irrelevant. -/
theorem ext
    {P Q : BruhatTitsIharaProfile}
    (hp : P.p = Q.p)
    (hf : P.f = Q.f)
    (hq : P.q = Q.q)
    (hv : P.vertexCount = Q.vertexCount)
    (hi : P.ihara = Q.ihara) :
    P = Q := by
  cases P
  cases Q
  simp_all

end BruhatTitsIharaProfile

namespace BruhatTitsConcreteIhara

variable
    {A : ℕ → Type u}
    [∀ n, CommRing (A n)]
    [∀ n, IsLocalRing (A n)]
    [∀ n, Fintype (A n)]
    {T : PrimePowerLocalRingTower A}
    {B : BruhatTitsBranchingContract T}
    (I : BruhatTitsConcreteIhara.{u, v} B)

noncomputable local instance :
    Fintype I.quotient.QuotVertex :=
  I.quotient.vertexFintype

noncomputable local instance :
    DecidableEq I.quotient.QuotVertex :=
  I.quotient.vertexDecEq

noncomputable local instance :
    Fintype I.quotient.QuotEdge :=
  I.quotient.edgeFintype

noncomputable local instance :
    DecidableEq I.quotient.QuotEdge :=
  I.quotient.edgeDecEq

/-- Stable local/Ihara provenance extracted from a concrete finite
Bruhat--Tits quotient. -/
noncomputable def toProfile :
    BruhatTitsIharaProfile where
  p := T.p
  f := T.f
  q := T.q
  p_prime := T.p_prime
  f_pos := T.f_pos
  q_eq := rfl

  vertexCount :=
    Nat.card I.quotient.QuotVertex

  edgeCount :=
    Nat.card I.quotient.QuotEdge

  nnzCount :=
    Nat.card
      I.quotient.finiteSystem.HashimotoNonzero

  edgeCount_law :=
    I.hashimoto_state_natCard

  nnzCount_law :=
    I.hashimoto_nnz_natCard

  ihara :=
    FiniteIharaSignature.ofHashimoto
      I.primitiveComparison

  determinantNormalized :=
    FiniteIharaSignature.ofHashimoto_normalized
      I.primitiveComparison

  satisfiesIhara :=
    FiniteIharaSignature.ofHashimoto_satisfiesIhara
      I.primitiveComparison

@[simp] theorem toProfile_q :
    I.toProfile.q = T.q :=
  rfl

@[simp] theorem toProfile_vertexCount :
    I.toProfile.vertexCount =
      Nat.card I.quotient.QuotVertex :=
  rfl

@[simp] theorem toProfile_edgeCount :
    I.toProfile.edgeCount =
      Nat.card I.quotient.QuotEdge :=
  rfl

@[simp] theorem toProfile_nnzCount :
    I.toProfile.nnzCount =
      Nat.card
        I.quotient.finiteSystem.HashimotoNonzero :=
  rfl

end BruhatTitsConcreteIhara

/-- Arithmetic extension of the local Ihara profile.

Primitive integer multiplicities are now identified with actual finite
primitive conjugacy-class counts at each translation length. -/
structure ArithmeticBruhatTitsIharaProfile
    extends BruhatTitsIharaProfile where

  primitiveClassCount :
    ℕ → ℕ

  primitive_eq_classCount :
    ∀ n,
      toBruhatTitsIharaProfile.ihara
          .primitive.primitive n =
        (primitiveClassCount n : ℤ)

namespace ArithmeticBruhatTitsIharaProfile

/-- Arithmetic primitive multiplicities are nonnegative automatically. -/
theorem primitive_nonnegative
    (P : ArithmeticBruhatTitsIharaProfile)
    (n : ℕ) :
    0 ≤
      P.toBruhatTitsIharaProfile
        .ihara.primitive.primitive n := by
  rw [P.primitive_eq_classCount n]
  exact Int.natCast_nonneg _

/-- Primitive class count is determined by the stable integer primitive
signature. -/
theorem primitiveClassCount_eq_of_primitive_eq
    {P Q : ArithmeticBruhatTitsIharaProfile}
    (h :
      P.toBruhatTitsIharaProfile
          .ihara.primitive =
        Q.toBruhatTitsIharaProfile
          .ihara.primitive)
    (n : ℕ) :
    P.primitiveClassCount n =
      Q.primitiveClassCount n := by
  have hp :=
    P.primitive_eq_classCount n
  have hq :=
    Q.primitive_eq_classCount n
  have hi :
      P.toBruhatTitsIharaProfile.ihara
          .primitive.primitive n =
        Q.toBruhatTitsIharaProfile.ihara
          .primitive.primitive n := by
    rw [h]
  rw [hp, hq] at hi
  exact_mod_cast hi

end ArithmeticBruhatTitsIharaProfile

namespace BruhatTitsArithmeticConcreteIhara

variable
    {Γ : Type g} [Group Γ]
    {A : ℕ → Type u}
    [∀ n, CommRing (A n)]
    [∀ n, IsLocalRing (A n)]
    [∀ n, Fintype (A n)]
    {T : PrimePowerLocalRingTower A}
    {B : BruhatTitsBranchingContract T}
    [MulAction Γ
      (BruhatTitsUniversalGraph.Vertex
        (B := B))]
    [MulAction Γ
      (BruhatTitsUniversalGraph.OrientedEdge
        (B := B))]
    (I : BruhatTitsArithmeticConcreteIhara.{u, v, g}
      Γ B)

noncomputable local instance :
    Fintype
      I.arithmeticQuotient.quotient.QuotVertex :=
  I.arithmeticQuotient.quotient.vertexFintype

noncomputable local instance :
    DecidableEq
      I.arithmeticQuotient.quotient.QuotVertex :=
  I.arithmeticQuotient.quotient.vertexDecEq

noncomputable local instance :
    Fintype
      I.arithmeticQuotient.quotient.QuotEdge :=
  I.arithmeticQuotient.quotient.edgeFintype

noncomputable local instance :
    DecidableEq
      I.arithmeticQuotient.quotient.QuotEdge :=
  I.arithmeticQuotient.quotient.edgeDecEq

/-- Stable arithmetic/local/Ihara profile extracted from Γ\T. -/
noncomputable def toArithmeticProfile :
    ArithmeticBruhatTitsIharaProfile where
  toBruhatTitsIharaProfile :=
    I.toConcreteIhara.toProfile

  primitiveClassCount :=
    fun n =>
      Nat.card
        (I.conjugacyComparison.spectrum.Level n)

  primitive_eq_classCount :=
    I.primitive_eq_conjugacy_natCard

@[simp] theorem toArithmeticProfile_primitiveClassCount
    (n : ℕ) :
    I.toArithmeticProfile.primitiveClassCount n =
      Nat.card
        (I.conjugacyComparison.spectrum.Level n) :=
  rfl

end BruhatTitsArithmeticConcreteIhara
end CausalGeometry
