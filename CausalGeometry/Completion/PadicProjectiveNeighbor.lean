import CausalGeometry.Completion.LocalProjectiveCharts
import CausalGeometry.Completion.PadicLatticeIndex
import CausalGeometry.Completion.RankTwoLatticeStandard
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Tactic

namespace CausalGeometry

namespace PadicProjectiveNeighbor

open PadicLattice

variable (p : ℕ) [Fact p.Prime]

abbrev O := PadicLattice.O p
abbrev K := PadicLattice.K p
abbrev F := ZMod p
abbrev P1 :=
  LocalProjectivePair.Line (F p)

/-- Canonical two-chart coordinate of a projective residue point. -/
noncomputable def chart
    (q : P1 p) :
    LocalProjectivePair.Chart (F p) :=
  (LocalProjectivePair.chartEquiv
    (R := F p)).symm q

/-- Residual linear functional associated to one projective point.

For [1:t] we use (x,y) |-> y-tx.
For [u:1] we use (x,y) |-> x-uy.

The construction uses the canonical chart normal form, so it depends only on
the projective class, not on a chosen representative pair. -/
noncomputable def functional
    (q : P1 p) :
    (O p × O p) →+ F p := by
  classical
  cases hq : chart p q with
  | inl t =>
      exact
        { toFun := fun x =>
            residue p x.2 -
              t * residue p x.1
          map_zero' := by
            simp
          map_add' := by
            intro x y
            simp [mul_add]
            ring }
  | inr u =>
      exact
        { toFun := fun x =>
            residue p x.1 -
              u.1 * residue p x.2
          map_zero' := by
            simp
          map_add' := by
            intro x y
            simp [mul_add]
            ring }

/-- Every projective functional is onto: one coefficient is normalized to one
in the canonical chart. -/
theorem functional_surjective
    (q : P1 p) :
    Function.Surjective
      (functional p q) := by
  classical
  unfold functional
  split
  next t hq =>
    intro z
    rcases residue_surjective p z with
      ⟨a, ha⟩
    refine ⟨(0, a), ?_⟩
    simp [ha]
  next u hq =>
    intro z
    rcases residue_surjective p z with
      ⟨a, ha⟩
    refine ⟨(a, 0), ?_⟩
    simp [ha]

/-- The uniformizer p reduces to zero. -/
theorem residue_p_zero :
    residue p (p : O p) = 0 := by
  rw [← RingHom.mem_ker]
  rw [residue_kernel p]
  exact Ideal.mem_span_singleton_self _

/-- O-submodule of integral vectors whose residue lies on the chosen
projective line. -/
noncomputable def parameterSubmodule
    (q : P1 p) :
    Submodule (O p) (O p × O p) where
  carrier := {x | functional p q x = 0}
  zero_mem' := by
    simp [functional]
  add_mem' := by
    intro x y hx hy
    rw [map_add, hx, hy, add_zero]
  smul_mem' := by
    classical
    intro a x hx
    unfold functional at *
    split at hx ⊢
    next t hq =>
      change
        residue p (a * x.2) -
            t * residue p (a * x.1) =
          0
      rw [map_mul, map_mul]
      change
        residue p a * residue p x.2 -
            t * (residue p a * residue p x.1) =
          0
      have hx' :
          residue p x.2 =
            t * residue p x.1 := by
        exact sub_eq_zero.mp hx
      rw [hx']
      ring
    next u hq =>
      change
        residue p (a * x.1) -
            u.1 * residue p (a * x.2) =
          0
      rw [map_mul, map_mul]
      change
        residue p a * residue p x.1 -
            u.1 * (residue p a * residue p x.2) =
          0
      have hx' :
          residue p x.1 =
            u.1 * residue p x.2 := by
        exact sub_eq_zero.mp hx
      rw [hx']
      ring

@[simp] theorem mem_parameterSubmodule_iff
    (q : P1 p)
    (x : O p × O p) :
    x ∈ parameterSubmodule p q ↔
      functional p q x = 0 :=
  Iff.rfl

/-- Every p-multiple vector lies in every projective neighbor parameter
submodule. -/
theorem p_smul_mem_parameterSubmodule
    (q : P1 p)
    (x : O p × O p) :
    (p : O p) • x ∈
      parameterSubmodule p q := by
  classical
  unfold parameterSubmodule functional
  split
  next t hq =>
    simp [residue_p_zero p]
  next u hq =>
    simp [residue_p_zero p]

/-- The projective parameter submodule is finitely generated. -/
theorem parameterSubmodule_fg
    (q : P1 p) :
    (parameterSubmodule p q).FG := by
  exact
    Submodule.FG.of_le
      (Module.Finite.fg_top :
        (⊤ : Submodule
          (O p) (O p × O p)).FG)
      le_top

/-- Every non-unit of the residue field is zero. -/
theorem residue_nonunit_eq_zero
    (u : LocalProjectivePair.Nonunit (F p)) :
    u.1 = 0 := by
  by_contra h
  exact u.2
    (isUnit_iff_ne_zero.mpr h)

/-- Distinct projective points have distinct residual kernel submodules. -/
theorem parameterSubmodule_injective :
    Function.Injective
      (parameterSubmodule p) := by
  intro q r hqr
  apply
    (LocalProjectivePair.chartEquiv
      (R := F p)).symm.injective
  change chart p q = chart p r
  classical
  cases hq : chart p q with
  | inl tq =>
      cases hr : chart p r with
      | inl tr =>
          rcases residue_surjective p tq with
            ⟨a, ha⟩
          have hmemq :
              ((1 : O p), a) ∈
                parameterSubmodule p q := by
            unfold parameterSubmodule functional
            rw [hq]
            simp [ha]
          have hmemr :
              ((1 : O p), a) ∈
                parameterSubmodule p r := by
            rw [← hqr]
            exact hmemq
          unfold parameterSubmodule functional at hmemr
          rw [hr] at hmemr
          change
            residue p a -
                tr * residue p (1 : O p) =
              0 at hmemr
          simp [ha] at hmemr
          exact congrArg Sum.inl
            sub_eq_zero.mp hmemr
      | inr ur =>
          rcases residue_surjective p tq with
            ⟨a, ha⟩
          have hmemq :
              ((1 : O p), a) ∈
                parameterSubmodule p q := by
            unfold parameterSubmodule functional
            rw [hq]
            simp [ha]
          have hmemr :
              ((1 : O p), a) ∈
                parameterSubmodule p r := by
            rw [← hqr]
            exact hmemq
          unfold parameterSubmodule functional at hmemr
          rw [hr] at hmemr
          have hu0 :=
            residue_nonunit_eq_zero p ur
          simp [ha, hu0] at hmemr
  | inr uq =>
      cases hr : chart p r with
      | inl tr =>
          rcases residue_surjective p tr with
            ⟨a, ha⟩
          have hmemr :
              ((1 : O p), a) ∈
                parameterSubmodule p r := by
            unfold parameterSubmodule functional
            rw [hr]
            simp [ha]
          have hmemq :
              ((1 : O p), a) ∈
                parameterSubmodule p q := by
            rw [hqr]
            exact hmemr
          unfold parameterSubmodule functional at hmemq
          rw [hq] at hmemq
          have hu0 :=
            residue_nonunit_eq_zero p uq
          simp [ha, hu0] at hmemq
      | inr ur =>
          have huq :
              uq.1 = 0 :=
            residue_nonunit_eq_zero p uq
          have hur :
              ur.1 = 0 :=
            residue_nonunit_eq_zero p ur
          have huu : uq = ur := by
            apply Subtype.ext
            rw [huq, hur]
          exact congrArg Sum.inr huu

/-- Projective neighbor lattice inside Q_p^2. -/
noncomputable def lattice
    (q : P1 p) :
    RankTwoLattice (O p) (K p) where
  carrier :=
    (parameterSubmodule p q).map
      (diagonalMap p 0)
  fg :=
    (parameterSubmodule_fg p q).map
      (diagonalMap p 0)
  spans := by
    apply top_unique
    intro x hx
    rcases x with ⟨a, b⟩
    let e1 : K p × K p := (1, 0)
    let e2 : K p × K p := (0, 1)
    have hpK :
        (p : K p) ≠ 0 := by
      exact_mod_cast
        (Fact.out : Nat.Prime p).ne_zero
    have hp1 :
        (((p : K p), 0) : K p × K p) ∈
          (parameterSubmodule p q).map
            (diagonalMap p 0) := by
      refine
        ⟨((p : O p), 0),
          p_smul_mem_parameterSubmodule
            p q (1, 0),
          ?_⟩
      ext <;> simp [diagonalMap]
    have hp2 :
        ((0, (p : K p)) : K p × K p) ∈
          (parameterSubmodule p q).map
            (diagonalMap p 0) := by
      refine
        ⟨(0, (p : O p)),
          p_smul_mem_parameterSubmodule
            p q (0, 1),
          ?_⟩
      ext <;> simp [diagonalMap]
    have hs1 :
        e1 ∈
          Submodule.span (K p)
            ((parameterSubmodule p q).map
              (diagonalMap p 0) :
              Set (K p × K p)) := by
      have h :=
        Submodule.smul_mem
          (Submodule.span (K p)
            ((parameterSubmodule p q).map
              (diagonalMap p 0) :
              Set (K p × K p)))
          ((p : K p)⁻¹)
          (Submodule.subset_span hp1)
      simpa [e1, hpK] using h
    have hs2 :
        e2 ∈
          Submodule.span (K p)
            ((parameterSubmodule p q).map
              (diagonalMap p 0) :
              Set (K p × K p)) := by
      have h :=
        Submodule.smul_mem
          (Submodule.span (K p)
            ((parameterSubmodule p q).map
              (diagonalMap p 0) :
              Set (K p × K p)))
          ((p : K p)⁻¹)
          (Submodule.subset_span hp2)
      simpa [e2, hpK] using h
    have hdecomp :
        (a, b) =
          a • e1 + b • e2 := by
      ext <;> simp [e1, e2]
    rw [hdecomp]
    exact
      Submodule.add_mem _
        (Submodule.smul_mem _ a hs1)
        (Submodule.smul_mem _ b hs2)

/-- Distinct projective points give distinct ambient lattice representatives. -/
theorem lattice_injective :
    Function.Injective
      (lattice p) := by
  intro q r h
  apply parameterSubmodule_injective p
  ext x
  constructor
  · intro hx
    have hmapq :
        diagonalMap p 0 x ∈
          (lattice p q).carrier :=
      ⟨x, hx, rfl⟩
    rw [h] at hmapq
    rcases hmapq with
      ⟨y, hy, hxy⟩
    have hyx :
        y = x :=
      diagonalMap_injective p 0 hxy
    simpa [hyx] using hy
  · intro hx
    have hmapr :
        diagonalMap p 0 x ∈
          (lattice p r).carrier :=
      ⟨x, hx, rfl⟩
    rw [← h] at hmapr
    rcases hmapr with
      ⟨y, hy, hxy⟩
    have hyx :
        y = x :=
      diagonalMap_injective p 0 hxy
    simpa [hyx] using hy

/-- Every projective neighbor lies inside the standard lattice L_0. -/
theorem lattice_le_standard
    (q : P1 p) :
    (lattice p q).carrier ≤
      (diagonalLattice p 0).carrier := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact ⟨y, rfl⟩

/-- Neighbor as a submodule of the standard lattice. -/
noncomputable def insideStandard
    (q : P1 p) :
    Submodule (O p)
      (diagonalLattice p 0).carrier :=
  (lattice p q).carrier.submoduleOf
    (diagonalLattice p 0).carrier

/-- Residual functional on the standard lattice, obtained by recovering the
unique Z_p^2 parameter. -/
noncomputable def standardFunctional
    (q : P1 p) :
    (diagonalLattice p 0).carrier →+
      F p :=
  (functional p q).comp
    (parameterEquiv p 0).symm
      .toLinearMap.toAddMonoidHom

@[simp] theorem standardFunctional_parameter
    (q : P1 p)
    (x : O p × O p) :
    standardFunctional p q
        (parameterEquiv p 0 x) =
      functional p q x := by
  simp [standardFunctional]

theorem standardFunctional_surjective
    (q : P1 p) :
    Function.Surjective
      (standardFunctional p q) := by
  intro z
  rcases functional_surjective p q z with
    ⟨x, hx⟩
  refine
    ⟨parameterEquiv p 0 x, ?_⟩
  simpa using hx

/-- The kernel inside L_0 is exactly the projective neighbor. -/
theorem standardFunctional_ker
    (q : P1 p) :
    (standardFunctional p q).ker =
      (insideStandard p q).toAddSubgroup := by
  ext x
  constructor
  · intro hx
    rw [AddMonoidHom.mem_ker] at hx
    let y : O p × O p :=
      (parameterEquiv p 0).symm x
    have hy :
        y ∈ parameterSubmodule p q := by
      simpa [y, standardFunctional] using hx
    change
      x.1 ∈ (lattice p q).carrier
    refine
      ⟨y, hy, ?_⟩
    exact
      congrArg Subtype.val
        ((parameterEquiv p 0).apply_symm_apply x)
  · intro hx
    change
      x.1 ∈ (lattice p q).carrier at hx
    rcases hx with
      ⟨y, hy, hxy⟩
    apply AddMonoidHom.mem_ker.mpr
    have hparam :
        parameterEquiv p 0 y = x := by
      apply Subtype.ext
      exact hxy
    rw [← hparam]
    simpa [standardFunctional] using hy

/-- Quotient by a projective neighbor is canonically a residue-field-sized
quotient. -/
theorem quotient_natCard
    (q : P1 p) :
    Nat.card
        ((diagonalLattice p 0).carrier ⧸
          insideStandard p q) =
      p := by
  let f :=
    standardFunctional p q
  have hker :
      f.ker =
        (insideStandard p q).toAddSubgroup := by
    simpa [f] using
      standardFunctional_ker p q
  change
    Nat.card
      ((diagonalLattice p 0).carrier ⧸
        (insideStandard p q).toAddSubgroup) =
      p
  rw [← hker]
  rw [Nat.card_congr
    (QuotientAddGroup.quotientKerEquivRange f).toEquiv]
  have hrange :
      f.range = ⊤ :=
    AddMonoidHom.range_eq_top.mpr
      (standardFunctional_surjective p q)
  rw [hrange]
  simpa using residue_natCard p

/-- Every projective point therefore gives an actual p-index edge leaving the
standard lattice. -/
noncomputable def indexStep
    (q : P1 p) :
    RankTwoLattice.IndexStep p
      (diagonalLattice p 0)
      (lattice p q) where
  le :=
    lattice_le_standard p q
  quotient_card := by
    simpa [insideStandard] using
      quotient_natCard p q

/-- Projective points map to adjacent lattice homothety classes. -/
noncomputable def neighborClass
    (q : P1 p) :
    RankTwoLattice.HomothetyClass
      (O := O p) (K := K p) :=
  RankTwoLattice.classOf (lattice p q)

theorem neighborClass_adjacent_root
    (q : P1 p) :
    RankTwoLattice.ClassAdjacent
      (O := O p) (K := K p) p
      (RankTwoLattice.classOf
        (diagonalLattice p 0))
      (neighborClass p q) := by
  exact
    ⟨diagonalLattice p 0,
      lattice p q,
      rfl, rfl,
      Or.inl (indexStep p q)⟩

end PadicProjectiveNeighbor
end CausalGeometry
