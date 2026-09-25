import CausalGeometry.Variational.JetCotangentLimit
import Mathlib.Tactic

namespace CausalGeometry.Models

/-- Constant identity tower used as a fully concrete jet/cotangent model. -/
def integerJetTower : JetRestrictionTower where
  Jet := fun _ => ℤ
  Restriction := fun _ => ℤ
  pair := fun _ => PairedTransform.identity ℤ
  jetTruncate := fun _ x => x
  restrictionTruncate := fun _ x => x

/-- Linear truncation agreeing with the structural identity truncation. -/
def integerJetLinearTruncation :
    JetCotangent.LinearTruncation
      integerJetTower ℤ where
  map := fun _ => LinearMap.id
  agrees := by
    intro n x
    rfl

/-- Identity prolongation is a section of identity truncation. -/
def integerJetProlongation :
    JetCotangent.Prolongation
      integerJetTower ℤ
      integerJetLinearTruncation where
  map := fun _ => LinearMap.id
  truncate_prolong := by
    intro n x
    rfl

/-- Standard identification of an integer restriction with the dual of the
rank-one integer jet. -/
def integerRestrictionDual :
    ℤ ≃ₗ[ℤ] Module.Dual ℤ ℤ :=
  (LinearMap.ringLmapEquivSelf ℤ ℤ ℤ).symm

/-- Concrete cotangent realization at every jet order. -/
def integerJetCotangentRealization :
    JetCotangent.Realization
      integerJetTower ℤ where
  form := fun _ =>
    integerRestrictionDual.toLinearMap
  restrictionDual := fun _ =>
    integerRestrictionDual
  forward_flat := by
    intro n x
    rfl

/-- The standard realization is musical: evaluation at one is sharp. -/
def integerJetMusicalRealization :
    JetCotangent.MusicalRealization
      integerJetTower ℤ where
  toRealization :=
    integerJetCotangentRealization
  sharp := fun _ =>
    LinearMap.ringLmapEquivSelf ℤ ℤ ℤ
  sharp_flat := by
    intro n x
    exact
      (LinearMap.ringLmapEquivSelf ℤ ℤ ℤ).apply_symm_apply x
  flat_sharp := by
    intro n ω
    exact
      (LinearMap.ringLmapEquivSelf ℤ ℤ ℤ).symm_apply_apply ω
  backward_sharp := by
    intro n r
    exact
      (LinearMap.ringLmapEquivSelf ℤ ℤ ℤ).apply_symm_apply r

theorem integerCotangentRestrictionCompatible :
    integerJetCotangentRealization.CotangentRestrictionCompatible
      integerJetLinearTruncation
      integerJetProlongation := by
  intro n r
  ext x
  simp [integerJetCotangentRealization,
    integerRestrictionDual,
    integerJetTower,
    integerJetProlongation,
    LinearMap.ringLmapEquivSelf_symm_apply]

theorem integerFlatTruncationCompatible :
    integerJetCotangentRealization.FlatTruncationCompatible
      integerJetLinearTruncation
      integerJetProlongation := by
  intro n x
  ext y
  simp [JetCotangent.Realization.flat,
    integerJetCotangentRealization,
    integerRestrictionDual,
    integerJetLinearTruncation,
    integerJetProlongation,
    LinearMap.ringLmapEquivSelf_symm_apply]

theorem integerSharpTruncationCompatible :
    integerJetMusicalRealization.SharpTruncationCompatible
      integerJetLinearTruncation
      integerJetProlongation := by
  intro n ω
  simp [JetCotangent.MusicalRealization.SharpTruncationCompatible,
    integerJetMusicalRealization,
    integerJetLinearTruncation,
    integerJetProlongation]

/-- Positive model: all structural tower compatibility is derived from the
cotangent/musical geometry. -/
theorem integerJetTower_compatible :
    integerJetTower.Compatible :=
  integerJetMusicalRealization.compatible_of_geometric
    integerJetLinearTruncation
    integerJetProlongation
    integerCotangentRestrictionCompatible
    integerFlatTruncationCompatible
    integerSharpTruncationCompatible

/-- And the inverse-limit structural pair is promoted to an actual
equivalence. -/
def integerJetLimitEquiv :
    integerJetTower.JetSection ≃
      integerJetTower.RestrictionSection :=
  integerJetMusicalRealization.limitEquiv
    integerJetLinearTruncation
    integerJetProlongation
    integerCotangentRestrictionCompatible
    integerFlatTruncationCompatible
    integerSharpTruncationCompatible

/-- Same types and same finite pair, but restriction truncation is negated. -/
def mutatedIntegerJetTower :
    JetRestrictionTower where
  Jet := fun _ => ℤ
  Restriction := fun _ => ℤ
  pair := fun _ => PairedTransform.identity ℤ
  jetTruncate := fun _ x => x
  restrictionTruncate := fun _ x => -x

def mutatedIntegerLinearTruncation :
    JetCotangent.LinearTruncation
      mutatedIntegerJetTower ℤ where
  map := fun _ => LinearMap.id
  agrees := by
    intro n x
    rfl

def mutatedIntegerProlongation :
    JetCotangent.Prolongation
      mutatedIntegerJetTower ℤ
      mutatedIntegerLinearTruncation where
  map := fun _ => LinearMap.id
  truncate_prolong := by
    intro n x
    rfl

def mutatedIntegerCotangentRealization :
    JetCotangent.Realization
      mutatedIntegerJetTower ℤ where
  form := fun _ =>
    integerRestrictionDual.toLinearMap
  restrictionDual := fun _ =>
    integerRestrictionDual
  forward_flat := by
    intro n x
    rfl

theorem mutatedIntegerFlatCompatible :
    mutatedIntegerCotangentRealization.FlatTruncationCompatible
      mutatedIntegerLinearTruncation
      mutatedIntegerProlongation := by
  intro n x
  ext y
  simp [JetCotangent.Realization.flat,
    mutatedIntegerCotangentRealization,
    integerRestrictionDual,
    mutatedIntegerLinearTruncation,
    mutatedIntegerProlongation,
    LinearMap.ringLmapEquivSelf_symm_apply]

/-- Same-type mutation: negating only restriction truncation destroys forward
tower compatibility. -/
theorem mutatedIntegerJetTower_not_forwardCompatible :
    ¬ mutatedIntegerJetTower.ForwardCompatible := by
  intro h
  have h1 := h 0 (1 : ℤ)
  norm_num [mutatedIntegerJetTower] at h1

/-- Therefore the mutated tower cannot satisfy the cotangent restriction
compatibility with the otherwise unchanged geometry. -/
theorem mutatedInteger_not_cotangentCompatible :
    ¬ mutatedIntegerCotangentRealization.CotangentRestrictionCompatible
        mutatedIntegerLinearTruncation
        mutatedIntegerProlongation := by
  intro hCot
  have hforward :=
    mutatedIntegerCotangentRealization.forwardCompatible_of_cotangent
      mutatedIntegerLinearTruncation
      mutatedIntegerProlongation
      hCot
      mutatedIntegerFlatCompatible
  exact mutatedIntegerJetTower_not_forwardCompatible
    hforward

end CausalGeometry.Models
