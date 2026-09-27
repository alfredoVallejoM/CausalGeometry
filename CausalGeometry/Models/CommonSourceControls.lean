import CausalGeometry.Number.Basic
import CausalGeometry.Realization.IndexedFamily

namespace CausalGeometry
namespace Models
namespace CommonSourceControls

/-- Empty primitive event system used as one causal-source witness. -/
def emptySystem :
    EventSystem PEmpty PUnit where
  precedes := fun _ _ => False
  conflict := fun _ _ => False
  label := fun e => nomatch e
  precedes_irrefl := by
    intro e
    exact nomatch e
  precedes_trans := by
    intro e
    exact nomatch e
  conflict_symm := by
    intro e
    exact nomatch e
  conflict_irrefl := by
    intro e
    exact nomatch e
  conflict_future := by
    intro e
    exact nomatch e

/-- A causal number with no primitive events. -/
def emptyCausalNumber :
    CausalNumber Unit where
  Event := PEmpty
  Label := PUnit
  system := emptySystem
  inputSupport := fun _ => ∅
  outputSupport := fun _ => ∅

/-- One-event primitive system with no causal or conflict edges. -/
def singletonSystem :
    EventSystem PUnit PUnit where
  precedes := fun _ _ => False
  conflict := fun _ _ => False
  label := fun _ => PUnit.unit
  precedes_irrefl := by
    intro e h
    exact h
  precedes_trans := by
    intro e f g hef
    exact False.elim hef
  conflict_symm := by
    intro e f hef
    exact False.elim hef
  conflict_irrefl := by
    intro e h
    exact h
  conflict_future := by
    intro e f g hef
    exact False.elim hef

/-- A causal number with one independent primitive event. -/
def singletonCausalNumber :
    CausalNumber Unit where
  Event := PUnit
  Label := PUnit
  system := singletonSystem
  inputSupport := fun _ => ∅
  outputSupport := fun _ => ∅

/-- The two source witnesses are genuinely distinct before any realization. -/
theorem empty_ne_singleton :
    emptyCausalNumber ≠
      singletonCausalNumber := by
  intro h
  have hnonempty :
      Nonempty emptyCausalNumber.Event := by
    rw [h]
    exact ⟨PUnit.unit⟩
  exact hnonempty.elim

/-- Named two-point source domain for downstream common-source realization
controls. -/
def TwoSourceDomain
    (X : CausalNumber Unit) : Prop :=
  X = emptyCausalNumber ∨
    X = singletonCausalNumber

theorem empty_mem_twoSourceDomain :
    TwoSourceDomain emptyCausalNumber :=
  Or.inl rfl

theorem singleton_mem_twoSourceDomain :
    TwoSourceDomain singletonCausalNumber :=
  Or.inr rfl

/-- The named two-source causal domain as an actual source type. -/
abbrev TwoSource :=
  {X : CausalNumber Unit // TwoSourceDomain X}

/-- Canonical empty source in the named domain. -/
def emptySource : TwoSource :=
  ⟨emptyCausalNumber, empty_mem_twoSourceDomain⟩

/-- Canonical singleton source in the named domain. -/
def singletonSource : TwoSource :=
  ⟨singletonCausalNumber, singleton_mem_twoSourceDomain⟩

/-- A Boolean tag that exactly distinguishes the two admitted causal
sources. -/
noncomputable def sourceTag
    (X : TwoSource) : Bool :=
  if X.1 = emptyCausalNumber
  then false
  else true

theorem sourceTag_empty :
    sourceTag emptySource = false := by
  simp [sourceTag, emptySource]

theorem sourceTag_singleton :
    sourceTag singletonSource = true := by
  simp [
    sourceTag,
    singletonSource,
    empty_ne_singleton
  ]

/-- On the named two-source domain the tag is injective. -/
theorem sourceTag_injective :
    Function.Injective sourceTag := by
  rintro ⟨X, hX⟩ ⟨Y, hY⟩ htag
  apply Subtype.ext
  rcases hX with hX | hX
  · rcases hY with hY | hY
    · simpa [hX, hY]
    · subst X
      subst Y
      have :
          (false : Bool) = true := by
        simpa [
          sourceTag,
          emptySource,
          singletonSource,
          empty_ne_singleton
        ] using htag
      cases this
  · rcases hY with hY | hY
    · subst X
      subst Y
      have :
          (true : Bool) = false := by
        simpa [
          sourceTag,
          emptySource,
          singletonSource,
          empty_ne_singleton
        ] using htag
      cases this
    · simpa [hX, hY]

/-- Two-place family on actual causal numbers.

The false place records the distinguishing causal-source tag while the true
place is deliberately neutral.  This is a minimal common-source
local-to-global control rather than an elliptic realization. -/
noncomputable def causalCoordinateFamily :
    IndexedRealizationFamily
      TwoSource Bool where
  Target := fun _ => Bool
  realize :=
    fun place source =>
      if place then false
      else sourceTag source

/-- Agreement at every place reconstructs the admitted causal source. -/
theorem causalCoordinateFamily_jointlyConservative :
    causalCoordinateFamily.JointlyConservative := by
  intro X Y h
  apply sourceTag_injective
  have hfalse := h false
  simpa [
    IndexedRealizationFamily.CollapsesAt,
    causalCoordinateFamily
  ] using hfalse

/-- Mutation erasing the only informative local coordinate. -/
def collapsedCausalFamily :
    IndexedRealizationFamily
      TwoSource Bool where
  Target := fun _ => Bool
  realize := fun _ _ => false

/-- The collapsed family cannot reconstruct the two distinct causal
sources. -/
theorem collapsedCausalFamily_not_jointlyConservative :
    ¬ collapsedCausalFamily.JointlyConservative := by
  intro h
  have hEq :
      emptySource = singletonSource := by
    apply h
    intro place
    rfl
  have hVal :
      emptyCausalNumber =
        singletonCausalNumber :=
    congrArg Subtype.val hEq
  exact empty_ne_singleton hVal

/-- Positive/negative joint-conservativity discriminator on a named
`CausalNumber` domain. -/
theorem causal_joint_conservativity_discriminator :
    causalCoordinateFamily.JointlyConservative ∧
      ¬ collapsedCausalFamily.JointlyConservative :=
  ⟨causalCoordinateFamily_jointlyConservative,
    collapsedCausalFamily_not_jointlyConservative⟩

end CommonSourceControls
end Models
end CausalGeometry
