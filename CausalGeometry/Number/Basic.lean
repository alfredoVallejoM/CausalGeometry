import CausalGeometry.Process.Diary

namespace CausalGeometry

universe u

/-- A causal number over boundary A is, at the primitive carrier level, an
endodiary. Admissibility and the selected equivalence are separate predicates,
not decorative fields. -/
abbrev CausalNumber (A : Type u) := EndDiary A

/-- Four comparison strata are kept distinct throughout the program. -/
inductive ComparisonLevel
  | strict
  | traceIso
  | effective
  | arithmeticShadow
  deriving DecidableEq, Repr

/-- A named semantic status for mathematical claims. -/
inductive ClaimStatus
  | definition
  | theoremTarget
  | realizationTarget
  | conditionalTarget
  | openResearch
  deriving DecidableEq, Repr

end CausalGeometry
