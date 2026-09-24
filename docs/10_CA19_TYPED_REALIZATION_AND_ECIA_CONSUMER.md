# CA-19 typed realizations and the ECIA consumer boundary

Snapshot: 2026-09-24

## 1. Purpose

CausalGeometry is upstream of ECIA. The source repository must therefore expose
a typed realization boundary that GenContinuum/ECIA can consume without turning
ECIA into a dependency of the causal kernel.

The source direction is

[
X in CNum(A)
longmapsto
R(X)
]

with the concrete target supplied downstream.

No theorem in this layer asserts essential surjectivity of ECIA structural
numbers back to causal numbers.

## 2. Real(X)

Realization/At.lean introduces RealizationAt X.

A RealizationAt X retains the complete realization map

[
R : alpha 	o Target_R
]

and distinguishes its value at the fixed source object X.

A RealizationAtHom between two realizations at the same X contains a typed map

[
eta_{R,S}:Target_R	o Target_S
]

and a commuting law at X.

Identity and composition are implemented. A global AnyRealization.Comparison
restricts canonically to a comparison at X.

This is the source-side categorical skeleton required by CA-19.01 and CA-19.02.

## 3. Comparison classification

ComparisonKind separates:

- equivalence;
- quotient/information loss;
- completion;
- localization;
- analytic upgrade;
- conditional bridge.

The existence of a comparison map does not determine its semantic class.
Classification is explicit data through ClassifiedRealizationAtHom.

This implements the typing discipline of CA-19.03 without claiming that every
target bridge already exists.

## 4. ECIA consumer contract

Realization/ECIAContract.lean defines a source-side ECIAStructuralTarget and an
ECIARealization.

The adapter takes:

- a causal source boundary A;
- an explicit source admissibility predicate on CausalNumber A;
- a downstream target carrier;
- a downstream target admissibility predicate;
- a realization map;
- a soundness theorem preserving admissibility.

The causal kernel does not import GenContinuum or ECIA.

The contract intentionally does not bundle arithmetic shadow, dagger, cyclic
shadow, composition, Morita data or analytic structure into one record.
Each preservation statement is a separate comparison theorem.

ECIAObservableCompatibility is the first generic preservation interface.

## 5. What is and is not closed

Source implementation now exists for the categorical skeleton behind:

- CA-19.01;
- CA-19.02;
- CA-19.03;
- the source-side adapter boundary needed by CA-19.17.

CA-19.17 itself is not closed until the real ECIA target implements the
contract and its preservation theorems are checked.

No CA-19 row is campaign-accredited until Lean compilation plus the full
positive/control/mutation/consumer/adversarial/import/resource closure contract
has been run.

## 6. Causal-calculus correction discovered adversarially

The 2026-09-24 adversarial review found that ConcurrentAt previously admitted
e = f. That made a nominal concurrency diamond capable of using the same event
twice even though the first execution disables the second.

The source definition now requires e != f and proves that two distinct enabled
compatible events remain enabled after executing the other one.

ConcurrencyDiamond now derives intermediate and terminal configurations from
the concurrency proof instead of storing freely overridable endpoint fields.

Calculus/IteratedDifference.lean adds:

- causalSquareVariation;
- causalOrderCurvature;
- vanishing of order curvature on a genuine flat concurrency diamond.

This is the first source-level reinforcement of the calculus described in the
formal specification beyond the original first finite difference.

## 7. Remaining implementation order

The next source layers should proceed in this order.

1. Causal calculus closure:
   iterated path differences, vertical/horizontal/restriction decomposition,
   connection data, curvature outside flat concurrency squares, and a typed
   Bianchi target under explicit hypotheses.

2. CA-18 localization:
   commutative localization first, then left/right Ore sectors without
   identifying residual division with inversion.

3. CA-18 local reconstruction:
   q = p^f residue towers, complete DVR comparison, valuation-colored graph
   towers and then the Bruhat-Tits boundary.

4. CA-19 concrete source realizations:
   graph/Ihara, Wilderber restriction, local/Tate/adelic and finite-field
   point-count/Frobenius adapters.

5. ECIA downstream adapter:
   instantiate ECIARealization in the ECIA/GenContinuum repository and prove
   admissibility, composition, dagger, cyclic-shadow and arithmetic-shadow
   compatibility independently.

6. CA-20:
   remain a theorem-indexed transformation program. RH, BSD and general
   Langlands are not promoted by source architecture alone.
