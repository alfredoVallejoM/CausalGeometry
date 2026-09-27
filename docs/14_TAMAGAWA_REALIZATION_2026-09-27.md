# ECIA / CA-24 Tamagawa realization status — 2026-09-27

This note records the Tamagawa continuation of the ECIA realization campaign.
It advances CA-19.30, CA-20.28, CA-24.39 and the Tamagawa part of T152 without
declaring any of them fully closed.

Source code SHA for the new causal contract:

- `6835e4557c68bf51b102868d4b16e6784f10e40d`

Downstream GenContinuum bridge code SHA:

- `5cb50ca45cf2662cb05b4eb3ede66a0ef537ac05`
- branch: `codex/ecia-continuation`
- file: `GenContinuum/ECIA/CausalBridge/Tamagawa.lean`
- concrete elliptic consumers: `GenContinuum/ECIA/CausalBridge/TamagawaEllipticCases.lean`
- consumer commit: `a94cbf0287211bd15cf576a0c61cfa13c6c7a4d4`

The downstream branch is pinned to the source SHA above.

## 1. Structural choice

Tamagawa is not a primitive field of a causal number.

For a local realization one first constructs a finite component quotient

[
P_v longrightarrow Phi_v,
]

where (P_v) is the chosen local point carrier and (Phi_v) is the finite
component carrier.  The local Tamagawa index is then derived:

[
c_v := #Phi_v.
]

The source implementation is

- `CausalGeometry/Realization/ECIATamagawaContract.lean`;
- `Tamagawa.LocalComponentQuotient`;
- `Tamagawa.LocalComponentQuotient.tamagawaIndex`.

The quotient map is required to be surjective and the component carrier is
required to be nonempty.  Hence the source derives

[
c_v>0
quad	ext{and}quad
c_v
eq0.
]

No unrelated natural number can be supplied as the Tamagawa factor.

The source quotient deliberately stores no extra pointed/group structure.
Identity preservation belongs to a concrete group-theoretic target.  This
keeps the causal source weaker than Neron geometry and prevents a parallel
Neron theory from entering CausalGeometry.

## 2. Finite-support global product

For a place type (V), a Tamagawa family contains

[
(P_v 	woheadrightarrow Phi_v)_{vin V},
]

a finite support (Ssubset V), and the proof

[
v
otin S Longrightarrow c_v=1.
]

The derived global finite product is

[
C_{mathrm{Tam}}=prod_{vin S} c_v.
]

This is implemented by

- `Tamagawa.Family`;
- `Tamagawa.Family.globalTamagawaIndex`.

It is only the Tamagawa factor/product.  It is not a BSD formula.

## 3. Strong and weak preservation

The ECIA realization contract distinguishes two levels.

Strong preservation requires an equivalence of component carriers at every
place together with equality of finite support:

[
Phi^{mathrm{src}}_v simeq
Phi^{mathrm{tgt}}_v.
]

From this the source proves equality of every (c_v) and equality of global
Tamagawa products.

Weak preservation records only equality of the natural-number indices.

The implication

[
	ext{component preservation}
Longrightarrow
	ext{index preservation}
]

is proved, but the converse is intentionally absent.  Equal cardinalities do
not identify component quotients.

## 4. Neron realization in GenContinuum

The existing GenContinuum elliptic layer already provides the target
mathematics that must not be reimplemented:

- genuine `ComponentQuotient` of an actual special-fiber group scheme;
- finite etale component group;
- rational-point carrier;
- `tamagawaNumber C = Nat.card (RationalPoints C.componentGroup)`;
- invariance under the component-quotient certificate;
- invariance under the chosen Neron model;
- connected-fiber factor (1);
- split multiplicative cyclic component groups;
- finite Tamagawa products for the BSD consumer.

The new bridge therefore identifies the causal component carrier with

[
Phi_v(k_v)
=
operatorname{RationalPoints}(C_v.mathrm{componentGroup}),
]

and proves definitionally

[
c_v^{mathrm{causal}}
=
c_v^{mathrm{Neron}}.
]

No second component group, Neron model or Tamagawa function is introduced.

## 5. Actual rational-point descent

The bridge now separates the carrier comparison from a stronger geometric
step.

For a genuine special-fiber group (G_v) and component quotient (C_v), it
constructs the induced map

[
G_v(k_v)
longrightarrow
Phi_v(k_v)
]

from the native group-scheme projection.

The proposition

[
mathrm{RationalPointComponentDescent}(C_v)
]

is exactly the surjectivity of this map.

Only after a concrete target proves that surjectivity does the bridge build a
`LocalComponentQuotient` whose point carrier is the actual special-fiber
rational-point type.

This obligation is deliberately exposed.  It is not inferred from a Kodaira
label, residue cardinal, point count or Bruhat--Tits skeleton.

For a full local elliptic realization one must still connect the generic local
elliptic points/Neron integral points to this special-fiber reduction map under
the appropriate local hypotheses.

## 6. Good reduction

The source proves the generic structural statement

[
Phi_v simeq 1
Longrightarrow
c_v=1.
]

GenContinuum already proves the corresponding target theorem for a
geometrically connected special fiber.

The downstream bridge consumes that theorem and obtains the same value for
the causal component shadow.

This is a comparison theorem, not a declaration that every supported source
object has good reduction.

## 7. Split multiplicative Tate type I_n

The source comparison is deliberately cyclic:

[
Phi_v simeq
operatorname{Multiplicative}(mathbf Z/nmathbf Z).
]

Using the native cardinal theorem for `ZMod n`, it derives

[
c_v=n.
]

This matches the existing GenContinuum reduction bridge, whose hypothesis is
an equivalence

[
Phi_v(k_v)
simeq
operatorname{Multiplicative}(mathbf Z/nmathbf Z).
]

The new downstream adapter consumes that equivalence directly.  It does not
insert an artificial `Fin n` layer.

The already existing explicit split-multiplicative component quotient also
gives the regression

[
c_v=n.
]

What remains for a general local elliptic object is the geometric theorem
identifying the actual Neron special fiber/component quotient with the
appropriate type-(I_n) target.

## 7.1 Concrete additive consumer

The downstream optional consumer now also applies the generic bridge to the
existing unconditional additive 5-adic Neron model.

For that actual special fiber it consumes the previously proved target result

[
c_v=1
]

and derives the same causal Tamagawa factor.  It also transports the existing
negative control excluding a cyclic type-(I_3) component description.

This is a concrete additive example, not a general theorem that all additive
reduction has Tamagawa factor one.  The general additive and nonsplit
classification remains open.

## 8. Adversarial loss control

`CausalGeometry/Models/TamagawaControls.lean` contains two quotients with
the same local point carrier `Bool`:

- collapsed components: (c=1);
- separated components: (c=2).

Therefore the source proves that local point count alone does not determine
Tamagawa.

This blocks a false route of the form

[
#P_v ightsquigarrow c_v
]

without a component-quotient theorem.

The GenContinuum BSD layer independently contains a skeleton-only mutation and
forces a sound connected singleton factor to be (1).

## 9. Current obligation matrix

| ID | Obligation | Status |
|---|---|---|
| TAM-01 | Structural finite nonempty component quotient, derived local index and positivity. | SOURCE IMPLEMENTED |
| TAM-02 | Finite support and derived global product. | SOURCE IMPLEMENTED |
| TAM-03 | Good-reduction structural control and same-point-count mutation. | SOURCE IMPLEMENTED |
| TAM-04 | Cyclic Tate (I_n) comparison deriving (c_v=n). | SOURCE IMPLEMENTED |
| TAM-05 | Native Neron component carrier -> causal component shadow. | DOWNSTREAM IMPLEMENTED / TYPECHECK PENDING |
| TAM-06 | Native Tamagawa number = causal local index. | DOWNSTREAM IMPLEMENTED / TYPECHECK PENDING |
| TAM-07 | Native special-fiber rational point -> component map with explicit surjectivity obligation. | DOWNSTREAM IMPLEMENTED / SURJECTIVITY DOMAIN-SPECIFIC |
| TAM-08 | Causal finite product = existing geometric BSD-layer Tamagawa product; certificate independence. | DOWNSTREAM IMPLEMENTED / TYPECHECK PENDING |
| TAM-09 | Named causal-number source family -> local elliptic/Neron targets. | PARTIAL — generic common-source infrastructure and real two-source control implemented; intrinsic arithmetic realization from causal numbers remains OPEN. |
| TAM-10 | Generic local elliptic/Neron integral points -> special-fiber component descent under exact local hypotheses. | PARTIAL — generic→integral→special-fiber→component chain implemented; identity-base full control and connected component descent proved; nontrivial DVR integral-reduction surjectivity remains OPEN. |
| TAM-11 | Reduction-type consumers beyond good/split: concrete effective additive model is bridged with c_v=1 and a false I_3 mutation rejected; general additive/nonsplit classification remains open. | PARTIAL / TYPECHECK PENDING |
| TAM-12 | Insert the certified Tamagawa product into a full BSD determinant/regulator/Sha comparison theorem. | OPEN |

The absence of a local Lean/lake toolchain in the current execution
environment leaves TAM-05--08 at static-audit/typecheck-pending status.

## 10. Consequence for CA-24.39 and T152

CA-24.39 is now **IN PROGRESS** rather than merely planned:

[
	ext{causal component contract}
	o
	ext{native Neron quotient}
	o
c_v
	o
prod_v c_v
]

has an explicit implementation route.

It is not closed because the campaign still lacks the named causal-number
elliptic source family and the full generic-point/Neron/special-fiber descent
theorem.

The Tamagawa segment of T152 is correspondingly advanced, but T152 remains
open because its common elliptic source must still integrate Frobenius/Galois,
q-adic/Bruhat--Tits, modular/Hecke, dessins, Mordell--Weil/height,
Selmer/Sha, Iwasawa, Gross--Zagier and the BSD determinant-line routes.

## 11. BSD firewall

Nothing in this change proves BSD.

In particular it does not prove

- analytic rank = Mordell--Weil rank;
- finiteness or order of Sha;
- a regulator formula;
- a period formula;
- the leading-term equality;
- the determinant-line comparison needed by the intended ECIA BSD route.

The gain is narrower and necessary: the Tamagawa term is now a typed,
structural, loss-audited realization attached to actual component quotients
instead of a free numerical parameter.


## 12. Common-source indexed realization layer

CausalGeometry now contains a general `IndexedRealizationFamily`.

For a single source object (X) and a place (v), it stores a typed local
realization (R_v(X)).  The entire dependent packet

[
v \mapsto R_v(X)
]

therefore has one explicit provenance.

The layer also defines:

- placewise collapse;
- collapse at every place;
- placewise comparison of realization families;
- monotonicity of information loss under such comparisons;
- `JointlyConservative`, kept as a theorem-level property rather than
  inferred from the existence of many localizations.

The positive control observes two independent coordinates at two places and
is jointly conservative.  A mutation observing the first coordinate at both
places is not.

Tamagawa families now expose both:

[
X \mapsto (P_v(X) \twoheadrightarrow \Phi_v(X))
]

and the further numerical shadow

[
X \mapsto c_v(X).
]

There is a typed comparison from the structural datum to the numerical index.

## 13. Generic-to-component theorem chain

The downstream ECIA consumer now formalizes

[
E(K_v)
\longrightarrow
\mathcal N(\mathcal O_v)
\longrightarrow
\mathcal N_{k_v}(k_v)
\longrightarrow
\Phi_v(k_v).
]

The first arrow is represented by the inverse of the Neron restriction
bijection supplied by the mapping property.

The second is the actual base-change reduction of an integral section.

The third is the native universal component projection.

The only additional local theorem lock is

`IntegralReductionSurjective`:

every special-fiber rational point is the reduction of an integral Neron
section.

Together with rational-point component descent, this proves that the complete
generic-to-component map is surjective.  The resulting generic-point quotient
has Tamagawa index definitionally equal to the native Neron Tamagawa number.

## 14. Common-source Neron/Tamagawa family

GenContinuum now contains `CommonSourceFamily` and
`GenericDescentFamily`.

A `CommonSourceFamily` requires every local place of one admitted source to
carry:

- an actual base;
- a generic base;
- a residue base;
- an actual Neron model;
- its actual special fiber;
- a universal component quotient;
- rational-point component descent.

The forgetful chain is typed:

[
\text{Neron packet}
\longrightarrow
\text{structural Tamagawa datum}
\longrightarrow
c_v.
]

For one common source, the global causal product is proved equal to the
existing BSD-layer `componentTamagawaProduct`.

A `GenericDescentFamily` additionally carries the integral-reduction
surjectivity at every place and upgrades the local point carrier from the
special fiber to the genuine generic-point carrier.

## 15. New positive and loss controls

The identity-base elliptic Neron model supplies a complete positive
generic-descent control: pullback along identity gives surjective reduction,
the connected component quotient gives surjective component descent, and the
generic-point quotient has (c_v=1).

A separate two-source control sends two genuinely distinct causal numbers to
two genuine elliptic/Neron constructions:

- an identity-base good-reduction elliptic model;
- the existing unconditional additive 5-adic Neron model.

Both give (c_v=1).  Hence numerical Tamagawa is proved non-conservative on
that named causal control domain.

This does not claim that those elliptic curves are intrinsically reconstructed
from the two causal numbers; it certifies non-vacuity and information loss of
the interface.

## 16. Refined frontier

The principal remaining local theorem is no longer component descent for
connected fibers.  That is closed.

The nontrivial arithmetic frontier is now:

[
\mathcal N(\mathcal O_v)
\twoheadrightarrow
\mathcal N_{k_v}(k_v)
]

for the intended nontrivial DVR/Henselian local models.

GenContinuum already contains finite-level good-reduction transition
surjectivity and independent Hensel/completion machinery, but these have not
yet been identified with the Neron integral-section reduction map.  That
comparison remains an explicit theorem obligation.
