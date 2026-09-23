# Formal specification of causal geometry and causal arithmetic

## 0. Thesis

The generative chain is

\[
\text{events}\to\text{histories}\to\text{bounded diaries}
\to\text{causal numbers}\to\text{typed realizations}
\to\text{ECIA structural numbers}\to\text{classical shadows}.
\]

The central object is not an integer carrying metadata. A causal number over a
boundary \(A\) is an admissible endodiary

\[
X:A\rightsquigarrow A.
\]

A classical number is obtained by forgetting causal structure.

## 1. Event systems

A causal event system is
\[
\mathcal E=(E,\prec,\#,\lambda)
\]
with strict causality, conflict and labels. The laws are irreflexivity and
transitivity of \(\prec\), symmetry and irreflexivity of conflict, plus
hereditary propagation of conflict toward causal futures.

A configuration \(C\subseteq E\) is downward closed and conflict free.
An event is enabled when its causal predecessors are already present and it is
compatible with the current history. Two enabled events are concurrent when
neither precedes the other and they do not conflict.

## 2. Histories

A finite execution is
\[
C_0\xrightarrow{e_1}C_1\to\cdots\to C_n.
\]

Concurrent adjacent events generate swaps
\[
uefv\sim ufev.
\]

The program keeps four objects distinct:
1. execution word;
2. trace class;
3. partial-order history;
4. the 2-cell witnessing exchange.

Completed histories are modeled by directed/ideal completion of finite
configurations where the corresponding hypotheses are available.

## 3. Bounded causal diaries

A diary has typed interfaces
\[
D:A\rightsquigarrow B.
\]

Compatible diaries glue sequentially. Sequential composition is weakly
associative with an explicit associator and unitors. Parallel composition is
a different operation and is never identified with sequential composition.

## 4. Dagger and closure

A causal dagger reverses interfaces and the selected process structure:
\[
(Y\circ X)^\dagger\simeq X^\dagger\circ Y^\dagger,
\qquad
(X^\dagger)^\dagger\simeq X.
\]

Closure of an endodiary gives a cyclic object. The required law is cyclicity
\[
Sh(XY)\simeq Sh(YX),
\]
not commutativity \(XY=YX\).

## 5. Causal numbers

\[
CNum(A)=End_{\mathbf{Cau}}(A).
\]

Multiplication is sequential composition. Equality is stratified:
- strict equality;
- trace/isomorphism;
- effective/Morita-style equivalence;
- equality of arithmetic shadow.

The program fixes which level each theorem uses; proofs may not switch levels
opportunistically.

## 6. Arithmetic shadow

On an arithmetic subdomain:
\[
\nu:CNum(A)\to\bigoplus_p\mathbb N[p],
\qquad
\nu(XY)=\nu(X)+\nu(Y).
\]

Define
\[
\chi(X)=\prod_p p^{\nu_p(X)}.
\]

Then
\[
\chi(XY)=\chi(X)\chi(Y).
\]

A natural lift
\[
\iota:\mathbb N_{>0}\to CNum(A)
\]
must satisfy
\[
\chi(\iota(n))=n.
\]

The fiber
\[
\mathcal N_n=\{X:\chi(X)=n\}
\]
is structural information invisible to the integer. A key discriminant is
the existence of \(X\not\simeq Y\) with \(\chi(X)=\chi(Y)\).

## 7. Intrinsic arithmetic

Left and right causal divisibility are separated in noncommutative domains.
Primality is defined through causal factorization, not by primitive cyclicity.
GCD and LCM are universal objects when the relevant divisor category admits
them.

Addition is introduced by an additive envelope; signed objects use a
Grothendieck completion when justified. Fractions are constructed only under
commutative or left/right Ore hypotheses.

## 8. Valuations, scales and length

Prime valuations live on the proved arithmetic fraction sector:
\[
v_p(XY)=v_p(X)+v_p(Y).
\]

The integral scale tower is indexed by \(\mathbb Z\). Dagger, arithmetic
inverse, sign reversal in scale, Pontryagin duality and modular inversion are
different operations until comparison theorems identify their images.

Arithmetic length is
\[
L_{arith}(X)=\log|\chi(X)|
\]
on the positive nonzero sector, hence additive under multiplication.

## 9. Cyclic geometry

Closed histories carry periods and primitive decompositions where proved. A
finite transfer realization may give
\[
\log Z_C(u)=\sum_{n\ge1}\frac{Tr(T^n)}n u^n
\]
and
\[
Z_C(u)=\det(I-uT)^{-1}
\]
in the finite matrix domain.

Analytic continuation, nuclearity, Fredholm determinants and identification
with completed arithmetic zetas are separate layers.

## 10. Causal calculus

For an observable \(F\) and enabled event \(e\):
\[
\Delta_eF(H)=F(H+e)-F(H).
\]

The broader calculus keeps the developed decomposition
\[
D=d_v+d_h+d_\mu.
\]

Flat concurrency diamonds support a square-zero differential in the appropriate
complex. Connections may have curvature
\[
\Omega=\nabla^2,
\]
with a Bianchi-type law. Higher iterates may encode compositional content,
order sensitivity or curvature; they are not normatively called errors.

## 11. Quotients and residual classes

Given
\[
M=k[Hist(D)],\quad S:M\to F,\quad \rho:R\to M,\quad S\rho=0,
\]
define
\[
Q=M/\operatorname{im}\rho,
\qquad
\mathfrak R=\ker S/\operatorname{im}\rho.
\]

Under exactness hypotheses,
\[
\mathfrak R=0\iff\operatorname{im}\rho=\ker S.
\]

This is the generic source for local/global and compatibility classes; any
identification with classical Selmer, Sha, cohomology or obstruction theories
requires a target theorem.

## 12. Predictive memory and renormalization

For a fixed future-observer family \(\Omega\),
\[
H_1\sim_\Omega H_2
\]
when no admitted future continuation/observer separates the histories.

\[
Q_\Omega=Hist(D)/{\sim_\Omega}
\]
is the effective causal memory. A directed family of such quotients gives a
causal coarse-graining/renormalization system.

## 13. Realizations

A realization
\[
R:\mathcal C\to\mathcal D
\]
creates an indistinguishability relation
\[
X\sim_RY\iff R(X)\simeq R(Y).
\]

Each mature bridge must state preservation, information loss, comparison with
other realizations and scope.

## 14. ECIA bridge

The main target is a pseudofunctor
\[
R_{ECIA}:\mathbf{Cau}\to\mathbf{ECIA}_{corr}
\]
preserving unit, composition, dagger and cyclic shadow on its declared domain.

Soundness:
\[
X\in CNum(A)\Rightarrow R_{ECIA}(X)
\text{ is an ECIA structural number}.
\]

Essential surjectivity is a stronger independent problem.

## 15. Universal restriction geometry

For a geometric/polynomial object \(A\) and probe \(\phi:Y\to X\), define
observation by pullback
\[
\phi^*A.
\]

For a polynomial law \(F\), an affine probe
\[
\phi(t)=p+Lt
\]
gives Wilderber's generalized restriction
\[
R_{F,p,L}(t)=F(p+Lt)=\phi^*F.
\]

The causal interpretation is that a history or subhistory selects a composable
probe into the state/parameter space. Composition of histories corresponds to
functorial pullback:
\[
(\phi\circ\psi)^*=\psi^*\phi^*.
\]

This is a realization theorem, not an identification of all causal systems
with polynomial geometry.

## 16. Finite fields and arithmetic geometry

Over \(\mathbf F_q\), restrictions support exact slicing:
\[
\#X(\mathbf F_q)
=
\sum_{w\in W}
\#\{u\in U:F(w+u)=0\}.
\]

Symmetry reduces the family of probes to orbit representatives. Repeating over
\(\mathbf F_{q^r}\) gives counts \(N_r\) and hence
\[
Z_X(T)=\exp\left(\sum_{r\ge1}N_rT^r/r\right).
\]

Frobenius is treated as a distinguished endomorphism in the finite-field
realization, not as the definition of causal time.

The proposed \(\mathbf F_q\to\mathbf F_1\) comparison keeps the incidence,
orbit, Weyl/Coxeter, matroid and Plücker-support skeleton while field-valued
coefficients are forgotten. This is a research realization and must not be
promoted without explicit functors and comparison theorems.
