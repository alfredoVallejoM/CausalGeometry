# Causal geometry and Wilderber generalized restrictions

## 1. Wilderber structure being compared

The post-W19 Wilderber program takes a homogeneous/polynomial law \(F\) and an
affine probe
\[
\phi(t)=p+Lt
\]
and forms
\[
R_{F,p,L}(t)=F(p+Lt)=\phi^*F.
\]

This is the affine-linear specialization of the generalized pullback
\[
\phi^*A
\]
for admissible \(\phi:Y\to X\).

The central laws already identified in Wilderber are:
- degree bound;
- associative/nested restriction;
- translation compatibility;
- affine covariance;
- scalar-extension compatibility;
- contained-subspace criterion;
- Hasse/restriction commutation;
- Grassmann/Plücker classification of subspace probes;
- automorphism preservation of restricted invariant profiles.

## 2. Structural relation to causal diaries

The relation is not “causality = polynomial restriction”. Instead:
\[
\boxed{\text{causal history}\leadsto\text{composable probe}}
\]
and
\[
\boxed{\text{restriction/pullback}\leadsto
\text{observation of a global law along that history}.}
\]

Let a causal realization assign to each history \(H\) a map
\[
\phi_H:Y_H\to X.
\]

Then a global law \(A\) is observed along the history by
\[
Obs_A(H)=\phi_H^*A.
\]

If continuation \(K\) refines \(H\) through
\[
\psi_{K/H}:Y_K\to Y_H,
\]
then
\[
\phi_K=\phi_H\circ\psi_{K/H}
\]
and
\[
Obs_A(K)=\psi_{K/H}^*Obs_A(H).
\]

Thus **causal composition becomes nested restriction**.

## 3. Constraints as causal observations

For an algebraic constraint \(F=0\), a causal probe produces
\[
R_{F,p,L}=0.
\]

A global constraint can therefore be propagated through a diary as a family of
lower-dimensional constraints.

A diary of probes is a structured constraint network:
- histories carry restricted laws;
- events refine or change probes;
- edges carry pullback maps;
- concurrency produces comparison squares when independent;
- incompatible events create distinct constraint branches.

This is strictly richer than evaluating \(F\) at points.

## 4. Hasse calculus and causal differentiation

Wilderber's restriction theorem program requires
\[
Hasse(R_{F,p,L})
=
L^*(\text{directional Hasse data of }F).
\]

For an event direction realized by \(L_e\), first causal variation of a
polynomial observable compares with the first Hasse layer, and higher causal
compositions compare with higher Hasse layers.

Hence:
\[
\text{causal derivative along events}
\longrightarrow
\text{directional Hasse restriction}.
\]

This matters especially in positive characteristic because Hasse derivatives
retain factorial-free semantics.

## 5. Symmetry, orbits and causal coarse-graining

For
\[
G_F(q)=\{g\in GL_n(\mathbf F_q):F(gx)=F(x)\},
\]
automorphisms transport probes
\[
(p,L)\mapsto(gp,gL)
\]
and automorphism-related probes have equivalent restricted invariant profiles.

Causally, symmetry identifies histories whose observations belong to the same
orbit:
\[
Hist\to Hist/G_F.
\]

This is a principled coarse-graining and also a computational compression:
evaluate one orbit representative and reconstruct the family from the action
and stabilizers.

## 6. Grassmann/Plücker probes

A \(k\)-dimensional linear probe is intrinsically a point of
\[
Gr(k,V),
\]
not a chosen basis.

Its exterior representative
\[
[v_1\wedge\cdots\wedge v_k]\in\mathbf P(\Lambda^kV)
\]
satisfies Grassmann--Plücker relations.

Thus equivalent families of event directions/subspaces can be represented by
one intrinsic probe object; Wilderber evaluates the global law through it.

## 7. Finite-field slicing

If \(V=W\oplus U\), exact slicing gives
\[
\#X(\mathbf F_q)
=
\sum_{w\in W}
\#\{u\in U:F(w+u)=0\}.
\]

Read causally:
1. select a slice \(w\);
2. pull back the global constraint to \(w+U\);
3. solve/count the restricted law;
4. aggregate.

If a symmetry group acts on slices, the diary is quotiented by orbits and
orbit/stabilizer data reconstructs the full exact count.

## 8. Extension fields, Frobenius and zeta

Repeat over
\[
\mathbf F_{q^r}.
\]

The restriction diary yields
\[
N_r=\#X(\mathbf F_{q^r})
\]
and
\[
Z_X(T)=\exp\left(\sum_{r\ge1}N_rT^r/r\right).
\]

Frobenius is a distinguished endomorphism in this realization. It is **not**
identified with causal time in the kernel.

The useful chain is:
\[
\text{causal source}
\to
\text{finite-field realization}
\to
\text{Frobenius iterates/traces}
\to
N_r
\to
Z_X.
\]

This is a direct bridge to the cyclic/trace side of ECIA.

## 9. The \(\mathbf F_q\to\mathbf F_1\) route

The proposed limit/specialization keeps thin combinatorial data while
forgetting field-valued thickness:
- incidence relations;
- Weyl/Coxeter skeletons;
- matroidal dependence;
- supports of Plücker coordinates;
- orbit/stabilizer combinatorics.

In causal terms it is a forgetful realization
\[
R_q(D)\to R_1(D)
\]
that preserves dependency/incidence/probe structure while discarding
coefficient data.

Motivating classical patterns include
\[
\#\mathbf P^{n-1}(\mathbf F_1)=n,
\]
\[
Gr(k,n)(\mathbf F_1)\sim\{I\subseteq[n]:|I|=k\},
\]
and \(G(\mathbf F_1)\) governed by a Weyl group.

These motivate the target. They do not construct the required functor.

## 10. Arithmetic-geometric consequences

The combined architecture is:
\[
\text{causal source}
\to
\text{probe diary}
\to
\text{restricted algebraic laws}
\to
\text{finite-field point counts}
\to
\text{Frobenius/trace data}
\to
\text{local zeta factors}.
\]

This matters for ECIA because ECIA already contains:
- structural prime profiles;
- cyclic primitives;
- Frobenius-like actions;
- Tate/local realizations;
- trace/determinant zetas;
- local/global comparison.

Wilderber supplies a concrete algebraic-geometric measurement language.
CausalGeometry supplies the generative/process language.

## 11. Deeper relation: restrictions and causal constraints

A generalized restriction is a *local view of a global constraint*.
A causal event is a *transition that changes which local views are available*.

Hence a generalized constraint system can be modeled as a functor
\[
\mathcal H_D^{op}\to\mathbf{Constraint},
\]
where \(\mathcal H_D\) is the history category and the functor sends a history
to the restrictions valid/visible there.

Causal dependency says which restriction refinements are allowed.
Conflict says which constraint branches cannot coexist.
Concurrency says which refinements commute.
Predictive quotient identifies histories inducing indistinguishable future
restriction systems.

This is the precise meeting point of the two architectures.

## 12. Why they remain separate repositories

CausalGeometry does not import Wilderber. Wilderber is the exact computational
geometry engine; CausalGeometry formalizes upstream mathematical contracts.

A future adapter may certify:
- pullback functoriality;
- affine restriction laws;
- Hasse transport;
- orbit compression;
- finite-field slicing;
- comparison to arithmetic shadows.

No workflow or cross-repository build machinery is required for this
mathematical relation.
