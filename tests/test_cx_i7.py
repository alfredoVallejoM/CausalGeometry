"""CX-I7 exact finite invariant-core oracles; these tests do not run Lean.

All old tests are replayed unchanged through a checked root-only projection.
The finite linear solver uses rational row spaces, not floating-point rank or
an enumeration of all histories. Its fixed-point certificate is checked at
EVERY vertex. A budget limit gives an outer approximation, not a fixed point.
"""
from __future__ import annotations
import atexit
from fractions import Fraction as Q
import hashlib
import importlib.util
from itertools import permutations, product
import json
from pathlib import Path
import random
import re
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
MODULES = ["Calculus.LinearInvariantCore", "Calculus.PersistentLinearCompatibility",
           "Calculus.LinearInvariantPaths", "Exchange.PersistentCompatibility",
           "Models.ExchangePersistentControls"]
SUFFIX = "\n" + "".join("import CausalGeometry."+m+"\n" for m in MODULES)


def matrix(rows):
    return tuple(tuple(Q(v) for v in row) for row in rows)


def eye(n):
    return matrix([[int(i == j) for j in range(n)] for i in range(n)])


def zero(m,n):
    return matrix([[0]*n for _ in range(m)])


def mul(a,b):
    if not a or not b or len(a[0]) != len(b):
        raise ValueError("nonempty compatible matrix dimensions required")
    return tuple(tuple(sum((x*y for x,y in zip(row,col)),Q(0)) for col in zip(*b)) for row in a)


def sub(a,b):
    if len(a) != len(b) or any(len(x) != len(y) for x,y in zip(a,b)):
        raise ValueError("matrix dimensions differ")
    return tuple(tuple(x-y for x,y in zip(ar,br)) for ar,br in zip(a,b))


def mv(a,x):
    return tuple(sum((v*w for v,w in zip(row,x)),Q(0)) for row in a)


def rows_basis(rows, n):
    """Canonical rational RREF basis for an annihilator. Empty means no equations."""
    a=[list(map(Q,row)) for row in rows]
    if any(len(row)!=n for row in a):
        raise ValueError("wrong annihilator width")
    r=0
    for c in range(n):
        piv=next((i for i in range(r,len(a)) if a[i][c]),None)
        if piv is None:
            continue
        a[r],a[piv]=a[piv],a[r]
        d=a[r][c]; a[r]=[x/d for x in a[r]]
        for i in range(len(a)):
            if i!=r and a[i][c]:
                d=a[i][c]; a[i]=[x-d*y for x,y in zip(a[i],a[r])]
        r+=1
        if r==len(a):
            break
    return tuple(tuple(row) for row in a[:r])


def annihilates(rows, x):
    return all(v==0 for v in mv(rows,x))


def refines(a,b,n):
    """kernel(a) <= kernel(b) iff row(b) is contained in row(a)."""
    return rows_basis(a+b,n)==rows_basis(a,n)


def prune(dimensions, local, old, edges):
    pending={p:list(local[p]) for p in dimensions}
    for p,q,a in edges:
        if len(a)!=dimensions[q] or any(len(row)!=dimensions[p] for row in a):
            raise ValueError("edge has wrong dependent dimensions")
        if old[q]:
            pending[p].extend(mul(old[q],a))
    return {p:rows_basis(pending[p],dimensions[p]) for p in dimensions}


def invariant_core(dimensions, local, edges, budget=100):
    if budget<0:
        raise ValueError("negative budget")
    base={p:rows_basis(local[p],dimensions[p]) for p in dimensions}
    current=base
    history=[sum(len(current[p]) for p in dimensions)]
    for k in range(budget):
        new=prune(dimensions,base,current,edges)
        history.append(sum(len(new[p]) for p in dimensions))
        if new==current:
            return {"status":"EXACT_FIXED_POINT","rows":current,"rounds":k+1,"ranks":history}
        current=new
    return {"status":"INCONCLUSIVE","rows":current,"rounds":budget,"ranks":history}


def certify(dimensions, local, edges, candidate):
    """One exact step checks stability and local containment, but NOT maximality alone.

Maximality additionally needs the recorded top-down iteration/reachable seed.
"""
    return prune(dimensions,local,candidate,edges)==candidate


STATES=list(product(range(2),repeat=3))
HISTORIES=list(permutations(range(3)))


def flip(a,b): return b,a

def copy_right(a,b): return b,b

def toggle(a,b): return 1-a,b

def wake(a,b): return (b,a) if a or b else (1,1)


def local_matrix(op,i):
    out=[[0]*8 for _ in range(8)]
    for j,x in enumerate(STATES):
        y=list(x); y[i],y[i+1]=op(y[i],y[i+1])
        out[STATES.index(tuple(y))][j]=1
    return matrix(out)


def swap_history(p,i):
    q=list(p);q[i],q[i+1]=q[i+1],q[i]
    return tuple(q)


def causal_problem(source,target):
    a=[local_matrix(source,i) for i in (0,1)]
    b=[local_matrix(target,i) for i in (0,1)]
    edges=[(p,swap_history(p,i),a[i]) for p in HISTORIES for i in (0,1)]
    local={p:sub(b[0],a[0])+sub(b[1],a[1]) for p in HISTORIES}
    return {p:8 for p in HISTORIES},local,edges,a,b


def word(a,indices):
    result=eye(len(a[0]))
    for i in indices:
        result=mul(a[i],result)
    return result


def unit_state(values):
    return tuple(Q(int(x==tuple(values))) for x in STATES)


class ExactInvariantChecks(unittest.TestCase):
    def test_rref_exact_and_canonical(self):
        rows=matrix([[1,2,3],[2,4,6],[0,1,1]])
        expected=matrix([[1,0,1],[0,1,1]])
        self.assertEqual(rows_basis(rows,3),expected)
        self.assertEqual(rows_basis(rows[::-1]+rows,3),expected)

    def test_unconstrained_and_zero_domains_are_fixed(self):
        dims={0:2}; edges=[(0,0,matrix([[0,1],[1,0]]))]
        self.assertEqual(invariant_core(dims,{0:()},edges)["rows"][0],())
        self.assertEqual(invariant_core(dims,{0:eye(2)},edges)["rows"][0],eye(2))

    def test_no_edges_gives_the_original_local_domain(self):
        dims={0:2,1:3}; local={0:matrix([[1,0]]),1:matrix([[0,1,0]])}
        result=invariant_core(dims,local,[])
        self.assertEqual(result["rows"],local)
        self.assertEqual(result["status"],"EXACT_FIXED_POINT")

    def test_i6_plane_kernel_is_not_invariant(self):
        a=matrix([[0,1],[1,0]]); local={0:matrix([[0,0],[0,1]])}
        self.assertTrue(annihilates(local[0],(1,0)))
        self.assertFalse(annihilates(local[0],mv(a,(1,0))))
        r=invariant_core({0:2},local,[(0,0,a)])
        self.assertEqual(r["rows"][0],eye(2))

    def test_horizons_are_outer_approximations(self):
        d,l,e,_,_=causal_problem(flip,wake)
        exact=invariant_core(d,l,e)
        for k in range(4):
            approx=invariant_core(d,l,e,k)
            for p in d:
                self.assertTrue(refines(exact["rows"][p],approx["rows"][p],d[p]))

    def test_all_generator_kernels_can_fail_after_two_steps(self):
        d,l,e,a,b=causal_problem(flip,wake); x=unit_state((0,1,0)); p=(0,1,2)
        self.assertTrue(annihilates(l[p],x))
        self.assertNotEqual(mv(word(a,(0,1)),x),mv(word(b,(0,1)),x))
        result=invariant_core(d,l,e)
        self.assertFalse(annihilates(result["rows"][p],x))

    def test_delayed_failure_has_actual_histories(self):
        p=(0,1,2); p=swap_history(p,0);self.assertEqual(p,(1,0,2))
        p=swap_history(p,1); self.assertEqual(p,(1,2,0))
        _,_,_,a,b=causal_problem(flip,wake);x=unit_state((0,1,0))
        self.assertEqual(mv(word(a,(0,1)),x),unit_state((1,0,0)))
        self.assertEqual(mv(word(b,(0,1)),x),unit_state((1,1,1)))

    def test_nonzero_proper_persistent_domain(self):
        d,l,e,_,_=causal_problem(flip,copy_right); r=invariant_core(d,l,e)
        for p in d:
            self.assertTrue(annihilates(r["rows"][p],unit_state((0,0,0))))
            self.assertTrue(annihilates(r["rows"][p],unit_state((1,1,1))))
            self.assertFalse(annihilates(r["rows"][p],unit_state((0,1,0))))
            self.assertGreater(len(r["rows"][p]),0)
            self.assertLess(len(r["rows"][p]),8)

    def test_each_computed_domain_is_preserved_by_every_actual_edge(self):
        for target in (copy_right,toggle,wake):
            d,l,e,_,_=causal_problem(flip,target); r=invariant_core(d,l,e)["rows"]
            for p,q,a in e:
                pre=mul(r[q],a) if r[q] else ()
                self.assertTrue(refines(r[p],pre,d[p]))

    def test_constant_states_persist_for_many_lengths(self):
        for n in range(1,7):
            for a in (0,1):
                xs=[a]*n
                for i in range(max(n-1,0)):
                    for op in (flip,copy_right):
                        y=xs.copy();y[i],y[i+1]=op(y[i],y[i+1])
                        self.assertEqual(y,xs)

    def test_formal_linear_combinations_are_not_individual_states(self):
        d,l,e,_,_=causal_problem(flip,toggle);r=invariant_core(d,l,e)["rows"]
        for p in d:
            self.assertFalse(any(annihilates(r[p],unit_state(x)) for x in STATES))
            self.assertTrue(annihilates(r[p],(1,)*8))
            self.assertEqual(len(r[p]),7)

    def test_more_constraints_reduce_the_core(self):
        d,l,e,_,_=causal_problem(flip,copy_right)
        extra={p:l[p]+(unit_state((0,0,0)),) for p in d}
        r=invariant_core(d,l,e)["rows"];s=invariant_core(d,extra,e)["rows"]
        for p in d:self.assertTrue(refines(s[p],r[p],d[p]))

    def test_more_continuations_reduce_the_core(self):
        d,l,e,_,_=causal_problem(flip,wake)
        r=invariant_core(d,l,e[:6])["rows"];s=invariant_core(d,l,e)["rows"]
        for p in d:self.assertTrue(refines(s[p],r[p],d[p]))

    def test_core_idempotence(self):
        d,l,e,_,_=causal_problem(flip,wake);r=invariant_core(d,l,e)
        self.assertEqual(invariant_core(d,r["rows"],e)["rows"],r["rows"])

    def test_horizon_matches_all_defects_up_to_its_depth(self):
        d,l,e,a,b=causal_problem(flip,wake);p=(0,1,2)
        for horizon in range(4):
            allrows=()
            for n in range(horizon+2):
                for route in product((0,1),repeat=n):
                    allrows+=sub(word(b,route),word(a,route))
            expected=rows_basis(allrows,8)
            found=invariant_core(d,l,e,horizon)["rows"][p]
            self.assertEqual(found,expected)

    def test_global_not_single_vertex_stopping(self):
        # Vertex 0 appears stationary on the first pass, but changes next pass.
        d={0:1,1:1,2:1};l={0:(),1:(),2:eye(1)};e=[(0,1,eye(1)),(1,2,eye(1))]
        r=invariant_core(d,l,e,1)
        self.assertEqual(r["rows"][0],())
        self.assertEqual(r["status"],"INCONCLUSIVE")
        self.assertEqual(invariant_core(d,l,e)["rows"][0],eye(1))

    def test_budget_exhaustion_is_not_exactness(self):
        d={0:4};l={0:matrix([[1,0,0,0]])};a=matrix([[0,1,0,0],[0,0,1,0],[0,0,0,1],[0,0,0,0]])
        e=[(0,0,a)]
        self.assertEqual(invariant_core(d,l,e,1)["status"],"INCONCLUSIVE")
        r=invariant_core(d,l,e,5)
        self.assertEqual(r["status"],"EXACT_FIXED_POINT")
        self.assertEqual(r["rows"][0],eye(4))
        self.assertEqual(r["ranks"],[1,2,3,4,4])

    def test_stationarity_certificate_is_not_maximality_without_iteration(self):
        d={0:2};l={0:()};e=[(0,0,eye(2))]
        self.assertTrue(certify(d,l,e,{0:eye(2)})) # bottom is stable
        self.assertNotEqual(invariant_core(d,l,e)["rows"],{0:eye(2)})

    def test_finite_dimension_bounds_strict_refinements(self):
        rng=random.Random(7307)
        for trial in range(16):
            d={0:2,1:3};l={0:matrix([[rng.randrange(-2,3),rng.randrange(-2,3)]]),1:()}
            e=[(0,1,matrix([[rng.randrange(-2,3) for _ in range(2)] for _ in range(3)])),
               (1,0,matrix([[rng.randrange(-2,3) for _ in range(3)] for _ in range(2)]))]
            result=invariant_core(d,l,e,7)
            self.assertEqual(result["status"],"EXACT_FIXED_POINT")
            ranks=result["ranks"]
            self.assertTrue(all(a<b for a,b in zip(ranks[:-2],ranks[1:-1])))
            self.assertLessEqual(len(ranks)-2,sum(d.values())-ranks[0])

    def test_rectangular_graph_is_well_typed(self):
        d={0:2,1:1};l={0:(),1:eye(1)};e=[(0,1,matrix([[1,2]]))]
        r=invariant_core(d,l,e)["rows"]
        self.assertTrue(annihilates(r[0],(-2,1)))
        self.assertFalse(annihilates(r[0],(1,0)))
        with self.assertRaises(ValueError):
            invariant_core(d,l,[(0,1,eye(2))])

    def test_compound_cancellation_does_not_certify_factors(self):
        d,l,e,_,_=causal_problem(flip,toggle);r=invariant_core(d,l,e)["rows"]
        d2,l2,e2,_,_=causal_problem(flip,flip);s=invariant_core(d2,l2,e2)["rows"]
        x=unit_state((0,0,0));p=(0,1,2)
        self.assertFalse(annihilates(r[p],x));self.assertTrue(annihilates(s[p],x))

    def test_terminal_cancellation_is_not_prefix_compatibility(self):
        a=matrix([[1,0],[0,1]]);b=matrix([[0,1],[1,0]]);x=(1,0)
        self.assertNotEqual(mv(a,x),mv(b,x))
        self.assertEqual(mv(mul(a,a),x),mv(mul(b,b),x))

    def test_augmentation_can_hide_nonzero_persistent_failure(self):
        d,l,e,a,b=causal_problem(flip,toggle);x=unit_state((0,0,0))
        defect=sub(word(b,(0,1,0)),word(a,(0,1,0)))
        self.assertFalse(annihilates(defect,x))
        self.assertEqual(mul(matrix([[1]*8]),defect),zero(1,8))

    def test_rational_tiny_nonzero_constraint_is_not_discarded(self):
        eps=Q(1,10**30)
        self.assertEqual(rows_basis(((eps,0),),2),matrix([[1,0]]))
        self.assertFalse(annihilates(((eps,0),),(1,0)))


class SourceContracts(unittest.TestCase):
    def test_prior_payload_unchanged_and_root_exact(self):
        m=json.loads((ROOT/"verification/cx-i6/manifest.json").read_text())
        for path,digest in m["files_sha256"].items():
            data=(ROOT/path).read_bytes()
            if path=="CausalGeometry.lean":
                self.assertTrue(data.endswith(SUFFIX.encode()));data=data[:-len(SUFFIX.encode())]
            self.assertEqual(hashlib.sha256(data).hexdigest(),digest,path)

    def test_new_modules_imported_once(self):
        root=(ROOT/"CausalGeometry.lean").read_text().splitlines()
        for m in MODULES:
            self.assertEqual(root.count("import CausalGeometry."+m),1)

    def test_native_carriers_and_old_defects_reused(self):
        s=(ROOT/"CausalGeometry/Calculus/LinearInvariantCore.lean").read_text()
        self.assertIn("Submodule K",s);self.assertIn("ModuleCat.ofHom",s)
        t=(ROOT/"CausalGeometry/Calculus/PersistentLinearCompatibility.lean").read_text()
        self.assertIn("LinearSquare.defect",t)
        self.assertNotRegex(s+t,r"(?:inductive|structure)\s+(?:Submodule|Functor|Category|Finsupp)\b")

    def test_maximality_and_naturality_are_results(self):
        for path,names in {
            "Calculus/LinearInvariantCore.lean":["theorem le_core","theorem core_stable","def inclusion"],
            "Calculus/PersistentLinearCompatibility.lean":["theorem domain_stable","theorem domain_maximal","def transport"],
            "Calculus/LinearInvariantPaths.lean":["theorem persistent_eq_core_generators","theorem horizon_fixed_eq_core"]}.items():
            s=(ROOT/"CausalGeometry"/path).read_text()
            for n in names:self.assertIn(n,s)

    def test_causal_action_not_artin_is_the_source(self):
        s=(ROOT/"CausalGeometry/Exchange/PersistentCompatibility.lean").read_text()
        self.assertIn("action K R U V",s)
        self.assertIn("coefficient K f q.length",s)
        self.assertNotIn("Artin.positiveAction",s)

    def test_linear_domain_not_equated_to_compatible_basis_states(self):
        s=(ROOT/"CausalGeometry/Exchange/PersistentCompatibility.lean").read_text()
        self.assertIn("theorem basis_mem_iff [Nontrivial K]",s)
        self.assertIn("theorem span_states_le [Nontrivial K]",s)
        self.assertNotIn("span_states_eq",s)

    def test_counterexamples_use_existing_histories(self):
        s=(ROOT/"CausalGeometry/Models/ExchangePersistentControls.lean").read_text()
        for n in ("swapFirst 0 1 2", "swapSecond 1 0 2", "middle_locally_compatible",
                  "middle_delayed_failure", "persistent_nonzero_proper", "composition_inclusion_can_be_strict"):
            self.assertIn(n,s)

    def test_no_shortcuts_or_external_target_imports(self):
        for m in MODULES:
            s=(ROOT/"CausalGeometry"/(m.replace(".","/")+".lean")).read_text()
            s=re.sub(r"/-.*?-/","",s,flags=re.S);s=re.sub(r"--[^\n]*","",s)
            self.assertNotRegex(s,r"\b(sorry|admit|native_decide|unsafe)\b|(?m:^\s*axiom\b)")
            self.assertNotRegex(s,r"(?m)^import (GenContinuum|ECIA|RenormCore)\b")

    def test_kernel_harness_covers_real_conclusions(self):
        s=(ROOT/"verification/cx-i7/KernelAudit.lean").read_text()
        for name in ("persistent_eq_core_generators","horizon_fixed_eq_core","PersistentLinear.transport",
                     "middle_delayed_failure","persistent_nonzero_proper"):
            self.assertIn(name,s)


def load_tests(loader,tests,pattern):
    data=(ROOT/"CausalGeometry.lean").read_bytes()
    if not data.endswith(SUFFIX.encode()):raise ValueError("undeclared I7 root")
    projected=data[:-len(SUFFIX.encode())]
    oldmanifest=json.loads((ROOT/"verification/cx-i6/manifest.json").read_text())
    if hashlib.sha256(projected).hexdigest()!=oldmanifest["files_sha256"]["CausalGeometry.lean"]:
        raise ValueError("not the exact I6 root")
    temp=tempfile.TemporaryDirectory(prefix="cx-i7-i6-");atexit.register(temp.cleanup)
    view=Path(temp.name)
    for name in ("CausalGeometry","verification","tests","tools"):
        (view/name).symlink_to(ROOT/name,target_is_directory=True)
    (view/"CausalGeometry.lean").write_bytes(projected)
    spec=importlib.util.spec_from_file_location("cx_i6_regression",ROOT/"tests/test_cx_i6.py")
    old=importlib.util.module_from_spec(spec);spec.loader.exec_module(old);old.ROOT=view
    tests.addTests(loader.loadTestsFromModule(old))
    return tests


if __name__=="__main__":unittest.main(verbosity=2)
