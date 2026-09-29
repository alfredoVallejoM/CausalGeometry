"""Exact rational controls for CX-I6; no finite test substitutes for Lean.

Native causal histories/observations are replayed through the I5 test model.
Matrices are independent arithmetic oracles, not implementations of Lean types.
"""
from __future__ import annotations
import atexit
from fractions import Fraction as Q
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path
import random
import re
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
MODULES = ["Calculus.LinearSquareDefect", "Calculus.GradedDefectCompatibility",
           "Exchange.TensorTransportDefect", "Exchange.LinearizedCausalAction",
           "Models.ExchangeLinearDefectControls"]
SUFFIX = "\n" + "".join("import CausalGeometry."+m+"\n" for m in MODULES)


def load_old():
    spec = importlib.util.spec_from_file_location("cx_i5_defect_baseline", ROOT/"tests/test_cx_i5.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


OLD = load_old()
STATES = tuple(product(range(2), repeat=3))
HISTORIES = OLD.event_route((0, 1, 2), (0, 1, 0))
OPS = [OLD.OLD.FLIP, OLD.OLD.COPY, OLD.OLD.TOGGLE, OLD.OLD.table_operator(OLD.CONTROLLED)]
MAPS = [lambda x, t=t: t[x] for t in OLD.MAPS]


def mat(rows):
    return tuple(tuple(Q(x) for x in row) for row in rows)


def identity(n):
    return mat([[int(i == j) for j in range(n)] for i in range(n)])


def zero(n, m):
    return mat([[0]*m for _ in range(n)])


def add(a, b):
    if len(a) != len(b) or len(a[0]) != len(b[0]):
        raise ValueError("matrix shapes differ")
    return tuple(tuple(x+y for x, y in zip(r, s)) for r, s in zip(a, b))


def neg(a):
    return tuple(tuple(-x for x in r) for r in a)


def sub(a, b):
    return add(a, neg(b))


def mul(a, b):
    if len(a[0]) != len(b):
        raise ValueError("uncomposable matrices")
    return tuple(tuple(sum((a[i][k]*b[k][j] for k in range(len(b))), Q(0))
                       for j in range(len(b[0]))) for i in range(len(a)))


def vec(a, x):
    if len(a[0]) != len(x):
        raise ValueError("wrong input dimension")
    return tuple(sum((c*y for c, y in zip(r, x)), Q(0)) for r in a)


def kron(a, b):
    return tuple(tuple(x*y for x in ar for y in br) for ar in a for br in b)


def square(a, b, f0, f1):
    return sub(mul(b, f0), mul(f1, a))


def tensor_defect(a, b, f):
    ff = kron(f, f)
    return square(a, b, ff, ff)


def random_matrix(rng, n, m):
    return tuple(tuple(Q(rng.randint(-2, 2), rng.randint(1, 3)) for _ in range(m)) for _ in range(n))


def free_matrix(domain, codomain, f):
    """One column per basis state; collisions add when applying to a vector."""
    index = {x: i for i, x in enumerate(codomain)}
    if len(index) != len(codomain):
        raise ValueError("duplicate codomain basis")
    out = [[0]*len(domain) for _ in codomain]
    for j, x in enumerate(domain):
        y = f(x)
        if y not in index:
            raise ValueError("state outside target")
        out[index[y]][j] = 1
    return mat(out)


def action_matrix(op, histories=HISTORIES):
    return free_matrix(STATES, STATES, lambda x: OLD.actual_action(op, histories, x))


def coefficients(f):
    return free_matrix(STATES, STATES, lambda x: tuple(map(f, x)))


class ExactDefectChecks(unittest.TestCase):
    def test_horizontal_rectangular_squares(self):
        rng = random.Random(60601)
        for _ in range(64):
            a0, a1, b0, b1, c0, c1 = [rng.randint(1, 3) for _ in range(6)]
            a,b,c = random_matrix(rng,a1,a0), random_matrix(rng,b1,b0), random_matrix(rng,c1,c0)
            f0,f1,g0,g1 = (random_matrix(rng,b0,a0), random_matrix(rng,b1,a1),
                            random_matrix(rng,c0,b0), random_matrix(rng,c1,b1))
            self.assertEqual(square(a,c,mul(g0,f0),mul(g1,f1)),
                             add(mul(square(b,c,g0,g1),f0), mul(g1,square(a,b,f0,f1))))

    def test_vertical_rectangular_squares(self):
        rng = random.Random(60602)
        for _ in range(64):
            a0,a1,a2,b0,b1,b2 = [rng.randint(1,3) for _ in range(6)]
            a,aa,b,bb = (random_matrix(rng,a1,a0),random_matrix(rng,a2,a1),
                         random_matrix(rng,b1,b0),random_matrix(rng,b2,b1))
            f0,f1,f2 = random_matrix(rng,b0,a0),random_matrix(rng,b1,a1),random_matrix(rng,b2,a2)
            self.assertEqual(square(mul(aa,a),mul(bb,b),f0,f2),
                             add(mul(bb,square(a,b,f0,f1)), mul(square(aa,bb,f1,f2),a)))

    def test_signed_difference_is_not_absolute_value(self):
        i,z = identity(1),zero(1,1)
        self.assertEqual(square(z,i,i,i),neg(square(i,z,i,i)))
        self.assertNotEqual(square(z,i,i,i),square(i,z,i,i))

    def test_square_transport_additivity(self):
        rng=random.Random(60603)
        for _ in range(24):
            a,b,f0,f1,g0,g1=[random_matrix(rng,2,2) for _ in range(6)]
            self.assertEqual(square(a,b,add(f0,g0),add(f1,g1)),
                             add(square(a,b,f0,f1),square(a,b,g0,g1)))

    def test_defect_kernel_is_pointwise_compatibility(self):
        a=mat([[0,1],[1,0]]); b=mat([[0,1],[1,1]]); i=identity(2)
        d=square(a,b,i,i)
        for x in product(range(-2,3),repeat=2):
            self.assertEqual(vec(d,x)==(0,0),vec(b,x)==vec(a,x))

    def test_compatibility_kernel_is_not_automatically_invariant(self):
        a=mat([[0,1],[1,0]]); b=mat([[0,1],[1,1]]); d=square(a,b,identity(2),identity(2))
        self.assertEqual(vec(d,(1,0)),(0,0))
        self.assertNotEqual(vec(d,vec(a,(1,0))),(0,0))

    def test_directional_defects_can_cancel(self):
        i,z=identity(2),zero(2,2)
        d1,d2=square(z,i,i,i),square(i,z,i,i)
        self.assertNotEqual(d1,z); self.assertNotEqual(d2,z)
        self.assertEqual(add(d1,d2),z)
        self.assertEqual(square(z,z,i,i),z)

    def test_compatible_maps_need_not_be_inverse(self):
        a=mat([[0,1],[1,0]]); f=mat([[1,1],[1,1]])
        self.assertEqual(square(a,a,f,f),zero(2,2))
        self.assertNotEqual(mul(f,f),identity(2))

    def test_tensor_defect_composition(self):
        rng=random.Random(60604)
        for _ in range(16):
            a,b,c=[random_matrix(rng,4,4) for _ in range(3)]
            f,g=[random_matrix(rng,2,2) for _ in range(2)]
            self.assertEqual(tensor_defect(a,c,mul(g,f)),
                add(mul(tensor_defect(b,c,g),kron(f,f)),mul(kron(g,g),tensor_defect(a,b,f))))

    def test_tensor_lift_has_cross_terms(self):
        f=mat([[1,2],[0,1]]); g=mat([[0,1],[1,0]])
        self.assertEqual(kron(add(f,g),add(f,g)),
                         add(add(kron(f,f),kron(f,g)),add(kron(g,f),kron(g,g))))
        self.assertNotEqual(kron(add(f,g),add(f,g)),add(kron(f,f),kron(g,g)))

    def test_tensor_defect_is_not_additive_in_coefficient_map(self):
        i,z=identity(1),zero(1,1)
        self.assertEqual(tensor_defect(z,i,add(i,i)),mat([[4]]))
        self.assertEqual(add(tensor_defect(z,i,i),tensor_defect(z,i,i)),mat([[2]]))

    def test_nil_route_has_zero_defect(self):
        nil_history=[(0,1,2)]
        for r,t,f in product(OPS,OPS,MAPS):
            c=coefficients(f)
            self.assertEqual(square(action_matrix(r,nil_history),action_matrix(t,nil_history),c,c),zero(8,8))

    def test_tensor_forward_zero_does_not_imply_backward_zero(self):
        a,b=zero(4,4),identity(4)
        phi,psi=zero(2,2),identity(2)
        self.assertEqual(tensor_defect(a,b,phi),zero(4,4))
        self.assertNotEqual(tensor_defect(b,a,psi),zero(4,4))

    def test_canonical_linearization_composes_and_preserves_collisions(self):
        domain=(0,1,2); target=(0,1); end=(0,)
        f=lambda x:x%2; g=lambda _:0
        fm=free_matrix(domain,target,f); gm=free_matrix(target,end,g)
        self.assertEqual(mul(gm,fm),free_matrix(domain,end,lambda x:g(f(x))))
        self.assertEqual(vec(fm,(1,2,-3)),(-2,2))
        self.assertEqual(vec(mul(gm,fm),(1,2,-3)),(0,))

    def test_basis_defect_matches_direct_causal_square(self):
        for r,t,f in product(OPS,OPS,MAPS):
            rm,tm,cm=action_matrix(r),action_matrix(t),coefficients(f)
            dm=square(rm,tm,cm,cm)
            for col,x in enumerate(STATES):
                y=OLD.actual_action(t,HISTORIES,tuple(map(f,x)))
                z=tuple(map(f,OLD.actual_action(r,HISTORIES,x)))
                expected=tuple(Q(int(s==y)-int(s==z)) for s in STATES)
                self.assertEqual(tuple(row[col] for row in dm),expected)

    def test_actual_route_defect_nonzero(self):
        d=square(action_matrix(OPS[0]),action_matrix(OPS[2]),identity(8),identity(8))
        self.assertNotEqual(d,zero(8,8))
        x=(0,0,0); col=STATES.index(x)
        self.assertEqual(d[STATES.index((0,1,0))][col],1)
        self.assertEqual(d[STATES.index((0,0,0))][col],-1)

    def test_actual_route_directional_defects_cancel(self):
        a,b=action_matrix(OPS[0]),action_matrix(OPS[2]); i=identity(8)
        self.assertEqual(add(square(a,b,i,i),square(b,a,i,i)),zero(8,8))
        self.assertNotEqual(square(a,b,i,i),zero(8,8))

    def test_forward_compatible_backward_incompatible(self):
        copy,flip=action_matrix(OPS[1]),action_matrix(OPS[0])
        const,ident=coefficients(lambda _:0),identity(8)
        self.assertEqual(square(copy,flip,const,const),zero(8,8))
        self.assertNotEqual(square(flip,copy,ident,ident),zero(8,8))

    def test_defect_propagation_on_two_actual_routes(self):
        first=OLD.event_route((0,1,2),(0,1)); second=OLD.event_route(first[-1],(0,1))
        combined=first+second[1:]
        for r,t,f in product(OPS,OPS,MAPS):
            ar,at,br,bt=(action_matrix(r,first),action_matrix(r,second),
                         action_matrix(t,first),action_matrix(t,second))
            c=coefficients(f)
            self.assertEqual(square(action_matrix(r,combined),action_matrix(t,combined),c,c),
                             add(mul(bt,square(ar,br,c,c)),mul(square(at,bt,c,c),ar)))

    def test_augmentation_hides_every_causal_defect(self):
        for r,t,f in product(OPS,OPS,MAPS):
            c=coefficients(f); d=square(action_matrix(r),action_matrix(t),c,c)
            self.assertTrue(all(sum(row[j] for row in d)==0 for j in range(8)))

    def test_nontrivial_coefficient_ring_is_required_for_reflection(self):
        a=free_matrix((0,1),(0,1),lambda x:x)
        b=free_matrix((0,1),(0,1),lambda _:0)
        self.assertNotEqual(a,b)
        mod_one=lambda m:tuple(tuple(x%1 for x in r) for r in m)
        self.assertEqual(mod_one(a),mod_one(b))

    def test_graded_differential_defect_identity(self):
        rng=random.Random(60605); a=mat([[0,1],[0,0]]); b=mat([[0,2],[0,0]])
        for _ in range(64):
            f0,f1,f2=[random_matrix(rng,2,2) for _ in range(3)]
            d0,d1=square(a,b,f0,f1),square(a,b,f1,f2)
            self.assertEqual(add(mul(b,d0),mul(d1,a)),zero(2,2))

    def test_raw_graded_defect_on_cycles_is_exact(self):
        rng=random.Random(60606); a=mat([[0,1],[0,0]]); b=mat([[0,2],[0,0]])
        for _ in range(64):
            f0,f1=[random_matrix(rng,2,2) for _ in range(2)]; x=(Q(3),Q(0))
            d=square(a,b,f0,f1)
            self.assertEqual(vec(a,x),(0,0))
            self.assertEqual(vec(d,x),vec(b,vec(f0,x)))
            self.assertEqual(vec(b,vec(d,x)),(0,0))

    def test_causal_history_admissibility_not_bypassed(self):
        with self.assertRaises(ValueError):
            OLD.infer_step((0,1,2),(2,1,0))
        with self.assertRaises(ValueError):
            OLD.actual_action(OPS[0],HISTORIES,(0,1))


class SourceContracts(unittest.TestCase):
    def test_old_payload_preserved_and_root_append_only(self):
        m=json.loads((ROOT/"verification/cx-i5/manifest.json").read_text())
        for p,h in m["files_sha256"].items():
            b=(ROOT/p).read_bytes()
            if p=="CausalGeometry.lean":
                self.assertTrue(b.endswith(SUFFIX.encode())); b=b[:-len(SUFFIX.encode())]
            self.assertEqual(hashlib.sha256(b).hexdigest(),h,p)

    def test_five_modules_imported_once(self):
        root=(ROOT/"CausalGeometry.lean").read_text().splitlines()
        for m in MODULES:
            self.assertEqual(root.count("import CausalGeometry."+m),1)
            self.assertTrue((ROOT/"CausalGeometry"/(m.replace(".","/")+".lean")).is_file())

    def test_native_tensor_and_free_functor_are_reused(self):
        tensor=(ROOT/"CausalGeometry/Exchange/TensorTransportDefect.lean").read_text()
        linear=(ROOT/"CausalGeometry/Exchange/LinearizedCausalAction.lean").read_text()
        for name in ("TensorProduct.map", "TensorProduct.map_comp", "LinearSquare.horizontal"):
            self.assertIn(name,tensor)
        for name in ("ModuleCat.free K", "ModuleCat.free_map_apply", "ModuleCat.free_hom_ext"):
            self.assertIn(name,linear)
        self.assertNotRegex(tensor+linear,r"(?:structure|inductive)\s+(?:TensorProduct|Finsupp|ModuleCat)\b")

    def test_previous_graded_defect_consumed_not_redefined(self):
        t=(ROOT/"CausalGeometry/Calculus/GradedDefectCompatibility.lean").read_text()
        self.assertIn("import CausalGeometry.Calculus.PairedCochainTransport",t)
        self.assertIn("defect_is_square",t); self.assertIn("B.classOfClosedSucc",t)
        self.assertNotRegex(t,r"(?:def|structure)\s+(?:defect|GradedLinearTransport)\b")

    def test_nontriviality_guarded_and_domains_not_made_invariant(self):
        t=(ROOT/"CausalGeometry/Exchange/LinearizedCausalAction.lean").read_text()
        self.assertIn("theorem defect_zero_iff [Nontrivial K]",t)
        m=(ROOT/"CausalGeometry/Models/ExchangeLinearDefectControls.lean").read_text()
        self.assertIn("compatible_domain_not_invariant",m)
        self.assertIn("nonzero_directional_defects_zero_roundtrip",m)

    def test_no_shortcuts_or_downstream_imports(self):
        for m in MODULES:
            t=(ROOT/"CausalGeometry"/(m.replace(".","/")+".lean")).read_text()
            t=re.sub(r"/-.*?-/","",t,flags=re.S); t=re.sub(r"--[^\n]*","",t)
            self.assertNotRegex(t,r"\b(sorry|admit|native_decide|unsafe)\b|(?m:^\s*axiom\b)")
            self.assertNotRegex(t,r"(?m)^import (GenContinuum|ECIA|RenormCore)\b")

    def test_action_is_from_causal_source_not_artin_definition(self):
        t=(ROOT/"CausalGeometry/Exchange/LinearizedCausalAction.lean").read_text()
        self.assertIn("CausalOperator.action R U V ⋙ ModuleCat.free K",t)
        for n in ("defect_comp_route","defect_comp_coefficient","sourceRoundTrip_defect","targetRoundTrip_defect"):
            self.assertIn(n,t)

    def test_kernel_harness_names_main_boundaries(self):
        t=(ROOT/"verification/cx-i6/KernelAudit.lean").read_text()
        for n in ("TensorTransport.defect_comp", "LinearizedAction.augmentation_defect",
                  "defect_closed_class_zero", "causal_defect_nonzero", "defect_zero_iff"):
            self.assertIn(n,t)
        self.assertGreaterEqual(t.count("#print axioms"),30)


def load_tests(loader, tests, pattern):
    b=(ROOT/"CausalGeometry.lean").read_bytes()
    if not b.endswith(SUFFIX.encode()):
        raise ValueError("not the declared append-only I6 root")
    projected=b[:-len(SUFFIX.encode())]
    previous=json.loads((ROOT/"verification/cx-i5/manifest.json").read_text())
    if hashlib.sha256(projected).hexdigest()!=previous["files_sha256"]["CausalGeometry.lean"]:
        raise ValueError("root prefix is not the exact I5 root")
    temp=tempfile.TemporaryDirectory(prefix="cx-i6-i5-"); atexit.register(temp.cleanup)
    view=Path(temp.name)
    for name in ("CausalGeometry","verification","tests","tools"):
        (view/name).symlink_to(ROOT/name,target_is_directory=True)
    (view/"CausalGeometry.lean").write_bytes(projected)
    old=load_old(); old.ROOT=view
    tests.addTests(loader.loadTestsFromModule(old))
    return tests


if __name__=="__main__":
    unittest.main(verbosity=2)
