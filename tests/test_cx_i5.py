"""CX-I5 exact finite controls; these do not elaborate or emulate Lean.

Reuses the I4 operator model and replays all 99 old tests on an explicit,
hash-checked root projection. The actual/positional check computes one route
from event-history differences and the other from stored positional words.
"""
from __future__ import annotations
import atexit
from functools import lru_cache
import hashlib
import importlib.util
from itertools import product, permutations
import json
from pathlib import Path
import re
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
MODULES = ["Exchange.OperatorTransport", "Exchange.CausalOperatorTransport",
           "Exchange.ArtinOperatorTransport", "Exchange.CausalArtinComparison",
           "Models.ExchangeTransportControls"]
SUFFIX = "\n" + "".join("import CausalGeometry."+m+"\n" for m in MODULES)


def load_i4():
    spec = importlib.util.spec_from_file_location("cx_i4_operators", ROOT/"tests/test_cx_i4.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


OLD = load_i4()
PAIRS = OLD.PAIRS
MAPS = tuple(product(range(2), repeat=2))
FLIP = (0, 2, 1, 3)
COPY = (0, 3, 0, 3)
TOGGLE = (2, 3, 0, 1)
CONTROLLED = (0, 1, 3, 2)


def pair_map(f, p):
    return f[p[0]], f[p[1]]


def compatible(f, r, t):
    R, T = OLD.table_operator(r), OLD.table_operator(t)
    return all(pair_map(f, R(*p)) == T(*pair_map(f, p)) for p in PAIRS)


@lru_cache(None)
def census():
    return tuple((f, r, t) for f in MAPS for r in OLD.ALL_TABLES for t in OLD.ALL_TABLES
                 if compatible(f, r, t))


def transport(f, xs):
    return tuple(f[x] for x in xs)


def event_route(start, positions):
    histories = [tuple(start)]
    for i in positions:
        cur = histories[-1]
        if not 0 <= i < len(cur)-1 or len(set(cur)) != len(cur):
            raise ValueError("not an admitted independent-event exchange")
        histories.append(cur[:i]+(cur[i+1], cur[i])+cur[i+2:])
    return histories


def infer_step(source, target):
    """Recover position from occurrence histories, not from a free position label."""
    if len(source) != len(target):
        raise ValueError("different arities")
    changed = [i for i, (a, b) in enumerate(zip(source, target)) if a != b]
    if (len(changed) != 2 or changed[1] != changed[0]+1
            or source[changed[0]] != target[changed[1]]
            or source[changed[1]] != target[changed[0]]):
        raise ValueError("not an adjacent witnessed exchange")
    return changed[0]


def actual_action(op, histories, xs):
    if len(histories[0]) != len(xs):
        raise ValueError("input is not in the causal fiber")
    for p, q in zip(histories, histories[1:]):
        xs = OLD.step(op, infer_step(p, q), xs)
    return xs


class FiniteTransportChecks(unittest.TestCase):
    def test_identity_and_composition(self):
        identity = (0, 1)
        for r in OLD.ALL_TABLES:
            self.assertTrue(compatible(identity, r, r))
        # All triples in a nontrivial supported domain, without assuming bijections.
        for r, t, u in product((FLIP, COPY, TOGGLE, CONTROLLED), repeat=3):
            for f, g in product(MAPS, repeat=2):
                if compatible(f, r, t) and compatible(g, t, u):
                    self.assertTrue(compatible(tuple(g[f[i]] for i in range(2)), r, u))

    def test_full_binary_intertwiner_census_includes_noninvertible_maps(self):
        c = census()
        self.assertTrue(any(f[0] == f[1] and r != t for f, r, t in c))
        self.assertTrue(all(compatible(f, r, t) for f, r, t in c))

    def test_lift_to_each_position(self):
        for r, t in product((FLIP, COPY, TOGGLE, CONTROLLED), repeat=2):
            R, T = OLD.table_operator(r), OLD.table_operator(t)
            for f in MAPS:
                if not compatible(f, r, t):
                    continue
                for n in range(6):
                    for xs in product(range(2), repeat=n):
                        for i in range(n+2):
                            self.assertEqual(transport(f, OLD.step(R, i, xs)),
                                             OLD.step(T, i, transport(f, xs)))

    def test_lift_to_routes(self):
        for r, t in product((FLIP, COPY, TOGGLE, CONTROLLED), repeat=2):
            R, T = OLD.table_operator(r), OLD.table_operator(t)
            for f in MAPS:
                if not compatible(f, r, t):
                    continue
                for n in (2, 3, 4):
                    for indices in product(range(n-1), repeat=3):
                        for xs in product(range(2), repeat=n):
                            self.assertEqual(transport(f, OLD.word(R, indices, xs)),
                                             OLD.word(T, indices, transport(f, xs)))

    def test_injective_reflection_of_yb(self):
        for f, r, t in census():
            if len(set(f)) == 2 and t in OLD.YB_TABLES:
                self.assertIn(r, OLD.YB_TABLES)

    def test_surjective_transfer_of_yb(self):
        for f, r, t in census():
            if len(set(f)) == 2 and r in OLD.YB_TABLES:
                self.assertIn(t, OLD.YB_TABLES)

    def test_nonsurjective_counterexample_same_carrier(self):
        self.assertIn(FLIP, OLD.YB_TABLES)
        self.assertNotIn(CONTROLLED, OLD.YB_TABLES)
        self.assertTrue(compatible((0, 0), FLIP, CONTROLLED))
        self.assertEqual(set((0, 0)), {0})

    def test_noninjective_hides_yb_failure(self):
        R = OLD.table_operator(TOGGLE)
        self.assertNotIn(TOGGLE, OLD.YB_TABLES)
        collapse = lambda xs: tuple(0 for _ in xs)
        for p in PAIRS:
            self.assertEqual(collapse(R(*p)), (0, 0))
        for xs in OLD.TRIPLES:
            self.assertEqual(collapse(OLD.word(R, (0, 1, 0), xs)),
                             collapse(OLD.word(R, (1, 0, 1), xs)))

    def test_equivalence_reverses_intertwining(self):
        for f, r, t in census():
            if len(set(f)) == 2:
                inverse = tuple(f.index(x) for x in range(2))
                self.assertTrue(compatible(inverse, t, r))

    def test_paired_directions_are_independent(self):
        self.assertTrue(compatible((0, 0), COPY, FLIP))
        self.assertFalse(compatible((0, 1), FLIP, COPY))

    def test_compatible_pair_not_inverse(self):
        self.assertTrue(compatible((0, 0), FLIP, FLIP))
        self.assertNotEqual(transport((0, 0), (1, 1, 1)), (1, 1, 1))
        self.assertEqual(transport((0, 0), (1, 1, 1)), (0, 0, 0))

    def test_both_roundtrips_commute_when_both_squares_hold(self):
        for r, t in product((FLIP, COPY, TOGGLE, CONTROLLED), repeat=2):
            for f, g in product(MAPS, repeat=2):
                if compatible(f, r, t) and compatible(g, t, r):
                    self.assertTrue(compatible(tuple(g[f[i]] for i in range(2)), r, r))
                    self.assertTrue(compatible(tuple(f[g[i]] for i in range(2)), t, t))

    def test_actual_vs_positional_independent_constructions(self):
        for table in OLD.ALL_TABLES:
            op = OLD.table_operator(table)
            for indices in ((), (0,), (1,), (0, 1, 0), (1, 0, 1), (0, 0, 1, 0)):
                histories = event_route((0, 1, 2), indices)
                self.assertEqual(tuple(infer_step(p, q) for p, q in zip(histories, histories[1:])), indices)
                for xs in OLD.TRIPLES:
                    self.assertEqual(actual_action(op, histories, xs), OLD.word(op, indices, xs))

    def test_comparison_works_on_non_yb_operator(self):
        op = OLD.table_operator(TOGGLE)
        actual_p = actual_action(op, event_route((0, 1, 2), (0, 1, 0)), (0, 0, 0))
        actual_q = actual_action(op, event_route((0, 1, 2), (1, 0, 1)), (0, 0, 0))
        self.assertEqual(actual_p, (0, 1, 0))
        self.assertEqual(actual_q, (1, 0, 0))
        self.assertNotEqual(actual_p, actual_q)

    def test_actual_action_respects_declared_artin_relation_for_yb(self):
        p, q = event_route((0, 1, 2), (0, 1, 0)), event_route((0, 1, 2), (1, 0, 1))
        for table in OLD.YB_TABLES:
            op = OLD.table_operator(table)
            for xs in OLD.TRIPLES:
                self.assertEqual(actual_action(op, p, xs), actual_action(op, q, xs))

    def test_contexts_do_not_change_coefficient_transport_law(self):
        op = OLD.table_operator(FLIP)
        for prefix in ((9,), (9, 8)):
            p = event_route(prefix+(0, 1, 2)+(7,), tuple(len(prefix)+i for i in (0, 1, 0)))
            for xs in product(range(2), repeat=len(prefix)+4):
                f = (1, 0)
                self.assertEqual(transport(f, actual_action(op, p, xs)),
                                 actual_action(op, p, transport(f, xs)))

    def test_reject_false_arity_and_nonadjacent_witness(self):
        with self.assertRaises(ValueError):
            actual_action(OLD.table_operator(FLIP), event_route((0, 1, 2), (0,)), (0, 1))
        with self.assertRaises(ValueError):
            infer_step((0, 1, 2), (2, 1, 0))

    def test_component_cast_changes_no_values(self):
        for n in range(5):
            for xs in product(range(2), repeat=n):
                for f in MAPS:
                    # Equality of size certificates cannot change either list.
                    self.assertEqual(transport(f, tuple(xs)), tuple(transport(f, xs)))

    def test_hurwitz_sign_homomorphism(self):
        group = tuple(permutations(range(3)))
        mul = lambda a, b: tuple(a[b[i]] for i in range(3))
        inv = lambda a: tuple(a.index(i) for i in range(3))
        parity = lambda a: sum(a[i] > a[j] for i in range(3) for j in range(i+1, 3)) % 2
        hurwitz = lambda a, b: (mul(mul(a, b), inv(a)), a)
        for a, b in product(group, repeat=2):
            self.assertEqual(parity(mul(a, b)), (parity(a)+parity(b)) % 2)
            self.assertEqual(tuple(map(parity, hurwitz(a, b))), (parity(b), parity(a)))
        for xs in product(group, repeat=3):
            for indices in ((0,), (1,), (0, 1, 0), (1, 0, 1)):
                self.assertEqual(tuple(map(parity, OLD.word(hurwitz, indices, xs))),
                                 OLD.word(OLD.table_operator(FLIP), indices, tuple(map(parity, xs))))

    def test_equality_of_observation_not_faithfulness(self):
        op = OLD.table_operator(COPY)
        self.assertEqual(OLD.word(op, (0,), (0, 0, 0)), OLD.word(op, (1,), (0, 0, 0)))
        # Different event routes still retain their occurrences and exchange position.
        self.assertNotEqual(event_route((0, 1, 2), (0,)), event_route((0, 1, 2), (1,)))


class SourceContracts(unittest.TestCase):
    def test_i4_payload_unchanged_except_exact_append_only_root(self):
        data = json.loads((ROOT/"verification/cx-i4/manifest.json").read_text())
        for path, digest in data["files_sha256"].items():
            b = (ROOT/path).read_bytes()
            if path == "CausalGeometry.lean":
                self.assertTrue(b.endswith(SUFFIX.encode()))
                b = b[:-len(SUFFIX.encode())]
            self.assertEqual(hashlib.sha256(b).hexdigest(), digest, path)

    def test_imports_exactly_once(self):
        lines = (ROOT/"CausalGeometry.lean").read_text().splitlines()
        for m in MODULES:
            self.assertEqual(lines.count("import CausalGeometry."+m), 1)

    def test_existing_paired_primitive_not_replaced(self):
        p = ROOT/"CausalGeometry/Foundation/PairedTransform.lean"
        b = p.read_bytes()
        self.assertEqual(hashlib.sha1(b"blob "+str(len(b)).encode()+b"\0"+b).hexdigest(),
                         "6ee6735ce2d962ba4f0562911993011a7cb0a8b8")
        t = (ROOT/"CausalGeometry/Exchange/CausalOperatorTransport.lean").read_text()
        self.assertIn("PairedTransform A B", t)
        self.assertIn("sourceRoundTrip_route", t)
        self.assertIn("targetRoundTrip_route", t)

    def test_direct_action_not_defined_via_artin(self):
        t = (ROOT/"CausalGeometry/Exchange/CausalArtinComparison.lean").read_text()
        for name in ("forgetPaths U V n ⋙ CausalOperator.action R U V", "actualPositionalIso",
                     "actualArtinIso", "actual_respects_realization", "forget_reifyRoute"):
            self.assertIn(name, t)

    def test_native_natural_transformations_not_reimplemented(self):
        a = (ROOT/"CausalGeometry/Exchange/CausalOperatorTransport.lean").read_text()
        b = (ROOT/"CausalGeometry/Exchange/CausalArtinComparison.lean").read_text()
        self.assertIn("NatIso.ofComponents", a)
        self.assertIn("NatIso.ofComponents", b)
        self.assertNotRegex(a+b, r"structure\s+(?:NatIso|NatTrans|Functor)\b")

    def test_lean_guarded_transfer_hypotheses(self):
        t = (ROOT/"CausalGeometry/Exchange/OperatorTransport.lean").read_text()
        for term in ("hinj : Function.Injective f", "hsurj : Function.Surjective f",
                     "yb_reflects_of_injective", "yb_descends_of_surjective"):
            self.assertIn(term, t)

    def test_no_forbidden_shortcuts_or_downstream_imports(self):
        for m in MODULES:
            t = (ROOT/"CausalGeometry"/(m.replace(".", "/")+".lean")).read_text()
            t = re.sub(r"/-.*?-/", "", t, flags=re.S)
            t = re.sub(r"--[^\n]*", "", t)
            self.assertNotRegex(t, r"\b(sorry|admit|native_decide|unsafe)\b|(?m:^\s*axiom\b)")
            self.assertNotRegex(t, r"(?m)^import (GenContinuum|ECIA|RenormCore)\b")

    def test_kernel_harness_has_named_declarations(self):
        t = (ROOT/"verification/cx-i5/KernelAudit.lean").read_text()
        for term in ("actualPositionalIso", "positiveTransport", "map_route",
                     "hurwitz_hom_intertwines", "yb_reflects_of_injective"):
            self.assertIn(term, t)
        self.assertGreaterEqual(t.count("#print axioms"), 30)


def load_tests(loader, tests, pattern):
    b = (ROOT/"CausalGeometry.lean").read_bytes()
    if not b.endswith(SUFFIX.encode()):
        raise ValueError("not the declared append-only CX-I5 migration")
    projected = b[:-len(SUFFIX.encode())]
    old_manifest = json.loads((ROOT/"verification/cx-i4/manifest.json").read_text())
    if hashlib.sha256(projected).hexdigest() != old_manifest["files_sha256"]["CausalGeometry.lean"]:
        raise ValueError("historical view differs from pinned I4 root")
    temp = tempfile.TemporaryDirectory(prefix="cx-i5-i4-")
    atexit.register(temp.cleanup)
    view = Path(temp.name)
    for name in ("CausalGeometry", "verification", "tests", "tools"):
        (view/name).symlink_to(ROOT/name, target_is_directory=True)
    (view/"CausalGeometry.lean").write_bytes(projected)
    old = load_i4()
    old.ROOT = view
    tests.addTests(loader.loadTestsFromModule(old))
    return tests


if __name__ == "__main__":
    unittest.main(verbosity=2)
