"""CX-I4 finite local-operator checks. No test here elaborates Lean.

The exhaustive operator census is over Bool^2 only. Higher-rank checks remain
finite evidence; the separate Lean source states the arbitrary-rank results.
"""
from __future__ import annotations
import atexit
import hashlib
import importlib.util
from itertools import permutations, product
import json
from pathlib import Path
import re
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
MODULES = ["Exchange.LocalOperator", "Exchange.ArtinPresentation", "Exchange.CausalOperator",
           "Exchange.CausalArtin", "Models.ExchangeOperatorControls"]
SUFFIX = "\n" + "".join(f"import CausalGeometry.{m}\n" for m in MODULES)
CONCURRENT_IMPORTS = ["import CausalGeometry.Realization.LocalArithmeticSource\n",
                      "import CausalGeometry.Models.LocalArithmeticSourceControls\n"]
PAIRS = tuple(product(range(2), repeat=2))
TRIPLES = tuple(product(range(2), repeat=3))


def table_operator(table):
    return lambda a, b: PAIRS[table[2*a+b]]


def step(op, i, xs):
    if i < 0:
        raise ValueError("index is not a natural number")
    if i+1 >= len(xs):
        return tuple(xs)
    return tuple(xs[:i]) + tuple(op(xs[i], xs[i+1])) + tuple(xs[i+2:])


def checked(op, generators, i, xs):
    if len(xs) != generators+1 or not 0 <= i < generators:
        raise ValueError("ill-typed arity or unavailable adjacent pair")
    return step(op, i, xs)


def word(op, indices, xs):
    for i in indices:
        xs = checked(op, len(xs)-1, i, xs)
    return tuple(xs)


def yb(op):
    return all(word(op, (0, 1, 0), t) == word(op, (1, 0, 1), t) for t in TRIPLES)


def involutive(op):
    return all(tuple(op(*op(*p))) == p for p in PAIRS)


ALL_TABLES = tuple(product(range(4), repeat=4))
YB_TABLES = tuple(t for t in ALL_TABLES if yb(table_operator(t)))
FLIP = lambda a, b: (b, a)
COPY = lambda a, b: (b, b)
TOGGLE = lambda a, b: (1-a, b)
S3 = tuple(permutations(range(3)))
IDENTITY = (0, 1, 2)


def mul(a, b):
    return tuple(a[b[i]] for i in range(3))


def inv(a):
    return tuple(a.index(i) for i in range(3))


def hurwitz(a, b):
    return mul(mul(a, b), inv(a)), a


def hurwitz_inv(a, b):
    return b, mul(mul(inv(b), a), b)


def group_product(xs):
    out = IDENTITY
    for x in xs:
        out = mul(out, x)
    return out


def project_i3_root(content):
    if not content.endswith(SUFFIX):
        raise ValueError("unknown CX root suffix")
    content = content[:-len(SUFFIX)]
    for line in CONCURRENT_IMPORTS:
        if content.count(line) != 1:
            raise ValueError("concurrent import boundary changed")
        content = content.replace(line, "")
    return content


class OperatorFiniteChecks(unittest.TestCase):
    def test_operator_census_exhaustive(self):
        self.assertEqual(len(ALL_TABLES), 256)
        self.assertTrue(0 < len(YB_TABLES) < 256)
        self.assertTrue(any(len(set(t)) < 4 for t in YB_TABLES))
        self.assertTrue(any(len(set(t)) == 4 for t in ALL_TABLES if t not in YB_TABLES))

    def test_length_preserved_for_every_boolean_operator(self):
        for t in ALL_TABLES:
            op = table_operator(t)
            for n in range(5):
                for xs in product(range(2), repeat=n):
                    for i in range(n+2):
                        self.assertEqual(len(step(op, i, xs)), n)

    def test_far_commutativity_without_yb(self):
        for t in ALL_TABLES:
            op = table_operator(t)
            for xs in product(range(2), repeat=5):
                for i, j in ((0, 2), (0, 3), (1, 3)):
                    self.assertEqual(word(op, (i, j), xs), word(op, (j, i), xs))

    def test_all_boolean_yb_operators_lift_to_higher_arity(self):
        for t in YB_TABLES:
            op = table_operator(t)
            for size in range(3, 7):
                for xs in product(range(2), repeat=size):
                    for i in range(size-2):
                        self.assertEqual(word(op, (i, i+1, i), xs), word(op, (i+1, i, i+1), xs))

    def test_every_invertible_boolean_operator_lifts_with_inverse(self):
        for t in permutations(range(4)):
            R, Q = table_operator(t), table_operator(tuple(t.index(k) for k in range(4)))
            for size in range(2, 6):
                for xs in product(range(2), repeat=size):
                    for i in range(size-1):
                        self.assertEqual(step(Q, i, step(R, i, xs)), xs)
                        self.assertEqual(step(R, i, step(Q, i, xs)), xs)

    def test_copy_right_yb_not_injective(self):
        self.assertTrue(yb(COPY))
        self.assertEqual(COPY(0, 0), COPY(1, 0))
        self.assertEqual(len({COPY(*p) for p in PAIRS}), 2)

    def test_involutive_does_not_imply_yb(self):
        self.assertTrue(involutive(TOGGLE))
        self.assertFalse(yb(TOGGLE))
        self.assertEqual(word(TOGGLE, (0, 1, 0), (0, 0, 0)), (0, 1, 0))
        self.assertEqual(word(TOGGLE, (1, 0, 1), (0, 0, 0)), (1, 0, 0))

    def test_unavailable_third_slot_refutes_unrestricted_law(self):
        xs = (0, 1)
        left = step(FLIP, 0, step(FLIP, 1, step(FLIP, 0, xs)))
        right = step(FLIP, 1, step(FLIP, 0, step(FLIP, 1, xs)))
        self.assertNotEqual(left, right)
        self.assertTrue(yb(FLIP))

    def test_sized_api_rejects_invalid_positions_and_shapes(self):
        for n, i, xs in ((1, 1, (0, 1)), (2, 0, (0, 1)), (0, 0, (0,)), (2, -1, (0, 0, 0))):
            with self.assertRaises(ValueError):
                checked(FLIP, n, i, xs)

    def test_empty_word_and_no_generator_boundary(self):
        self.assertEqual(word(FLIP, (), (0,)), (0,))
        with self.assertRaises(ValueError):
            word(FLIP, (0,), (0,))

    def test_prefix_shift_for_every_boolean_operator(self):
        for t in ALL_TABLES:
            op = table_operator(t)
            for prefix, xs in product(TRIPLES, repeat=2):
                for i in (0, 1, 2, 3):
                    self.assertEqual(step(op, len(prefix)+i, prefix+xs), prefix+step(op, i, xs))

    def test_suffix_requires_two_slots_in_left_block(self):
        for t in ALL_TABLES:
            op = table_operator(t)
            for xs, ys in product(TRIPLES, repeat=2):
                for i in (0, 1):
                    self.assertEqual(step(op, i, xs+ys), step(op, i, xs)+ys)
        self.assertNotEqual(step(FLIP, 0, (0,)+(1,)), step(FLIP, 0, (0,))+(1,))

    def test_hurwitz_group_inverse_and_product(self):
        for a, b in product(S3, repeat=2):
            self.assertEqual(hurwitz_inv(*hurwitz(a, b)), (a, b))
            self.assertEqual(hurwitz(*hurwitz_inv(a, b)), (a, b))
            self.assertEqual(mul(*hurwitz(a, b)), mul(a, b))

    def test_hurwitz_group_yb_all_triples(self):
        for t in product(S3, repeat=3):
            self.assertEqual(word(hurwitz, (0, 1, 0), t), word(hurwitz, (1, 0, 1), t))

    def test_hurwitz_group_list_product_all_ranks_up_to_four(self):
        for size in range(1, 5):
            for xs in product(S3, repeat=size):
                for i in range(size-1):
                    self.assertEqual(group_product(step(hurwitz, i, xs)), group_product(xs))

    def test_hurwitz_reversible_not_involutive(self):
        self.assertTrue(any(hurwitz(*hurwitz(a, b)) != (a, b) for a, b in product(S3, repeat=2)))

    def test_same_product_not_same_factorization(self):
        pairs = [(a, b) for a, b in product(S3, repeat=2) if hurwitz(a, b) != (a, b)]
        self.assertTrue(pairs)
        a, b = pairs[0]
        self.assertEqual(mul(*hurwitz(a, b)), mul(a, b))

    def test_actual_history_and_state_slots_are_distinct(self):
        # Event occurrences are only permuted; coefficient values can change or be lost.
        events, coeffs = ("e", "f", "g"), (0, 1, 0)
        for i in (0, 1, 0):
            events = step(FLIP, i, events)
            coeffs = checked(COPY, 2, i, coeffs)
        self.assertEqual(events, ("g", "f", "e"))
        self.assertEqual(len(coeffs), len(events))
        self.assertEqual(set(events), {"e", "f", "g"})

    def test_positional_realization_for_arbitrary_finite_event_ranks(self):
        for size in range(2, 7):
            start = tuple(range(size))
            for indices in product(range(size-1), repeat=3):
                end = word(FLIP, indices, start)
                self.assertEqual(sorted(end), list(start))
                self.assertEqual(len(end), size)

    def test_operator_word_composition(self):
        for op in (COPY, FLIP, TOGGLE):
            for xs in TRIPLES:
                for left, right in product(product(range(2), repeat=2), repeat=2):
                    self.assertEqual(word(op, left+right, xs), word(op, right, word(op, left, xs)))


class IncrementContractChecks(unittest.TestCase):
    def test_preserved_i3_payload_and_explicit_root_migration(self):
        old = json.loads((ROOT/"verification/cx-i3/manifest.json").read_text())
        expected = old.get("files_sha256", old.get("files", {}))
        for path, digest in expected.items():
            data = (ROOT/path).read_bytes()
            if path == "CausalGeometry.lean":
                data = project_i3_root(data.decode()).encode()
            if isinstance(digest, dict):
                digest = digest["sha256"]
            self.assertEqual(hashlib.sha256(data).hexdigest(), digest, path)

    def test_all_modules_once_and_concurrent_imports_retained(self):
        root = (ROOT/"CausalGeometry.lean").read_text()
        for m in MODULES:
            self.assertEqual(root.count("import CausalGeometry."+m+"\n"), 1)
        for line in CONCURRENT_IMPORTS:
            self.assertEqual(root.count(line), 1)

    def test_sized_api_and_slot_hypothesis_present(self):
        s = (ROOT/"CausalGeometry/Exchange/LocalOperator.lean").read_text()
        self.assertIn("i + 3 ≤ xs.length", s)
        self.assertIn("i : Fin n", s)
        self.assertIn("Sized A (n + 1)", s)
        self.assertIn("Function.LeftInverse", s)

    def test_native_presentations_reuse_quotient(self):
        s = (ROOT/"CausalGeometry/Exchange/ArtinPresentation.lean").read_text()
        for name in ("CategoryTheory.Paths", "CategoryTheory.Quotient", "Coherence.descend",
                     "Coherence.compare", "operator_respects", "SymmetricRelation"):
            self.assertIn(name, s)
        self.assertNotRegex(s, r"(?:inductive|structure)\s+(?:Category|Quotient|Functor)\b")

    def test_real_causal_source_not_a_word_alias(self):
        s = (ROOT/"CausalGeometry/Exchange/CausalArtin.lean").read_text()
        for name in ("path : CausalPath", "s.position_bound", "length_eq", "realization_square"):
            self.assertIn(name, s)
        c = (ROOT/"CausalGeometry/Exchange/CausalOperator.lean").read_text()
        self.assertIn("s.length_eq", c)
        self.assertIn("Reversible.extend", c)

    def test_hurwitz_general_group_proof_and_internal_consumer(self):
        s = (ROOT/"CausalGeometry/Models/ExchangeOperatorControls.lean").read_text()
        for name in ("[Group G]", "hurwitz_yb", "causal_hurwitz_product", "toggle_causal_separates",
                     "invalid_slot_breaks_braid"):
            self.assertIn(name, s)

    def test_no_forbidden_shortcuts_or_downstream_import(self):
        for m in MODULES:
            s = (ROOT/"CausalGeometry"/(m.replace(".", "/")+".lean")).read_text()
            s = re.sub(r"/-.*?-/", "", s, flags=re.S)
            s = re.sub(r"--[^\n]*", "", s)
            self.assertNotRegex(s, r"\b(sorry|admit|native_decide|unsafe)\b|(?m:^\s*axiom\b)")
            self.assertNotRegex(s, r"(?m)^import (GenContinuum|ECIA|RenormCore)\b")

    def test_kernel_audit_contains_general_and_finite_obligations(self):
        s = (ROOT/"verification/cx-i4/KernelAudit.lean").read_text()
        for name in ("stepList_braid", "operator_respects", "realization_square", "causal_hurwitz_product"):
            self.assertIn(name, s)
        self.assertGreaterEqual(s.count("#print axioms"), 30)


def load_tests(loader, tests, pattern):
    data = project_i3_root((ROOT/"CausalGeometry.lean").read_text()).encode()
    manifest = json.loads((ROOT/"verification/cx-i3/manifest.json").read_text())
    files = manifest.get("files_sha256", manifest.get("files", {}))
    digest = files["CausalGeometry.lean"]
    if isinstance(digest, dict):
        digest = digest["sha256"]
    if hashlib.sha256(data).hexdigest() != digest:
        raise ValueError("root projection does not equal the exact I3 source")
    temp = tempfile.TemporaryDirectory(prefix="cx-i4-i3-")
    atexit.register(temp.cleanup)
    view = Path(temp.name)
    for name in ("CausalGeometry", "verification", "tests", "tools"):
        (view/name).symlink_to(ROOT/name, target_is_directory=True)
    (view/"CausalGeometry.lean").write_bytes(data)
    spec = importlib.util.spec_from_file_location("cx_i3_unchanged_regression", ROOT/"tests/test_cx_i3.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.ROOT = view
    tests.addTests(loader.loadTestsFromModule(module))
    return tests


if __name__ == "__main__":
    unittest.main(verbosity=2)
