"""CX-I3 exact finite signed-path controls; not a Lean elaborator.

A letter remembers the identity of its positive directed edge AND a sign.
A positive edge in the opposite direction is not the negative of that edge.
The finite graph is the six-history submodel of CX-I1, not an asserted
classification of every Lean exchange witness.
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
MODULES = ["Exchange.Reversible", "Exchange.Defect", "Exchange.EquationFamily",
           "Models.ExchangeReversibleControls"]
SUFFIX = "\n" + "".join(f"import CausalGeometry.{m}\n" for m in MODULES)
VERTICES = tuple(permutations(range(3)))
START = (0, 1, 2)


def swap(src, i):
    if sorted(src) != [0, 1, 2] or i not in (0, 1):
        raise ValueError("not an admitted three-event adjacent exchange")
    dst = list(src)
    dst[i], dst[i+1] = dst[i+1], dst[i]
    return tuple(dst)


def ends(letter):
    src, i, sign = letter
    if sign not in (-1, 1):
        raise ValueError("invalid orientation")
    dst = swap(src, i)
    return (src, dst) if sign == 1 else (dst, src)


def inverse_letter(letter):
    src, i, sign = letter
    ends(letter)
    return src, i, -sign


def inverse(word):
    return tuple(inverse_letter(s) for s in reversed(word))


def endpoint(start, word):
    current = start
    for s in word:
        src, dst = ends(s)
        if src != current:
            raise ValueError("mismatched intermediate history")
        current = dst
    return current


def positive(start, positions):
    current, word = start, []
    for i in positions:
        word.append((current, i, 1))
        current = swap(current, i)
    return tuple(word)


def reduce_free(start, word):
    endpoint(start, word)
    stack = []
    for s in word:
        if stack and stack[-1] == inverse_letter(s):
            stack.pop()
        else:
            stack.append(s)
    return tuple(stack)


def arrows_from(start):
    # Positive generators with source start; negatives of generators with target start.
    return tuple((start, i, 1) for i in (0, 1)) + tuple((swap(start, i), i, -1) for i in (0, 1))


def words_from(start, length):
    if length == 0:
        yield ()
    else:
        for edge in arrows_from(start):
            for rest in words_from(ends(edge)[1], length-1):
                yield (edge,) + rest


def memory(word, t, m):
    for src, i, sign in word:
        ends((src, i, sign))
        # Each reflection is its own inverse. The sign must NOT be erased by other observers.
        m = (-m if i == 0 else t-m) % 5
    return m


def counter(word, z=0):
    return z + sum(sign for _, _, sign in word)


P = positive(START, (0, 1, 0))
Q = positive(START, (1, 0, 1))
F = P[0]
BACK = (ends(F)[1], 0, 1)
OMEGA = P + inverse(Q)


class SignedPathChecks(unittest.TestCase):
    def test_edge_identity_sign_and_endpoints(self):
        letters = {e for v in VERTICES for e in arrows_from(v)}
        self.assertEqual(len(letters), 24)
        for e in letters:
            self.assertEqual(ends(inverse_letter(e)), ends(e)[::-1])
            self.assertEqual(inverse_letter(inverse_letter(e)), e)

    def test_bad_sign_and_context_rejected(self):
        for sign in (0, 2):
            with self.assertRaises(ValueError):
                ends((START, 0, sign))
        with self.assertRaises(ValueError):
            endpoint(START, (BACK,))

    def test_exact_bounded_corpus_size(self):
        n = sum(1 for v in VERTICES for ell in range(5) for _ in words_from(v, ell))
        self.assertEqual(n, 6*sum(4**ell for ell in range(5)))
        self.assertEqual(n, 2046)

    def test_inverse_route_has_reversed_endpoints(self):
        for v in VERTICES:
            for word in words_from(v, 4):
                target = endpoint(v, word)
                self.assertEqual(endpoint(target, inverse(word)), v)

    def test_both_formal_inverse_cancellations(self):
        for v in VERTICES:
            for word in words_from(v, 4):
                self.assertEqual(reduce_free(v, word + inverse(word)), ())
                self.assertEqual(reduce_free(endpoint(v, word), inverse(word) + word), ())

    def test_reduction_is_idempotent_and_preserves_endpoints(self):
        for v in VERTICES:
            for word in words_from(v, 4):
                r = reduce_free(v, word)
                self.assertEqual(reduce_free(v, r), r)
                self.assertEqual(endpoint(v, word), endpoint(v, r))

    def test_opposite_generator_is_not_formal_inverse(self):
        self.assertEqual(ends(BACK), ends(inverse_letter(F)))
        self.assertNotEqual(BACK, inverse_letter(F))
        self.assertNotEqual(reduce_free(ends(F)[1], (BACK,)), reduce_free(ends(F)[1], (inverse_letter(F),)))
        self.assertEqual((counter((BACK,)), counter((inverse_letter(F),))), (1, -1))

    def test_positive_roundtrip_is_not_cancelled(self):
        self.assertEqual(endpoint(START, (F, BACK)), START)
        self.assertEqual(reduce_free(START, (F, BACK)), (F, BACK))
        self.assertEqual(counter((F, BACK)), 2)

    def test_ternary_routes_remain_distinct_with_inverses(self):
        self.assertEqual(endpoint(START, P), endpoint(START, Q))
        self.assertNotEqual(reduce_free(START, P), reduce_free(START, Q))
        self.assertEqual((memory(P, 2, 0), memory(Q, 2, 0)), (3, 4))

    def test_defect_is_nontrivial_loop(self):
        self.assertEqual(endpoint(START, OMEGA), START)
        self.assertTrue(reduce_free(START, OMEGA))
        for t, m in product(range(5), repeat=2):
            self.assertEqual(memory(OMEGA, t, m), (m+3*t) % 5)
        self.assertEqual(counter(OMEGA), 0)  # counting cannot see this defect

    def test_defect_swap_is_inverse(self):
        self.assertEqual(inverse(OMEGA), Q+inverse(P))

    def test_defect_presentation_changes_by_conjugation(self):
        for old_source in VERTICES:
            for a in words_from(old_source, 3):
                if endpoint(old_source, a) != START:
                    continue
                for b in words_from(endpoint(START, P), 2):
                    lhs = a+P+b+inverse(a+Q+b)
                    rhs = a+OMEGA+inverse(a)
                    self.assertEqual(reduce_free(old_source, lhs), reduce_free(old_source, rhs))

    def test_observers_respect_free_reduction(self):
        for v in VERTICES:
            for word in words_from(v, 3):
                r = reduce_free(v, word)
                self.assertEqual(counter(word), counter(r))
                for t, m in product(range(5), repeat=2):
                    self.assertEqual(memory(word, t, m), memory(r, t, m))

    def test_reverse_pair_relation_respected_by_all_memories(self):
        for t, m in product(range(5), repeat=2):
            self.assertEqual(memory((BACK,), t, m), memory((inverse_letter(F),), t, m))
        self.assertNotEqual(counter((BACK,)), counter((inverse_letter(F),)))

    def test_all_parameters_classified_after_formal_inversion(self):
        for t in range(5):
            same = all(memory(P, t, m) == memory(Q, t, m) for m in range(5))
            trivial = all(memory(OMEGA, t, m) == m for m in range(5))
            self.assertEqual((same, trivial), (t == 0, t == 0))

    def test_reversal_relation_does_not_force_ternary(self):
        t = 2
        self.assertTrue(all(memory((BACK,), t, m) == memory((inverse_letter(F),), t, m) for m in range(5)))
        self.assertNotEqual(memory(P, t, 0), memory(Q, t, 0))

    def test_ternary_quotient_not_indiscrete(self):
        longer = (F, BACK)+P
        self.assertEqual(counter(P), counter(Q))
        self.assertEqual(endpoint(START, longer), endpoint(START, P))
        self.assertNotEqual(counter(longer), counter(P))

    def test_reverse_presentation_mutation_detected(self):
        # Wrong model equates every opposite-position positive generator to a formal negative.
        self.assertEqual(memory((F, BACK), 2, 0), 0)
        self.assertNotEqual(counter((F, BACK)), 0)


class SourceChecks(unittest.TestCase):
    def test_i2_payload_is_preserved_except_declared_root_suffix(self):
        payload = json.loads((ROOT/"verification/cx-i2/manifest.json").read_text())["files_sha256"]
        for path, expected in payload.items():
            data = (ROOT/path).read_bytes()
            if path == "CausalGeometry.lean":
                self.assertTrue(data.endswith(SUFFIX.encode()))
                data = data[:-len(SUFFIX.encode())]
            self.assertEqual(hashlib.sha256(data).hexdigest(), expected, path)

    def test_native_free_groupoid_is_consumed(self):
        source = (ROOT/"CausalGeometry/Exchange/Reversible.lean").read_text()
        for declaration in ("Quiver.FreeGroupoid.lift", "Quiver.FreeGroupoid.lift_unique",
                            "Quiver.freeGroupoidFunctor_comp", "positive_extend"):
            self.assertIn(declaration, source)
        self.assertNotRegex(source, r"(?:inductive|structure)\s+(?:FreeGroupoid|SignedPath)\b")

    def test_equations_are_typed_data_not_assumed_laws(self):
        source = (ROOT/"CausalGeometry/Exchange/EquationFamily.lean").read_text()
        for declaration in ("FamilyRelation", "family_respects_iff", "family_factors_iff",
                            "reverseGeneratorEquation", "respects_join_iff"):
            self.assertIn(declaration, source)
        self.assertNotIn("left_eq_right :", source)

    def test_kernel_harness_and_root_cover_increment(self):
        root = (ROOT/"CausalGeometry.lean").read_text().splitlines()
        for m in MODULES:
            self.assertEqual(root.count("import CausalGeometry."+m), 1)
        audit = (ROOT/"verification/cx-i3/KernelAudit.lean").read_text()
        self.assertGreaterEqual(audit.count("#print axioms "), 30)
        for theorem in ("reversible_routes_distinct", "opposite_generator_not_formal_inverse",
                        "reversal_only_preserves_ternary_defect", "ternary_quotient_not_indiscrete"):
            self.assertIn(theorem, audit)

    def test_axiom_hygiene_and_no_downstream_dependency(self):
        for m in MODULES:
            content = (ROOT/"CausalGeometry"/(m.replace(".", "/")+".lean")).read_text()
            stripped = re.sub(r"/-.*?-/", "", content, flags=re.S)
            stripped = re.sub(r"--[^\n]*", "", stripped)
            self.assertNotRegex(stripped, r"\b(sorry|admit|native_decide|unsafe)\b|(?m:^\s*axiom\b)")
            self.assertNotRegex(stripped, r"(?m)^import (GenContinuum|ECIA|RenormCore)\b")


def load_tests(loader, tests, pattern):
    """Replay the full I2 suite (including I1) against unchanged producer files.

    Only the append-only root is projected. Its exact I2 hash is checked first;
    all mathematical sources in the view are symlinks to the current files.
    """
    root = (ROOT/"CausalGeometry.lean").read_bytes()
    if not root.endswith(SUFFIX.encode()):
        raise ValueError("unrecognized root extension")
    prefix = root[:-len(SUFFIX.encode())]
    expected = json.loads((ROOT/"verification/cx-i2/manifest.json").read_text())["files_sha256"]["CausalGeometry.lean"]
    if hashlib.sha256(prefix).hexdigest() != expected:
        raise ValueError("root does not extend exact I2 prefix")
    tmp = tempfile.TemporaryDirectory(prefix="cx-i3-i2-regression-")
    atexit.register(tmp.cleanup)
    view = Path(tmp.name)
    for name in ("CausalGeometry", "verification", "tests", "tools"):
        (view/name).symlink_to(ROOT/name, target_is_directory=True)
    (view/"CausalGeometry.lean").write_bytes(prefix)
    spec = importlib.util.spec_from_file_location("cx_i2_unchanged_regression", ROOT/"tests/test_cx_i2.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.ROOT = view
    tests.addTests(loader.loadTestsFromModule(module))
    return tests


if __name__ == "__main__":
    unittest.main(verbosity=2)
