"""CX-I2 finite quotient controls and unchanged CX-I1 regression projection.

These tests do not elaborate Lean. The exhaustive finite model uses one
length-preserving named equation; it is not a general word-problem solver.
"""
from __future__ import annotations
import atexit
from functools import lru_cache
import hashlib
import importlib.util
from itertools import permutations, product
import json
from pathlib import Path
import re
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
NEW_MODULES = ["Exchange.Quotient", "Exchange.ContextRelation", "Models.ExchangeCoherenceControls"]
SUFFIX = "\n" + "".join(f"import CausalGeometry.{m}\n" for m in NEW_MODULES)
START = (0, 1, 2)
P, Q = (0, 1, 0), (1, 0, 1)


def act(start, word):
    current = list(start)
    for i in word:
        if i not in (0, 1):
            raise ValueError("exchange outside the three-event domain")
        current[i], current[i+1] = current[i+1], current[i]
    return tuple(current)


def observe(word, offset, x):
    for i in word:
        x = (-x if i % 2 == 0 else offset-x) % 5
    return x


def neighbours(start, word):
    """One native-composition-context instance of the NAMED relation at START."""
    state = start
    for i in range(len(word)):
        window = word[i:i+3]
        if state == START and window in (P, Q):
            replacement = Q if window == P else P
            yield word[:i] + replacement + word[i+3:]
        state = act(state, word[i:i+1])


@lru_cache(None)
def component(start, word):
    """Exact for this finite length sector: every rule preserves word length."""
    seen, queue = {word}, [word]
    while queue:
        for other in neighbours(start, queue.pop()):
            if other not in seen:
                seen.add(other)
                queue.append(other)
    return frozenset(seen)


def bounded_search(start, source, target, max_nodes):
    """A bounded positive search: exhaustion is never reported as inequality."""
    seen, queue, expanded = {source}, [source], 0
    while queue and expanded < max_nodes:
        current = queue.pop()
        if current == target:
            return "EQUAL"
        expanded += 1
        for other in neighbours(start, current):
            if other not in seen:
                seen.add(other)
                queue.append(other)
    return "INCONCLUSIVE"


class QuotientFiniteChecks(unittest.TestCase):
    def test_raw_routes_are_distinct_with_same_target(self):
        self.assertNotEqual(P, Q)
        self.assertEqual(act(START, P), act(START, Q))

    def test_named_pair_identified_and_reflexive(self):
        self.assertIn(Q, component(START, P))
        self.assertIn(P, component(START, P))

    def test_empty_policy_does_not_identify(self):
        self.assertNotIn(Q, {P})

    def test_relation_is_not_universal_yang_baxter(self):
        other_start = (1, 0, 2)
        self.assertEqual(act(other_start, P), act(other_start, Q))
        self.assertNotIn(Q, component(other_start, P))

    def test_all_generated_steps_preserve_start_end_and_length(self):
        count = 0
        for start in permutations(range(3)):
            for n in range(7):
                for word in product(range(2), repeat=n):
                    for other in neighbours(start, word):
                        count += 1
                        self.assertEqual(len(word), len(other))
                        self.assertEqual(act(start, word), act(start, other))
                        self.assertIn(word, set(neighbours(start, other)))
        # Each window has two orientations; its prefix determines one starting permutation.
        self.assertEqual(count, sum((n-2) * 2**(n-2) for n in range(3, 7)))

    def test_equivalence_classes_are_equal_for_related_words(self):
        for n in range(7):
            for word in product(range(2), repeat=n):
                c = component(START, word)
                for other in c:
                    self.assertEqual(c, component(START, other))

    def test_composition_contexts_preserve_generated_pair(self):
        for start in permutations(range(3)):
            for n in range(5):
                for prefix in product(range(2), repeat=n):
                    if act(start, prefix) != START:
                        continue
                    for m in range(3):
                        for suffix in product(range(2), repeat=m):
                            self.assertIn(prefix+Q+suffix, component(start, prefix+P+suffix))

    def test_only_zero_offset_respects_generating_equation(self):
        for offset in range(5):
            same = all(observe(P, offset, x) == observe(Q, offset, x) for x in range(5))
            self.assertEqual(same, offset == 0)

    def test_zero_offset_respects_all_finite_generated_classes(self):
        for n in range(7):
            for word in product(range(2), repeat=n):
                for other in component(START, word):
                    for x in range(5):
                        self.assertEqual(observe(word, 0, x), observe(other, 0, x))

    def test_invertible_boundary_relabelling_cannot_fix_offset_two(self):
        # 120 source and 120 target relabellings; the same ones act on both routes.
        for a in permutations(range(5)):
            for b in permutations(range(5)):
                left = tuple(b[observe(P, 2, a[x])] for x in range(5))
                right = tuple(b[observe(Q, 2, a[x])] for x in range(5))
                self.assertNotEqual(left, right)

    def test_three_and_five_exchanges_not_identified(self):
        longer = (0, 0)+P
        self.assertEqual(act(START, P), act(START, longer))
        self.assertNotIn(longer, component(START, P))
        self.assertNotEqual(len(P), len(longer))

    def test_no_inverse_cancellation_imposed(self):
        self.assertEqual(act(START, (0, 0)), START)
        self.assertNotIn((), component(START, (0, 0)))

    def test_causal_history_contexts_shift_positions_not_route_count(self):
        for prefix_length in range(5):
            p = tuple(i+prefix_length for i in P)
            q = tuple(i+prefix_length for i in Q)
            for offset, x in product(range(5), repeat=2):
                self.assertEqual(observe(p, offset, x) == observe(q, offset, x), offset == 0)
            self.assertEqual(len(p), len(q))

    def test_more_relations_can_only_merge_classes(self):
        for n in range(6):
            for word in product(range(2), repeat=n):
                generated = component(START, word)
                universal_parallel = {w for w in product(range(2), repeat=n)
                                      if act(START, w) == act(START, word)}
                self.assertLessEqual({word}, generated)
                self.assertLessEqual(generated, universal_parallel)

    def test_nonrespecting_observer_is_not_declared_well_defined(self):
        values = {observe(w, 2, 0) for w in component(START, P)}
        self.assertEqual(values, {3, 4})

    def test_bounded_search_does_not_promote_exhaustion(self):
        self.assertEqual(bounded_search(START, P, Q, 1), "INCONCLUSIVE")
        self.assertEqual(bounded_search(START, P, Q, 3), "EQUAL")
        self.assertEqual(bounded_search(START, P, (0, 0)+P, 100), "INCONCLUSIVE")


class SourceContractChecks(unittest.TestCase):
    def test_all_i1_payload_files_unchanged_except_append_only_root(self):
        manifest = json.loads((ROOT/"verification/cx-i1/manifest.json").read_text())
        for path, data in manifest["files"].items():
            content = (ROOT/path).read_bytes()
            if path == "CausalGeometry.lean":
                self.assertTrue(content.endswith(SUFFIX.encode()))
                content = content[:-len(SUFFIX.encode())]
            self.assertEqual(hashlib.sha256(content).hexdigest(), data["sha256"], path)

    def test_new_modules_imported_exactly_once(self):
        root = (ROOT/"CausalGeometry.lean").read_text().splitlines()
        for m in NEW_MODULES:
            self.assertEqual(root.count("import CausalGeometry."+m), 1)
            self.assertTrue((ROOT/"CausalGeometry"/(m.replace(".", "/")+".lean")).is_file())

    def test_native_quotient_and_uniqueness_reused(self):
        source = (ROOT/"CausalGeometry/Exchange/Quotient.lean").read_text()
        for api in ("Quotient.lift", "Quotient.lift_unique", "Quotient.functor_map_eq_iff",
                    "Quotient.functor_homRel_eq_compClosure_eqvGen"):
            self.assertIn(api, source)
        self.assertNotRegex(source, r"(?:inductive|structure)\s+(?:Quotient|Congruence)\b")

    def test_contexts_are_not_only_route_composition(self):
        source = (ROOT/"CausalGeometry/Exchange/ContextRelation.lean").read_text()
        for s in ("prefixFunctor r", "suffixFunctor r", "saturated_contextClosed",
                  "saturated_le", "prefixOnQuotient_square", "suffixOnQuotient_square"):
            self.assertIn(s, source)

    def test_up_to_iso_not_only_strict_descent(self):
        source = (ROOT/"CausalGeometry/Exchange/Quotient.lean").read_text()
        self.assertIn("respects_iff_factorsUpToIso", source)
        self.assertIn("cancel_epi", source)
        model = (ROOT/"CausalGeometry/Models/ExchangeCoherenceControls.lean").read_text()
        self.assertIn("offset_two_no_factor_upToIso", model)

    def test_no_downstream_or_forbidden_proof_shortcuts(self):
        for m in NEW_MODULES:
            content = (ROOT/"CausalGeometry"/(m.replace(".", "/")+".lean")).read_text()
            stripped = re.sub(r"/-.*?-/", "", content, flags=re.S)
            stripped = re.sub(r"--[^\n]*", "", stripped)
            self.assertNotRegex(stripped, r"\b(sorry|admit|native_decide|unsafe)\b|(?m:^\s*axiom\b)")
            self.assertNotRegex(stripped, r"(?m)^import (GenContinuum|ECIA|RenormCore)\b")

    def test_kernel_audit_covers_new_and_old_consumers(self):
        source = (ROOT/"verification/cx-i2/KernelAudit.lean").read_text()
        self.assertEqual(source.count("#print axioms "), 36)
        for t in ("respects_iff_factorsUpToIso", "saturated_le", "factors_iff_zero",
                  "longerRoute_not_identified", "Exchange.Route.preservesAction"):
            self.assertIn(t, source)


def load_tests(loader, tests, pattern):
    """Replay unchanged I1 tests after proving the exact append-only root projection.

The producer files are symlinked to the CURRENT files, not historical copies.
Only the root import list is projected to the SHA-pinned I1 prefix; the new
suite independently checks the full current import list and all hashes.
"""
    root_bytes = (ROOT/"CausalGeometry.lean").read_bytes()
    if not root_bytes.endswith(SUFFIX.encode()):
        raise ValueError("unrecognized root migration; refusing historical projection")
    projected = root_bytes[:-len(SUFFIX.encode())]
    manifest = json.loads((ROOT/"verification/cx-i1/manifest.json").read_text())
    if hashlib.sha256(projected).hexdigest() != manifest["files"]["CausalGeometry.lean"]["sha256"]:
        raise ValueError("root prefix does not match the exact I1 producer")
    temp = tempfile.TemporaryDirectory(prefix="cx-i2-i1-regression-")
    atexit.register(temp.cleanup)
    view = Path(temp.name)
    for name in ("CausalGeometry", "verification", "tests", "tools"):
        (view/name).symlink_to(ROOT/name, target_is_directory=True)
    (view/"CausalGeometry.lean").write_bytes(projected)
    spec = importlib.util.spec_from_file_location("cx_i1_unchanged_regression", ROOT/"tests/test_cx_i1.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.ROOT = view
    tests.addTests(loader.loadTestsFromModule(module))
    return tests


if __name__ == "__main__":
    unittest.main(verbosity=2)
