"""Finite mathematical and source-reuse checks. These do not elaborate Lean."""
from __future__ import annotations

import hashlib
import itertools
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
MODULES = [
    "History.Composition", "History.DiamondPaths", "History.EventList",
    "Exchange.Basic", "Exchange.Path", "Exchange.Variational",
    "Models.ExchangeThreeEvents",
]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def git_blob(s: str) -> str:
    data = s.encode()
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def enabled(done, event, predecessors=(), conflicts=()):
    return (event not in done
            and all(a in done for a, b in predecessors if b == event)
            and all(not (a == event and b in done or b == event and a in done)
                    for a, b in conflicts))


def valid(history, predecessors=(), conflicts=()):
    done = set()
    for event in history:
        if not enabled(done, event, predecessors, conflicts):
            return False
        done.add(event)
    return True


def exchange(history, position, predecessors=(), conflicts=()):
    if not 0 <= position < len(history)-1 or not valid(history, predecessors, conflicts):
        raise ValueError("invalid source history or exchange position")
    done = set(history[:position])
    a, b = history[position:position+2]
    if a == b or not enabled(done, a, predecessors, conflicts) or not enabled(done, b, predecessors, conflicts):
        raise ValueError("not a concurrent pair")
    result = history[:position] + (b, a) + history[position+2:]
    if not valid(result, predecessors, conflicts):
        raise ValueError("invalid target history")
    return result


def route(history, positions, predecessors=(), conflicts=()):
    for position in positions:
        history = exchange(history, position, predecessors, conflicts)
    return history


def observe(positions, offset, value):
    for position in positions:
        value = (-value if position % 2 == 0 else offset-value) % 5
    return value


def action(history, lagrangian):
    done, value = set(), 0
    for event in history:
        value += lagrangian(frozenset(done), event)
        done.add(event)
    return value


class FiniteCausalChecks(unittest.TestCase):
    def test_six_actual_histories(self):
        histories = list(itertools.permutations(range(3)))
        self.assertEqual(len(histories), 6)
        self.assertTrue(all(valid(p) for p in histories))

    def test_twelve_witnessed_edges(self):
        edges = [(p, i, exchange(p, i)) for p in itertools.permutations(range(3)) for i in range(2)]
        self.assertEqual(len(edges), 12)
        self.assertTrue(all(set(p) == set(q) and len(p) == len(q) for p, _, q in edges))

    def test_routes_have_same_endpoints(self):
        self.assertEqual(route((0, 1, 2), (0, 1, 0)), (2, 1, 0))
        self.assertEqual(route((0, 1, 2), (1, 0, 1)), (2, 1, 0))

    def test_dependency_rejected(self):
        self.assertTrue(valid((0, 1, 2), ((0, 1),)))
        with self.assertRaises(ValueError):
            exchange((0, 1, 2), 0, ((0, 1),))

    def test_conflict_rejected(self):
        with self.assertRaises(ValueError):
            exchange((0, 1, 2), 0, conflicts=((0, 1),))

    def test_repeated_occurrence_rejected(self):
        self.assertFalse(valid((0, 0)))
        with self.assertRaises(ValueError):
            exchange((0, 0), 0)

    def test_bad_position_rejected(self):
        for i in (-1, 2, 3):
            with self.assertRaises(ValueError):
                exchange((0, 1, 2), i)

    def test_prefix_and_suffix_contexts(self):
        for p in itertools.permutations(range(3)):
            for i in range(2):
                self.assertEqual(exchange((3,) + p + (4,), i+1), (3,) + exchange(p, i) + (4,))

    def test_all_reflections_involutive(self):
        for t, m, i in itertools.product(range(5), range(5), range(2)):
            self.assertEqual(observe((i, i), t, m), m)

    def test_all_observer_formulas(self):
        for t, m in itertools.product(range(5), repeat=2):
            self.assertEqual(observe((0, 1, 0), t, m), (-t-m) % 5)
            self.assertEqual(observe((1, 0, 1), t, m), (2*t-m) % 5)

    def test_three_four_discriminator(self):
        self.assertEqual((observe((0, 1, 0), 2, 0), observe((1, 0, 1), 2, 0)), (3, 4))

    def test_zero_offset_same_type_control(self):
        for m in range(5):
            self.assertEqual(observe((0, 1, 0), 0, m), observe((1, 0, 1), 0, m))

    def test_only_zero_offset_collapses_the_pair(self):
        for t in range(5):
            self.assertEqual(all(observe((0, 1, 0), t, m) == observe((1, 0, 1), t, m)
                                 for m in range(5)), t == 0)

    def test_contextual_action_defect(self):
        L = lambda c, e: e*(len(c)+1) + sum(c)
        for p in itertools.permutations(range(4)):
            for i in range(3):
                q = exchange(p, i)
                c, a, b = frozenset(p[:i]), p[i], p[i+1]
                square = L(c, a) + L(c | {a}, b) - L(c, b) - L(c | {b}, a)
                self.assertEqual(action(p, L)-action(q, L), square)

    def test_stationary_action_on_all_histories(self):
        B = lambda c: sum(c)**2
        L = lambda c, e: e+1+B(c | {e})-B(c)
        values = {action(p, L) for p in itertools.permutations(range(4))}
        self.assertEqual(len(values), 1)

    def test_nonstationary_action_not_promoted(self):
        L = lambda c, e: e*(len(c)+1)
        self.assertNotEqual(action((0, 1, 2), L), action((1, 0, 2), L))


class SourceReuseChecks(unittest.TestCase):
    def test_composition_exact_relocation(self):
        producer = text("CausalGeometry/History/Composition.lean")
        block = producer.split("namespace CausalPath\n\n", 1)[1].split("@[simp] theorem comp_nil", 1)[0]
        current = text("CausalGeometry/Variational/DiscreteAction.lean")
        old = current.replace("import CausalGeometry.History.Composition", "import CausalGeometry.History.Path", 1)
        old = old.replace("/-- Local discrete causal Lagrangian", "namespace CausalPath\n\n" + block + "end CausalPath\n\n/-- Local discrete causal Lagrangian", 1)
        self.assertEqual(git_blob(old), "b79c34284030ef9945b123b261997b995c4ce7c8")

    def test_diamond_relocation_and_single_proof_repair(self):
        producer = text("CausalGeometry/History/DiamondPaths.lean")
        block = producer.split("namespace CausalVariational\n\n", 1)[1].split("\nend CausalVariational", 1)[0]
        current = text("CausalGeometry/Variational/ElementaryEulerLagrange.lean")
        old = current.replace("import CausalGeometry.History.DiamondPaths", "import CausalGeometry.History.PathEquivariance", 1)
        old = old.replace("  simp only [pathAction_step, pathAction_nil, add_zero, squareActionDefect]", "  rfl", 1)
        old = old.replace("/-- The local square-action defect", block.rstrip()+"\n\n/-- The local square-action defect", 1)
        self.assertEqual(git_blob(old), "a12119debe90b78f985029de54bc6d149d8d7215")

    def test_root_only_appends_new_modules(self):
        suffix = "\n" + "".join(f"import CausalGeometry.{m}\n" for m in MODULES)
        root = text("CausalGeometry.lean")
        self.assertTrue(root.endswith(suffix))
        self.assertEqual(git_blob(root[:-len(suffix)]), "03f949dba89d35432f2daa5e2068014f485a5a30")

    def test_all_new_modules_exist_and_imported(self):
        root = text("CausalGeometry.lean").splitlines()
        for module in MODULES:
            self.assertTrue((ROOT / "CausalGeometry" / (module.replace(".", "/")+".lean")).is_file())
            self.assertEqual(root.count("import CausalGeometry."+module), 1)

    def test_no_downstream_import(self):
        for module in MODULES:
            source = text("CausalGeometry/"+module.replace(".", "/")+".lean")
            self.assertNotRegex(source, r"(?m)^import (GenContinuum|ECIA|RenormCore)\b")

    def test_native_path_universality_reused(self):
        source = text("CausalGeometry/Exchange/Path.lean")
        self.assertIn("Quiver.Path p q", source)
        self.assertIn("CategoryTheory.Paths.lift_unique", source)
        self.assertNotRegex(source, r"inductive\s+Route")

    def test_no_forbidden_proof_shortcuts_in_changed_sources(self):
        files = [ROOT / "CausalGeometry" / (m.replace(".", "/")+".lean") for m in MODULES]
        files += list((ROOT / "CausalGeometry/Variational").glob("*.lean"))
        for path in files:
            # Narrow increment scan; the repository's native audit is also run by the full runner.
            stripped = re.sub(r"/-.*?-/", "", path.read_text(), flags=re.S)
            stripped = re.sub(r"--[^\n]*", "", stripped)
            self.assertNotRegex(stripped, r"\b(sorry|admit|native_decide|unsafe)\b|(?m:^\s*axiom\b)")

    def test_legacy_variational_consumers_remain(self):
        source = text("CausalGeometry/Exchange/Variational.lean")
        self.assertIn("actionDifference_diamondPaths", source)
        self.assertIn("hEL : ElementaryEulerLagrange L", source)
        self.assertIn("ih.trans", source)

    def test_audit_includes_source_and_historical_theorems(self):
        source = text("verification/cx-i1/KernelAudit.lean")
        self.assertEqual(source.count("#print axioms "), 22)
        for name in ["routes_distinct", "observed_three_four", "Route.preservesAction", "elementaryEulerLagrange_addBoundary_iff"]:
            self.assertIn(name, source)


if __name__ == "__main__":
    unittest.main(verbosity=2)
