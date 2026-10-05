import contextlib
import importlib.util
import io
import itertools
import json
from pathlib import Path
import sys
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from verification.verify import rows_from_histogram, snapshot_row, validate_histogram, verify_package

spec = importlib.util.spec_from_file_location('original_enumerator', ROOT / 'verification_program_CCdominance.py')
original = importlib.util.module_from_spec(spec)
spec.loader.exec_module(original)


class VerificationTests(unittest.TestCase):
    def test_original_oracle_against_exhaustive_subsets(self):
        sequences = {1: 'A395684', 2: 'A395691', 3: 'A395692', 4: 'A395693', 5: 'A395694'}
        for n in range(1, 7):
            edges = list(itertools.combinations(range(n), 2))
            edge_index = {uv: i for i, uv in enumerate(edges)}
            requirements = []
            for k in range(n, 0, -1):
                for vertices in itertools.combinations(range(n), k):
                    required = sum(1 << edge_index[uv] for uv in itertools.combinations(vertices, 2))
                    requirements.append((k, required))
            rows = {p: [0] * n for p in sequences}
            for mask in range(1 << len(edges)):
                present = [uv for i, uv in enumerate(edges) if mask & (1 << i)]
                expected = next(k for k, required in requirements if mask & required == required)
                self.assertEqual(original.max_clique_size(n, present), expected, (n, mask))
                for p in rows:
                    rows[p][expected - 1] += p ** len(present)
            for p, sequence in sequences.items():
                self.assertEqual(rows[p], snapshot_row(sequence, n))

    def test_cumulative_reporting_and_real_reference_comparison(self):
        output = io.StringIO()
        with mock.patch.multiple(original, P=1, N_LIST=[3], CUMULATIVE=True):
            with contextlib.redirect_stdout(output):
                original.main()
        text = output.getvalue()
        self.assertIn('Final cumulative entry: 8', text)
        self.assertIn('Matches stored A395695 row n=3 term by term.', text)
        self.assertNotIn('Row sum: 16', text)

    def test_correct_total_does_not_hide_wrong_clique_buckets(self):
        with mock.patch.object(original, 'max_clique_size', return_value=1):
            with contextlib.redirect_stdout(io.StringIO()):
                counts = original.compute_dp(1, 4)
        self.assertEqual(sum(counts.values()), 64)
        with self.assertRaises(AssertionError):
            original.compare_to_oeis_snapshot(1, 4, [counts.get(k, 0) for k in range(1, 5)])

    def test_histogram_classifier_corruption_is_detected(self):
        receipt = json.loads((ROOT / 'verification/results/census_n7_subset.json').read_text())
        hist = receipt['histogram_by_clique_then_edges']
        hist[2][1] -= 1
        hist[1][1] += 1
        validate_histogram(hist, 7)  # Edge marginals and total remain unchanged.
        with self.assertRaises(AssertionError):
            rows_from_histogram(hist, 7)

    def test_recorded_package_and_unavailable_reference(self):
        self.assertEqual(verify_package()['all_six_sequences_matched_through_n'], 8)
        self.assertIsNone(original.compare_to_oeis_snapshot(2, 3, [1, 19, 27], cumulative=True))


if __name__ == '__main__':
    unittest.main()
