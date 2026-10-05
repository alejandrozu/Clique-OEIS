"""Validate stored independent censuses against the actual six OEIS snapshots.

Requires Python 3.10+ and only the standard library. Decimal values are parsed
as Python integers. This validates evidence files; census.js recomputes them.
"""
import argparse
import hashlib
import json
from math import comb
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EXACT = {1: 'A395684', 2: 'A395691', 3: 'A395692', 4: 'A395693', 5: 'A395694'}
CUMULATIVE = 'A395695'


def load_snapshot(sequence):
    path = ROOT / 'data' / 'oeis_bfiles' / (sequence + '.txt')
    values = []
    for line in path.read_text(encoding='utf-8-sig').splitlines():
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        index, value = map(int, line.split())
        if index != len(values) + 1 or value < 0:
            raise AssertionError(f'{sequence}: invalid bfile row {line!r}')
        values.append(value)
    return values


def snapshot_row(sequence, n):
    if not isinstance(n, int) or n < 1:
        raise ValueError('n must be positive')
    values = load_snapshot(sequence)
    start, end = n * (n - 1) // 2, n * (n + 1) // 2
    if end > len(values):
        raise ValueError(f'{sequence}: no complete stored row n={n}')
    return values[start:end]


def assert_snapshot_row(sequence, n, actual):
    expected = snapshot_row(sequence, n)
    if list(actual) != expected:
        raise AssertionError(f'{sequence}, n={n}: computed {list(actual)}, expected {expected}')


def validate_histogram(hist, n):
    if not isinstance(n, int) or not 1 <= n <= 8:
        raise AssertionError('Evidence n must lie between 1 and 8')
    edges = comb(n, 2)
    if len(hist) != n + 1 or any(len(row) != edges + 1 for row in hist):
        raise AssertionError('Invalid histogram dimensions')
    if any(type(value) is not int or value < 0 for row in hist for value in row):
        raise AssertionError('Histogram entries must be nonnegative integers')
    if any(hist[0]):
        raise AssertionError('A nonempty vertex set cannot have clique number zero')
    if sum(map(sum, hist)) != 2 ** edges:
        raise AssertionError('Incorrect number of enumerated graphs')
    for e in range(edges + 1):
        if sum(row[e] for row in hist) != comb(edges, e):
            raise AssertionError(f'Incorrect edge marginal e={e}')


def rows_from_histogram(hist, n):
    validate_histogram(hist, n)
    rows = {}
    for p, sequence in EXACT.items():
        row = [sum(count * p ** e for e, count in enumerate(hist[k])) for k in range(1, n + 1)]
        assert_snapshot_row(sequence, n, row)
        if sum(row) != (p + 1) ** comb(n, 2):
            raise AssertionError(f'{sequence}: incorrect weighted total')
        rows[sequence] = row
    exact = rows[EXACT[1]]
    rows[CUMULATIVE] = [sum(exact[:k]) for k in range(1, n + 1)]
    assert_snapshot_row(CUMULATIVE, n, rows[CUMULATIVE])
    return rows


def verify_receipt(path):
    result = json.loads(Path(path).read_text(encoding='utf-8-sig'))
    n = result['n']
    hist = result['histogram_by_clique_then_edges']
    if result['graphs_enumerated'] != 2 ** comb(n, 2):
        raise AssertionError('Receipt graph count is incorrect')
    rows = rows_from_histogram(hist, n)
    if 'weighted_rows' in result:
        for p, sequence in EXACT.items():
            if [int(x) for x in result['weighted_rows'][str(p)]] != rows[sequence]:
                raise AssertionError('Receipt weighted row differs from its histogram')
    return hist, rows


def verify_snapshot_structure():
    provenance = json.loads((ROOT / 'data' / 'provenance.json').read_text())
    for source in provenance['sources']:
        contents = (ROOT / source['path']).read_bytes()
        if hashlib.sha256(contents).hexdigest() != source['sha256']:
            raise AssertionError(f"Snapshot digest changed: {source['sequence']}")
        if len(load_snapshot(source['sequence'])) != source['terms']:
            raise AssertionError('Snapshot term count changed')
    checked = 0
    for p, sequence in EXACT.items():
        max_n = 12 if p == 1 else 11
        if len(load_snapshot(sequence)) != max_n * (max_n + 1) // 2:
            raise AssertionError(f'{sequence}: incomplete snapshot')
        for n in range(1, max_n + 1):
            row, edges = snapshot_row(sequence, n), comb(n, 2)
            if sum(row) != (p + 1) ** edges or row[0] != 1 or row[-1] != p ** edges:
                raise AssertionError(f'{sequence}, n={n}: failed structural identity')
            if n >= 2:
                next_diagonal = n * p ** (edges - n + 1) * ((p + 1) ** (n - 1) - p ** (n - 1)) - edges * p ** (edges - 1)
                if row[-2] != next_diagonal:
                    raise AssertionError(f'{sequence}, n={n}: failed next-to-diagonal identity')
            checked += 1
    if len(load_snapshot(CUMULATIVE)) != 45:
        raise AssertionError('Incomplete cumulative snapshot')
    for n in range(1, 10):
        exact = snapshot_row(EXACT[1], n)
        assert_snapshot_row(CUMULATIVE, n, [sum(exact[:k]) for k in range(1, n + 1)])
    return checked


def verify_package(extra_census=None):
    structural_rows = verify_snapshot_structure()
    folder = ROOT / 'verification' / 'results'
    lower = json.loads((folder / 'original_oracle_n1_n6.json').read_text())
    if lower['graphs_checked'] != sum(2 ** comb(n, 2) for n in range(1, 7)):
        raise AssertionError('Lower-order oracle evidence graph count changed')
    for n in range(1, 7):
        for p, sequence in EXACT.items():
            assert_snapshot_row(sequence, n, lower['weighted_rows_by_n_then_p'][str(n)][str(p)])
    verify_receipt(folder / 'census_n7_subset.json')
    subset, _ = verify_receipt(folder / 'census_n8_subset.json')
    induced, _ = verify_receipt(folder / 'census_n8_induced.json')
    if induced != subset:
        raise AssertionError('The two independent eight-vertex histograms differ')
    portable, _ = verify_receipt(folder / 'census_n8_induced_node.json')
    if portable != subset:
        raise AssertionError('Portable Node census differs from recorded independent evidence')
    if extra_census:
        verify_receipt(extra_census)
    return {
        'all_six_sequences_matched_through_n': 8,
        'eight_vertex_graphs_in_each_independent_census': 2 ** 28,
        'independent_eight_vertex_histograms_identical': True,
        'exact_stored_rows_passing_structural_checks': structural_rows,
        'cumulative_stored_rows_matched': 9,
        'larger_interior_terms_exhaustively_recomputed': False,
        'extra_census_checked': bool(extra_census),
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--census', type=Path, help='Also validate a newly computed census JSON')
    parser.add_argument('--out', type=Path, help='Write verification summary JSON')
    args = parser.parse_args()
    summary = verify_package(args.census)
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(summary, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(summary, indent=2))
