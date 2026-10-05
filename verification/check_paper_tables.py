"""Check the three retained LaTeX enumeration tables against OEIS fixtures."""
import re
from pathlib import Path
from verify import assert_snapshot_row

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / 'OEIS_Sequence_D_Dominance_Threshold_Corrected.tex'


def table_rows(body):
    rows = {}
    for line in body.split(r'\\'):
        line = re.sub(r'\\(?:toprule|midrule|bottomrule)', '', line).strip()
        if not re.fullmatch(r'\d+(?:\s*&\s*\d+)+', line):
            continue
        cells = [int(x.strip()) for x in line.split('&')]
        n = cells[0]
        if n in rows or len(cells) != n + 1:
            raise AssertionError(f'Duplicate or incomplete paper row n={n}')
        rows[n] = cells[1:]
    return rows


def check_tables():
    source = PAPER.read_text(encoding='utf-8')
    blocks = re.findall(r'\\begin\{tabular\}\{[^}]+\}(.*?)\\end\{tabular\}', source, flags=re.S)
    if len(blocks) != 3:
        raise AssertionError(f'Expected three retained enumeration tables, found {len(blocks)}')
    count = 0
    for body, sequence, max_n in zip(blocks, ['A395684', 'A395695', 'A395691'], [8, 8, 7]):
        rows = table_rows(body)
        if set(rows) != set(range(1, max_n + 1)):
            raise AssertionError(f'{sequence}: unexpected paper row range {sorted(rows)}')
        for n, row in rows.items():
            assert_snapshot_row(sequence, n, row)
            count += len(row)
    return count


if __name__ == '__main__':
    print(f'All {check_tables()} retained table entries match the actual OEIS snapshots.')
