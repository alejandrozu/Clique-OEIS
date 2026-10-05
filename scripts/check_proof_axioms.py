"""Check Lean's printed axiom dependencies against the standard allowlist."""
import argparse
from pathlib import Path
import re

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def check_output(text):
    declarations = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, flags=re.S)
    independent = re.findall(r"'([^']+)' does not depend on any axioms", text)
    if not declarations and not independent:
        raise AssertionError('No Lean axiom dependency output was found')
    for name, body in declarations:
        actual = {item.strip() for item in body.split(',') if item.strip()}
        if not actual <= ALLOWED:
            raise AssertionError(f'{name}: unexpected axiom dependencies {sorted(actual - ALLOWED)}')
    if 'sorryAx' in text:
        raise AssertionError('A proved result depends on an admitted proof')
    return len(declarations) + len(independent)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('log', type=Path)
    args = parser.parse_args()
    count = check_output(args.log.read_text(encoding='utf-8-sig'))
    print(f'All {count} printed declarations use only standard Lean foundations.')
