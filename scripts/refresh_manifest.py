"""Refresh or check the SHA-256 manifest for the public verification package."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / 'verification' / 'manifest.json'


def entries():
    files = [ROOT / 'verification_program_CCdominance.py']
    for folder in ['data', 'verification', 'scripts']:
        files += [p for p in (ROOT / folder).rglob('*') if p.is_file() and p != MANIFEST
                  and '__pycache__' not in p.parts and p.suffix != '.pyc']
    return {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(set(files))}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    current = entries()
    if args.check:
        stored = json.loads(MANIFEST.read_text(encoding='utf-8'))['files']
        if current != stored:
            changed = sorted(k for k in current.keys() | stored.keys() if current.get(k) != stored.get(k))
            raise SystemExit('Manifest mismatch: ' + ', '.join(changed))
        print(f'Verification manifest matches all {len(current)} files.')
    else:
        MANIFEST.write_text(json.dumps({'algorithm': 'SHA-256', 'files': current}, indent=2) + '\n', encoding='utf-8', newline='\n')
        print(f'Wrote verification manifest for {len(current)} files.')
