# Reference snapshots

The six files in `oeis_bfiles/` are public OEIS snapshots accessed on October 5,
2026. Their URLs, term counts and SHA-256 digests are recorded in
[`provenance.json`](provenance.json). The source headers are retained. A395695's
bfile was synthesized by OEIS from its displayed entry.

Credit: **The On-Line Encyclopedia of Integer Sequences, The OEIS Foundation
Inc.**, [oeis.org](https://oeis.org/). Sequence attribution and links are in the
provenance file. Alejandro Zarzuelo Urdiales authored this family; Sean A.
Irvine and Pontus von Brömssen supplied independently computed extensions.

The OEIS content is distributed under
[CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/), following the
[OEIS End-User License Agreement](https://oeis.org/wiki/The_OEIS_End-User_License_Agreement).
This attribution and license apply to these reference snapshots. The local
files do not modify the public entries.

The independently recorded census results are in `verification/results/`.
All six sequences are checked term by term through eight vertices. For larger
stored rows, the verifier checks totals, endpoints and the next-to-diagonal
formula; it does not claim exhaustive recomputation of their interior terms.
