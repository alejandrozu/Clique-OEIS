# Labeled graphs by clique number

Supporting paper, exact enumerations and Lean development for Alejandro
Zarzuelo Urdiales's OEIS family
[A395684](https://oeis.org/A395684) and
[A395691–A395695](https://oeis.org/A395691).

The finite enumerative results have been independently reproduced. An
author-initiated review dated **October 5, 2026** supplies corrections to
ancillary formulas, comparisons and the coding-threshold interpretation.
**No sequence counts change.** The revised paper includes the dated
corrigendum in Section 11.

- [Revised paper source](OEIS_Sequence_D_Dominance_Threshold_Corrected.tex)
  and [PDF](Dominance.pdf)
- [Corrigendum summary](CORRIGENDUM.md)
- [Reference data and attribution](data/README.md)
- [Recorded independent verification](verification/results/)

## The sequences

For labeled simple graphs on `[n]`, write `omega(G)` for clique number and
`e(G)` for the number of edges. Define

```text
d_p(n,k) = sum over G with omega(G)=k of p^e(G)
D_1(n,k) = sum over j<=k of d_1(n,j).
```

Each positive edge multiplicity has `p` choices, so `d_p` counts labeled
bounded-multiplicity graphs by the clique number of their underlying simple
graph. The exact row total is `(p+1)^binomial(n,2)`.

| OEIS entry | Distribution | Complete stored rows |
|---|---|---:|
| [A395684](https://oeis.org/A395684) | `d_1` | 12 |
| [A395691](https://oeis.org/A395691) | `d_2` | 11 |
| [A395692](https://oeis.org/A395692) | `d_3` | 11 |
| [A395693](https://oeis.org/A395693) | `d_4` | 11 |
| [A395694](https://oeis.org/A395694) | `d_5` | 11 |
| [A395695](https://oeis.org/A395695) | `D_1` | 9 |

## Reproduce the numerical checks

Use Python 3.10+ and Node.js 22+; no third-party numerical packages are
required. Run these commands from the repository root:

```sh
python scripts/refresh_manifest.py --check
python -m unittest discover -s verification/tests -v
node verification/test_census.js
python verification/verify.py
python verification/check_paper_tables.py
node verification/census.js --n 8 --algorithm induced --out work/census_n8.json
python verification/verify.py --census work/census_n8.json
python verification/check_decoder.py
```

The original Bron–Kerbosch clique oracle is checked against exhaustive
vertex-subset tests on all **33,867 graphs through six vertices**. Independent
seven- and eight-vertex censuses then check every term of all six sequences
through eight vertices. The eight-vertex run covers **268,435,456 graphs**.

Two independent methods are provided: descending clique-subset edge masks
(`--algorithm subset`) and an induced-subgraph clique recurrence
(`--algorithm induced`). The latter enumerates Gray-code base graphs and
every last-vertex neighborhood. Both produce the same complete `(omega,e)`
histogram; weights are evaluated with exact integers. An optional C# version
can be run with PowerShell 7 using `scripts/census_n8.ps1`.

The larger stored rows receive endpoint, total and next-to-diagonal checks.
Their interior terms are not claimed to have been exhaustively recomputed
in this review. All **100 retained entries** in the paper's three tables are
also compared against the snapshots.

`verification_program_CCdominance.py` retains the author's original counting
algorithm. Its reporting now compares computed terms with the reference
files and distinguishes a cumulative row's final entry from its row sum.

## Formal development

Lean and mathlib are pinned to **v4.19.0** by `lean-toolchain`, `lakefile.lean`
and `lake-manifest.json`. With [elan](https://github.com/leanprover/elan)
installed, run:

```sh
lake exe cache get
lake build --wfail
```

`DominanceThreshold.lean` proves the range of the genuine graph clique
number, empty and complete graph characterizations, boundary and cumulative
distribution identities, a graph–unordered-edge-set equivalence, and exact
unweighted and weighted row totals. These finite distribution results are
independent of the CC decoder and random-graph asymptotics.
`CCRecovery.lean` defines the same-index construction, identifies coding
cliques under strict dominance, and proves multiplicity recovery and
injectivity when labels and port coordinates are retained and capacity is
sufficient. `CCImageSequences.lean` proves selected arithmetic properties
of the auxiliary image-parameter arrays. The decoder script checks the
same-index construction at `K=p+1`, recovering coding cliques from closed
neighborhoods of minimum-degree vertices and then recovering multiplicities.

The four-module project has also passed a local build with warnings treated
as errors. `CCUnusedRecovery.lean` proves recovery of the unmarked cluster
family and total cross-cluster multiplicities when `p<K`, without a
clique-number bound. See the [precise formalization scope](FORMALIZATION.md),
[build evidence](verification/results/lean-build.log), and
[axiom audit](verification/results/lean-axioms.log). All 29 audited central
declarations use only standard Lean foundations.

GitHub Actions rebuild the paper, the pinned Lean project and the numerical
checks. The paper workflow publishes `Dominance.pdf` as the `revised-paper`
artifact; numerical runs publish their census and verification summaries.

## Provenance

OEIS fixtures were accessed on October 5, 2026. Source URLs, attribution and
SHA-256 digests are in `data/provenance.json`; the verification package has
its own `verification/manifest.json`. Credit for independently computed OEIS
extensions belongs to Sean A. Irvine and Pontus von Brömssen.

The primary preprint is
[Zenodo DOI 10.5281/zenodo.20004703](https://doi.org/10.5281/zenodo.20004703).
Repository revisions preserve earlier material for comparison.
The other May 2026 TeX companions on the vertex census and edge-count array
are retained historical drafts. The current verified scope of their
auxiliary arithmetic is the inventory in `FORMALIZATION.md`.
