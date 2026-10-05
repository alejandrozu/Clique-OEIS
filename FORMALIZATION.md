# Verified formal development — October 5, 2026

The revised project uses **Lean 4.19.0** and **mathlib v4.19.0**. The
toolchain and dependency commits are pinned in `lean-toolchain`,
`lakefile.lean` and `lake-manifest.json`. Proofs use genuine finite graph
definitions. The revised modules contain no `sorry`, `admit`, or added
`axiom` declarations.

From the repository root, reproduce the build and dependency audit with:

```sh
lake exe cache get
lake build --wfail
mkdir -p work
lake env lean verification/ProofAudit.lean > work/proof_axioms.txt
python scripts/check_proof_axioms.py work/proof_axioms.txt
```

Recorded build and axiom-audit evidence accompanies the sources in
`verification/results/`. The axiom audit accepts only the standard Lean
foundations `propext`, `Classical.choice` and `Quot.sound` where used. It
rejects admitted proofs or other dependencies. This is separate from the
finite numerical checks.

## Labeled clique-number distribution

`DominanceThreshold.lean` defines clique number using mathlib's
`SimpleGraph.cliqueNum` on `Fin n`. It defines `d(n,k)` as the cardinality
of the actual clique-number fiber and `D(n,k)` as the cardinality of
graphs with clique number at most `k`.

The proved results establish:

- Clique number is at most `n`, and is positive for `n>=1`.
- For nonempty vertex sets, clique number one characterizes the empty
  graph. Clique number `n` characterizes the complete graph.
- `d(n,1)=d(n,n)=1`, with the stated nonempty-set qualification for the
  first column; out-of-range terms vanish.
- `D(n,0)=0` for `n>=1`, cumulative prefix sums equal `D`, and
  `d(n,k)=D(n,k)-D(n,k-1)` for `k>=1`.
- An explicit inverse equivalence identifies graphs with finite sets of
  unordered, non-loop edges. Hence there are `2^choose(n,2)` graphs.
- The clique-number fibers sum to that graph total.
- The weighted fiber definition `dp(p,n,k)` reduces to `d` at `p=1` and
  its row sum is `(p+1)^choose(n,2)`.
- A fixed support graph has exactly `p^e(G)` assignments of positive
  multiplicities. `Fin p` represents choices `1,...,p` by adding one to
  its values.
- `omega(G)<K` is equivalent to `omega(G)+1<=K`. This proves the minimum
  for the imposed strict dominance inequality; it is not a universal
  necessity claim for lossless encoding.

The weighted count is mechanized through support weights and the
fixed-support assignment count. A separate global equivalence identifying
the entire multigraph type with the union of all support fibers is not
implemented.

## Clique-cluster construction and recovery

`CCRecovery.lean` defines `PMultiGraph n p` with symmetric, loopless,
bounded natural multiplicities. The encoded graph has vertices
`Fin n × Fin K`, complete coding clusters, and same-index inter-cluster
edges below the input multiplicity.

Its proved structural results are:

- Every coding cluster is a clique of size `K`.
- Every clique either lies in one coding cluster or has at most the
  clique number of the underlying input graph.
- Under strict dominance, `K`-cliques are exactly the coding clusters.
- For distinct original vertices and capacity `p<=K`, the equal-index
  inter-port edge count equals the input multiplicity.
- With vertex labels and port coordinates retained, capacity alone makes
  the encoded graph function injective. This theorem is explicitly about
  labeled encodings.

`CCUnusedRecovery.lean` supplies the alternative cluster decoder in the
corrigendum. For `p<K`, it proves that an unused port exists in every
cluster, that every closed neighborhood has cardinality at least `K`,
and that a closed neighborhood of cardinality `K` is precisely its
coding cluster. The family of all such neighborhoods is exactly the
family of all coding clusters, **without a clique-number assumption**.
For nonempty input, the minimum closed-neighborhood cardinality is
attained and equals `K`.

It also proves that counting **all** edges between two distinct recovered
clusters gives the original multiplicity when `p<=K`. This count does not
require identification of port indices. Together these results prove the
finite partition and multiplicity recovery argument used in the corrigendum.

These finite set and counting theorems justify the cluster recovery
argument. The development does not construct an abstract quotient
decoded graph or prove a general graph-isomorphism reflection theorem.

## Supplementary parameter and edge arithmetic

`CCImageSequences.lean` uses the prescribed complete-support rule
`K=max(p,n)+1`. Its census counts positive integer parameter pairs
`(n,p)` satisfying `N=n*(max(p,n)+1)`; it does not count graph isomorphism
classes.

Sixteen proved statements cover both parameter regimes, their lower
bound, bounds placing every positive valid pair inside the finite
census rectangle, census positivity, prime-input census value one,
pronic lower bounds, and the pronic-root and bonus arithmetic. They also
establish:

```text
E(n,p) = n*choose(max(p,n)+1,2) + p*choose(n,2)
E(n,p) = n*p*(p+n)/2                    when n<=p
E(n,p) = n*(n^2+(p+1)*n-p)/2            when p<=n
E(n,n) = n^3
E(n,n)/(n*n*(n-1)/2) = 2*n/(n-1)        when n>=2
```

The divided polynomial identities use exact rational division. The
natural-number edge count uses binomial coefficients. This prevents the
incorrect splitting of a natural-number division into separately
truncated terms.

## Boundaries of the verified scope

The general inclusion–exclusion and near-diagonal formulas have
mathematical proofs in the revised paper; they are not mechanized by this
project. The random-graph asymptotics remain cited classical results.
The general auxiliary divisor-plus-pronic census formula is not a
proved theorem of the revised module. No graph-isomorphism classification
or optimal encoding-size theorem is asserted.

The numerical supplement independently checks all six OEIS sequences
through eight vertices, including all 100 retained table entries. Later
stored rows receive structural checks. Those finite computations are
separate evidence and are not presented as Lean evaluations of every
published sequence term.
