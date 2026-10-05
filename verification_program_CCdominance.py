"""
OEIS VERIFICATION PROGRAM: labeled graphs by clique number.

Author's exhaustive Bron-Kerbosch enumerator, retained with its counting
algorithm unchanged. Reporting and reference comparisons revised 2026-10-05.

For a labeled simple graph G with e(G) edges, each positive edge multiplicity
can independently be chosen from 1,...,p. Thus

    d_p(n,k) = sum_{G: omega(G)=k} p**e(G),
    sum_k d_p(n,k) = (p+1)**binomial(n,2).

The cumulative row D_p(n,k) is the prefix sum of the exact row. Its final
entry, rather than the sum of its entries, is (p+1)**binomial(n,2).

This enumerator does not construct a CC image or prove a decoder theorem.
The revised companion paper distinguishes the largest-clique dominance rule
from lossless decoding and minimum possible encoding cost.

Row totals check graph enumeration and weights; term-by-term comparisons
against the bundled actual OEIS snapshots check the clique-number buckets.
Separate independent subset and induced-DP censuses are in verification/.
"""

import itertools
import time
from pathlib import Path
from collections import Counter

# =============================================================================
# CONFIGURATION SECTION
# =============================================================================
P = 1                  # Multiplicity parameter.
                       # P=1 -> Simple graphs (OEIS A395684)
                       # P=2 -> 2-multigraphs (OEIS A395691)
                       # P=3,4,5 -> Higher multigraphs (OEIS A395692-A395694)

N_LIST = [1, 2, 3, 4, 5, 6, 7]  # Vertex counts to compute.
                       # WARNING: Complexity is O(2^(n^2/2)).
                       # n=7 takes ~10-30 seconds. n=8 takes ~15-45 minutes.
                       # Adjust based on your machine's patience.

CUMULATIVE = False     # Set to True to compute D_p(n,k) (cumulative counts).
                       # Set to False to compute d_p(n,k) (exact counts).

PROGRESS_INTERVAL = 10  # Print progress update every N seconds
# =============================================================================


def max_clique_size(n, edges):
    """
    Compute the clique number ω(G) of a simple graph.

    Uses the Bron-Kerbosch algorithm with pivot selection to enumerate maximal
    cliques and retain the size of the largest one.

    The clique number is the size of the largest complete subgraph.
    This function computes that invariant directly; it does not assert that
    any particular CC coding size is necessary for lossless decoding.

    Parameters:
        n (int): Number of vertices.
        edges (list of tuples): List of edges (u, v) present in the graph.

    Returns:
        int: Size of the largest clique (ω(G)).
    """
    if n == 0:
        return 0

    # Build adjacency list for O(1) neighbor lookups
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)

    max_k = 0  # Tracks the size of the largest clique found

    def bron_kerbosch(R, P, X):
        """
        Recursive Bron-Kerbosch with pivot.
        R: Current clique being built
        P: Prospective vertices that can extend R
        X: Vertices already processed (to avoid duplicates)
        """
        nonlocal max_k
        if not P and not X:
            # R is a maximal clique
            if len(R) > max_k:
                max_k = len(R)
            return

        # Pivot selection: choose u in PX that maximizes |P ∩ N(u)|
        # This minimizes recursive calls and is crucial for performance.
        pivot = max(P | X, key=lambda v: len(P & adj[v]))

        # Iterate only over vertices in P that are NOT neighbors of the pivot
        for v in list(P - adj[pivot]):
            bron_kerbosch(
                R | {v},
                P & adj[v],
                X & adj[v]
            )
            P.remove(v)
            X.add(v)

    # Initial call: R=∅, P=V, X=
    bron_kerbosch(set(), set(range(n)), set())
    return max_k


def compute_dp(p, n):
    """
    Compute d_p(n, k) for a fixed n and multiplicity p.

    IMPLEMENTS Theorem 3.5 from "Clique-Size Dominance Threshold Distribution":

        d_p(n, k) = Σ_{G: ω(G)=k} p^{e(G)}

    MATHEMATICAL DERIVATION:
    ------------------------
    The key insight: for a FIXED simple graph G with e(G) edges, there are
    exactly p^{e(G)} distinct p-multigraphs having G as their underlying
    structure, because:
    - Each of the e(G) edges can independently take multiplicity 1, 2, ..., p
    - Non-edges must have multiplicity 0 (only 1 choice)
    - Total choices: p^{e(G)}

    We sum this weighting over ALL simple graphs with clique number k to get
    the total count d_p(n, k).

    VERIFICATION (Corollary 3.1):
    -----------------------------
    The row sum must equal (p+1)^{n choose 2} because:
    - Each of the (n choose 2) potential edges can take multiplicity 0, 1, ..., p
    - Total: (p+1) choices per edge
    - Independence: (p+1)^{n choose 2} total p-multigraphs

    This checks the total graph weights. A correct total alone does not
    establish correct clique-number classification.

    Parameters:
        p (int): Multiplicity parameter.
        n (int): Number of vertices.

    Returns:
        Counter: Mapping from clique number k -> count d_p(n, k).
    """
    m = n * (n - 1) // 2  # Total possible edges = n choose 2
    potential_edges = list(itertools.combinations(range(n), 2))
    counts = Counter()

    total_graphs = 1 << m  # 2^m total simple graphs
    last_update = time.time()
    graphs_processed = 0

    print(f"  Enumerating {total_graphs:,} labeled simple graphs on {n} vertices...")

    # Enumerate all 2^m labeled simple graphs via bitmask
    # Each bit in 'mask' corresponds to an edge in potential_edges
    for mask in range(total_graphs):
        graphs_processed += 1

        # Progress update every PROGRESS_INTERVAL seconds
        current_time = time.time()
        if current_time - last_update >= PROGRESS_INTERVAL:
            elapsed = current_time - last_update
            last_update = current_time
            percent = (graphs_processed / total_graphs) * 100
            eta_seconds = (total_graphs - graphs_processed) * elapsed / max(graphs_processed, 1)
            print(f"    Progress: {graphs_processed:,}/{total_graphs:,} ({percent:.1f}%), "
                  f"ETA: {eta_seconds:.1f}s")

        # Extract edges present in this simple graph
        edges = [potential_edges[i] for i in range(m) if mask & (1 << i)]
        e_G = len(edges)  # Number of edges in the underlying simple graph

        # Compute clique number ω(G)
        # Classify the underlying simple graph by its clique number.
        omega = max_clique_size(n, edges)

        # Apply weighting factor p^{e(G)}
        # This accounts for the p choices of multiplicity for each existing edge.
        # For p=1 (simple graphs), this is just 1^{e(G)} = 1 (count each graph once)
        # For p=2 (2-multigraphs), this is 2^{e(G)} (each edge has 2 choices: mult. 1 or 2)
        # For p=3, each edge has 3 choices: mult. 1, 2, or 3, etc.
        weight = p ** e_G
        counts[omega] += weight

    # ========================================================================
    # VERIFICATION: Row Sum Theorem (Corollary 3.1)
    # ========================================================================
    # The sum over all k must equal (p+1)^m, since each edge independently
    # has (p+1) states: multiplicity 0, 1, ..., p.
    row_sum = sum(counts.values())
    expected_sum = (p + 1) ** m

    if row_sum != expected_sum:
        raise AssertionError(
            f"❌ Row sum verification FAILED for n={n}:\n"
            f"   Computed sum: {row_sum}\n"
            f"   Expected sum: {expected_sum} (= ({p}+1)^{m})\n"
            f"   This indicates a bug in graph enumeration or weights."
        )

    return counts



def compare_to_oeis_snapshot(p, n, row, cumulative=False):
    """Compare with an actual stored row; return its sequence ID when checked.

    Configurations without a matching stored sequence/complete row return None.
    A present row with different terms raises instead of claiming success.
    """
    sequences = {1: "A395684", 2: "A395691", 3: "A395692", 4: "A395693", 5: "A395694"}
    sequence = "A395695" if cumulative and p == 1 else None if cumulative else sequences.get(p)
    if sequence is None:
        return None
    reference = Path(__file__).resolve().parent / "data" / "oeis_bfiles" / (sequence + ".txt")
    terms = [int(line.split()[1]) for line in reference.read_text(encoding="utf-8-sig").splitlines()
             if line.strip() and not line.lstrip().startswith("#")]
    start, end = n * (n - 1) // 2, n * (n + 1) // 2
    if n < 1 or end > len(terms):
        return None
    expected = terms[start:end]
    if list(row) != expected:
        raise AssertionError(f"{sequence}, n={n}: computed {list(row)}, expected {expected}")
    return sequence


def main():
    """Main execution routine. Prints results in OEIS-ready format."""
    print("=" * 70)
    print(f"OEIS VERIFICATION: p={P}, Cumulative={CUMULATIVE}")
    print(f"Computing rows for n in {N_LIST}")
    print("=" * 70 + "\n")

    snapshot_matches = 0
    for n in N_LIST:
        row_start_time = time.time()

        # Compute exact counts d_p(n, k)
        exact_counts = compute_dp(P, n)

        # Format row in standard OEIS order: k = 1, 2, ..., n
        row = [exact_counts.get(k, 0) for k in range(1, n + 1)]

        if CUMULATIVE:
            # Convert to cumulative D_p(n, k) = Σ_{j=1}^k d_p(n, j)
            # This matches OEIS A395695 when P=1.
            row = [sum(row[:i+1]) for i in range(len(row))]
            label = "Cumulative"
        else:
            label = "Exact"

        row_time = time.time() - row_start_time

        # Print in OEIS flattened triangle format
        print(f"n={n:2d} ({label}): {row}")
        if CUMULATIVE:
            print(f"  Final cumulative entry: {row[-1]:,} = ({P}+1)^{{{n*(n-1)//2}}} ✓")
        else:
            print(f"  Exact row sum: {sum(row):,} = ({P}+1)^{{{n*(n-1)//2}}} ✓")
        sequence = compare_to_oeis_snapshot(P, n, row, CUMULATIVE)
        if sequence:
            snapshot_matches += 1
            print(f"  Matches stored {sequence} row n={n} term by term. ✓")
        else:
            print("  No stored OEIS row comparison is available for this configuration.")
        print(f"  Computation time: {row_time:.2f}s")
        print()

    print("\n" + "=" * 70)
    print("All computed exact row totals verified against (p+1)^(n choose 2).")
    print(f"Term-by-term stored OEIS comparisons passed for {snapshot_matches} computed row(s).")
    print("=" * 70)


if __name__ == "__main__":
    main()
