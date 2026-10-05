"""Finite checks of the unused-index decoder for the same-index CC construction.

For K=p+1 the last index is unused by every intercluster edge. Every coding
clique therefore supplies a degree-(K-1) vertex. All minimum-degree vertices
have their coding clique as their closed neighborhood. This recovers coding
cliques and, by counting cross-cluster edges, their multiplicities.
"""
import argparse
from itertools import combinations
import json
from pathlib import Path


def cc_image(n, multiplicities, k):
    adj = [set() for _ in range(n * k)]
    def add(u, v):
        adj[u].add(v)
        adj[v].add(u)
    for v in range(n):
        for i, j in combinations(range(k), 2):
            add(v * k + i, v * k + j)
    for (u, v), q in multiplicities.items():
        if not 0 <= q <= k:
            raise ValueError('Invalid multiplicity')
        for i in range(q):
            add(u * k + i, v * k + i)
    return adj


def recover(adj):
    delta = min(map(len, adj))
    return {frozenset({v} | adj[v]) for v in range(len(adj)) if len(adj[v]) == delta}


def check(n, multiplicities, p):
    k = p + 1
    adj = cc_image(n, multiplicities, k)
    expected = {frozenset(range(v * k, (v + 1) * k)) for v in range(n)}
    if recover(adj) != expected:
        raise AssertionError('Coding cliques were not recovered')
    for u, v in combinations(range(n), 2):
        count = sum(b in adj[a] for a in range(u * k, (u + 1) * k) for b in range(v * k, (v + 1) * k))
        if count != multiplicities.get((u, v), 0):
            raise AssertionError('Multiplicity was not recovered')


def run_checks(quick=False):
    simple_cases = 0
    for n in range(1, (4 if quick else 6) + 1):
        pairs = list(combinations(range(n), 2))
        for mask in range(1 << len(pairs)):
            mu = {uv: 1 for b, uv in enumerate(pairs) if mask & (1 << b)}
            check(n, mu, 1)
            simple_cases += 1
    p, n = (2, 3) if quick else (5, 4)
    pairs = list(combinations(range(n), 2))
    multi_cases = (p + 1) ** len(pairs)
    for code in range(multi_cases):
        residual, mu = code, {}
        for uv in pairs:
            residual, q = divmod(residual, p + 1)
            mu[uv] = q
        check(n, mu, p)
    triangle = cc_image(3, {uv: 1 for uv in combinations(range(3), 2)}, 2)
    maximal = []
    for mask in range(1, 1 << len(triangle)):
        vertices = {v for v in range(len(triangle)) if mask & (1 << v)}
        if not all(v in triangle[u] for u, v in combinations(vertices, 2)):
            continue
        if any(all(u in triangle[v] for u in vertices) for v in set(range(len(triangle))) - vertices):
            continue
        maximal.append(sorted(vertices))
    return {
        'construction': 'K-cliques; q same-index cross-cluster edges encode multiplicity q',
        'decoder': 'Distinct closed neighborhoods of minimum-degree vertices; cross-cluster edge counts',
        'simple_graphs_checked': simple_cases,
        'multigraph_parameter': p, 'multigraph_vertices': n, 'multigraphs_checked': multi_cases,
        'triangle_K2_maximal_cliques_zero_based': sorted(maximal),
        'triangle_K2_clusters_recovered': sorted(map(sorted, recover(triangle))),
        'all_checks_passed': True,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true', help='Small representative run')
    parser.add_argument('--out', type=Path, help='Write results without changing tracked evidence')
    args = parser.parse_args()
    result = run_checks(args.quick)
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))
