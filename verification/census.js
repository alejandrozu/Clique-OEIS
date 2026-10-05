#!/usr/bin/env node
"use strict";
// Independent exact census of labeled simple graphs, requiring only Node.js.
// Histogram entries fit exactly in Number for n<=8; weights use BigInt.
const fs = require("node:fs");
const path = require("node:path");
const { performance } = require("node:perf_hooks");

function popcount(x) {
  x -= (x >>> 1) & 0x55555555;
  x = (x & 0x33333333) + ((x >>> 2) & 0x33333333);
  return (((x + (x >>> 4)) & 0x0f0f0f0f) * 0x01010101) >>> 24;
}
function validateN(n) {
  if (!Number.isInteger(n) || n < 1 || n > 8) {
    throw new RangeError("n must be an integer from 1 to 8 (32-bit masks).");
  }
}
function pairs(n) {
  const out = [];
  for (let u = 0; u < n; ++u) for (let v = u + 1; v < n; ++v) out.push([u, v]);
  return out;
}
function emptyHistogram(n) {
  return Array.from({ length: n + 1 }, () => Array(n * (n - 1) / 2 + 1).fill(0));
}

// Algorithm 1: descending vertex subsets, each represented by its required edges.
function subsetCensus(n) {
  validateN(n);
  const edgePairs = pairs(n), edgeCount = edgePairs.length;
  const cliqueMasks = [];
  for (let vertices = 1; vertices < (1 << n); ++vertices) {
    const k = popcount(vertices);
    if (k < 2) continue;
    let required = 0;
    for (let b = 0; b < edgeCount; ++b) {
      const [u, v] = edgePairs[b];
      if ((vertices & (1 << u)) && (vertices & (1 << v))) required |= 1 << b;
    }
    cliqueMasks.push({ k, required });
  }
  cliqueMasks.sort((a, b) => b.k - a.k);
  const hist = emptyHistogram(n);
  for (let graph = 0; graph < 2 ** edgeCount; ++graph) {
    let omega = 1;
    for (let j = 0; j < cliqueMasks.length; ++j) {
      const c = cliqueMasks[j];
      if ((graph & c.required) === c.required) { omega = c.k; break; }
    }
    ++hist[omega][popcount(graph)];
  }
  return hist;
}

// Algorithm 2: omega(S)=max(omega(S-v),1+omega((S-v) intersect N(v))).
// Enumerate (n-1)-vertex bases in Gray-code order, then all last neighborhoods.
function inducedCensus(n) {
  validateN(n);
  const baseN = n - 1, edgePairs = pairs(baseN), subsetCount = 1 << baseN;
  const adj = new Int32Array(baseN), omega = new Int32Array(subsetCount);
  const pc = new Int32Array(subsetCount), hist = emptyHistogram(n);
  for (let s = 1; s < subsetCount; ++s) pc[s] = pc[s & (s - 1)] + 1;
  let edges = 0;
  for (let ordinal = 0; ordinal < 2 ** edgePairs.length; ++ordinal) {
    if (ordinal > 0) {
      const bit = 31 - Math.clz32(ordinal & -ordinal);
      const [u, v] = edgePairs[bit];
      const wasPresent = (adj[u] & (1 << v)) !== 0;
      adj[u] ^= 1 << v; adj[v] ^= 1 << u;
      edges += wasPresent ? -1 : 1;
    }
    for (let s = 1; s < subsetCount; ++s) {
      const v = 31 - Math.clz32(s & -s), rest = s & (s - 1);
      omega[s] = Math.max(omega[rest], 1 + omega[rest & adj[v]]);
    }
    const baseOmega = omega[subsetCount - 1];
    for (let neighbors = 0; neighbors < subsetCount; ++neighbors) {
      const k = Math.max(baseOmega, 1 + omega[neighbors]);
      ++hist[k][edges + pc[neighbors]];
    }
  }
  return hist;
}
function weightedRows(hist) {
  return Object.fromEntries([1, 2, 3, 4, 5].map(p => [p, hist.slice(1).map(row =>
    row.reduce((sum, count, e) => sum + BigInt(count) * BigInt(p) ** BigInt(e), 0n).toString()
  )]));
}
function census(n, algorithm = "induced") {
  validateN(n);
  if (!["subset", "induced"].includes(algorithm)) throw new Error("Unknown algorithm: " + algorithm);
  const start = performance.now();
  const hist = algorithm === "subset" ? subsetCensus(n) : inducedCensus(n);
  return {
    schema_version: 1, n, algorithm, implementation: "Node.js / exact integer masks",
    graphs_enumerated: 2 ** (n * (n - 1) / 2),
    elapsed_seconds: (performance.now() - start) / 1000,
    histogram_by_clique_then_edges: hist, weighted_rows: weightedRows(hist),
  };
}
function main(args) {
  let n = 6, algorithm = "induced", output;
  for (let i = 0; i < args.length; ++i) {
    if (args[i] === "--n") n = Number(args[++i]);
    else if (args[i] === "--algorithm") algorithm = args[++i];
    else if (args[i] === "--out") output = args[++i];
    else if (args[i] === "--help") {
      console.log("node verification/census.js --n 8 --algorithm induced|subset [--out FILE]"); return;
    } else throw new Error("Unknown argument: " + args[i]);
  }
  const result = census(n, algorithm);
  if (output) {
    fs.mkdirSync(path.dirname(path.resolve(output)), { recursive: true });
    fs.writeFileSync(output, JSON.stringify(result, null, 2) + "\n");
    console.log(`${algorithm}: ${result.graphs_enumerated} graphs, n=${n}, ${result.elapsed_seconds.toFixed(3)} seconds; wrote ${output}`);
  } else console.log(JSON.stringify(result, null, 2));
}
module.exports = { subsetCensus, inducedCensus, weightedRows, census };
if (require.main === module) main(process.argv.slice(2));
