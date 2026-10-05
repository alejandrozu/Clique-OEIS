"use strict";
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { subsetCensus, inducedCensus, weightedRows } = require("./census.js");
const sequences = ["A395684", "A395691", "A395692", "A395693", "A395694"];
const values = sequences.map(a => fs.readFileSync(path.join(__dirname, "../data/oeis_bfiles", a + ".txt"), "utf8")
  .split(/\r?\n/).filter(line => /^\d+\s+\d+\s*$/.test(line)).map(line => line.trim().split(/\s+/)[1]));
for (let n = 1; n <= 6; ++n) {
  const subset = subsetCensus(n), induced = inducedCensus(n);
  assert.deepEqual(induced, subset, `Algorithms disagree at n=${n}`);
  const rows = weightedRows(subset), start = n * (n - 1) / 2;
  for (let p = 1; p <= 5; ++p) assert.deepEqual(rows[p], values[p - 1].slice(start, start + n));
}
assert.throws(() => inducedCensus(9), RangeError);
console.log("Both independent algorithms agree with each other and all five exact OEIS rows through n=6.");
