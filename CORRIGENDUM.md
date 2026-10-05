# Corrigendum — October 5, 2026

This dated author review accompanies the revised *Clique-Size Dominance
Threshold Distribution* paper. Section 11 of the
[revised source](OEIS_Sequence_D_Dominance_Threshold_Corrected.tex) gives the
corrections and their justification.

The principal finite enumerations, retained tables, near-diagonal formulas
and bounded-multiplicity weighting formula are unchanged. Independent
verification reproduces every term of A395684 and A395691–A395695 through
eight vertices. These corrections change no sequence counts.

- **Random-graph precision:** the clique-number concentration location
  includes the second-order term `-2 log_2 log_2 n`. The leading expression
  `2 log_2 n` remains a first-order approximation, but its floor and ceiling
  do not specify the concentrated integers.
- **Expansion and finite-data descriptions:** the chosen dominance rule
  gives a logarithmic expansion factor. The finite figure is described
  using its computed rows; random-graph asymptotics do not establish
  performance on empirical network distributions.
- **Related comparisons:** A058843 counts proper color partitions rather
  than graphs by chromatic number. The illustrative unlabeled entry of
  A263341 at `(n,k)=(4,2)` is 6; the corresponding labeled count remains 40.
- **Coding interpretation:** `omega(G)+1` is the minimum for the imposed
  strict clique-dominance rule. It is not asserted to be necessary for every
  lossless decoder. The same-index construction admits unused-index recovery
  when the coding size exceeds the maximum multiplicity.
- **Overlap bookkeeping:** inclusion–exclusion uses the cardinality of the
  union of forced clique-edge sets, preserving their full overlap pattern.

The reproducibility supplement distinguishes complete termwise verification
through eight vertices from structural checks on later stored rows. The
Lean development records the scope of the structural results it proves.
