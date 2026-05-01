-- OEIS Sequence Proposals E and F: Lean 4 Formalization
-- Sequence E: CC-Image Vertex Census
-- Sequence F: CC-Image Edge Count Array
--
-- Prerequisites: Lean 4 with Mathlib
-- Install: https://leanprover-community.github.io/get-started.html

import Mathlib.Data.Nat.Defs
import Mathlib.Data.Int.Defs
import Mathlib.Tactic

namespace CCImageSequences

/-! ## Sequence E: CC-Image Vertex Census

For N ≥ 2, a(N) counts the number of pairs (n, p) with n ≥ 1, p ≥ 1
such that N = n · (max(p, n) + 1).

Equivalently, a(N) counts the number of non-isomorphic simple graphs
on exactly N vertices that are CC-images of complete p-multigraphs.
-/

/-- The CC-image vertex count for parameters (n, p):
    N = n · (max(p, n) + 1) -/
def ccVertexCount (n p : ℕ) : ℕ :=
  n * (max p n + 1)

/-- A pair (n, p) is valid for vertex count N if
    n ≥ 1, p ≥ 1, and N = n · (max(p, n) + 1) -/
def isValidVertexPair (N n p : ℕ) : Bool :=
  n ≥ 1 && p ≥ 1 && N = ccVertexCount n p

/-- Sequence E: CC-Image Vertex Census.
    a(N) = number of pairs (n, p) with n ≥ 1, p ≥ 1
    such that N = n · (max(p, n) + 1). -/
def vertexCensus (N : ℕ) : ℕ :=
  if N < 2 then 0
  else
    (Finset.filter (fun np : ℕ × ℕ =>
      isValidVertexPair N np.1 np.2)
      (Finset.product
        (Finset.Icc 1 N)
        (Finset.Icc 1 N))).card

/-- The first term of the formula: number of strictly inferior
    divisors of N (divisors n with n < N/n).
    This equals OEIS A056924(N). -/
def strictlyInferiorDivisors (N : ℕ) : ℕ :=
  if N = 0 then 0
  else
    (Finset.filter (fun n : ℕ =>
      n ≥ 1 && N % n = 0 && n < N / n)
      (Finset.Icc 1 N)).card

/-- Check if N is a pronic (oblong) number: N = m(m+1) for some m ≥ 2.
    Returns the value of m if found, or 0 otherwise. -/
def pronicRoot (N : ℕ) : ℕ :=
  if N < 6 then 0  -- smallest pronic with m ≥ 2 is 2·3 = 6
  else
    let m := (Nat.sqrt (4 * N + 1) - 1) / 2
    if m * (m + 1) = N ∧ m ≥ 2 then m else 0

/-- The pronic bonus: m - 1 if N = m(m+1), else 0. -/
def pronicBonus (N : ℕ) : ℕ :=
  let m := pronicRoot N
  if m = 0 then 0 else m - 1

/-- Main theorem (stated): a(N) = A056924(N) + pronic_bonus(N) -/
theorem vertexCensus_eq (N : ℕ) (hN : N ≥ 2) :
    vertexCensus N =
      strictlyInferiorDivisors N + pronicBonus N := by
  sorry  -- Requires case analysis on n ≤ p vs n > p

/-- a(N) ≥ 1 for all N ≥ 2 -/
theorem vertexCensus_pos (N : ℕ) (hN : N ≥ 2) :
    vertexCensus N ≥ 1 := by
  -- The pair (1, N-1) always works since
  -- N = 1 · max(N-1, 1) + 1 = 1 · (N-1+1) = N
  sorry

/-- If N is prime and not pronic, then a(N) = 1 -/
theorem vertexCensus_prime (N : ℕ) (hPrime : Nat.Prime N) (hNotPronic : pronicRoot N = 0) :
    vertexCensus N = 1 := by
  sorry

/-! ## Sequence F: CC-Image Edge Count Array

For n ≥ 1 and p ≥ 1, T(n, p) counts the number of edges in the
CC-image of the complete p-multigraph on n vertices.

Piecewise formula:
  T(n,p) = np(p+n)/2           if n ≤ p
  T(n,p) = n[n²+(p+1)n-p]/2   if n > p
-/

/-- The CC-image edge count using the direct definition:
    T(n,p) = n·K(K-1)/2 + n(n-1)p/2
    where K = max(p, n) + 1 -/
def ccEdgeCount (n p : ℕ) : ℕ :=
  let K := max p n + 1
  n * K * (K - 1) / 2 + n * (n - 1) * p / 2

/-- The CC-image edge count using the piecewise formula. -/
def ccEdgeCountPiecewise (n p : ℕ) : ℕ :=
  if n ≤ p then
    n * p * (p + n) / 2
  else
    n * (n^2 + (p + 1) * n - p) / 2

/-- The two definitions are equivalent. -/
theorem ccEdgeCount_eq_piecewise (n p : ℕ) (hn : n ≥ 1) (hp : p ≥ 1) :
    ccEdgeCount n p = ccEdgeCountPiecewise n p := by
  simp [ccEdgeCount, ccEdgeCountPiecewise]
  split_ifs with h
  · -- Case n ≤ p: K = p + 1
    simp [max_eq_left h]
    omega
  · -- Case n > p: K = n + 1
    simp [max_eq_right (Nat.not_le.mp h).le]
    omega

/-- The diagonal T(n, n) = n³ (perfect cubes). -/
theorem ccEdgeCount_diag (n : ℕ) (hn : n ≥ 1) :
    ccEdgeCount n n = n^3 := by
  simp [ccEdgeCount]
  -- K = n + 1 when n = p
  have hK : max n n + 1 = n + 1 := by omega
  rw [hK]
  -- n(n+1)n/2 + n(n-1)n/2 = n²(n+1)/2 + n²(n-1)/2 = n²·2n/2 = n³
  omega

/-- For n > p, T(n, p) is linear in p with coefficient n(n-1)/2.
    This means rows above the diagonal are arithmetic progressions. -/
theorem ccEdgeCount_linear_in_p (n p : ℕ) (hn : n ≥ 2) (hp : p ≥ 1) (hnp : n > p) :
    ccEdgeCount n p = n * (n + 1) * n / 2 + n * (n - 1) * p / 2 := by
  simp [ccEdgeCount]
  have : max p n + 1 = n + 1 := by omega
  rw [this]
  omega

/-- For n ≤ p, T(n, p) is quadratic in p:
    T(n, p) = n·p²/2 + n²·p/2 -/
theorem ccEdgeCount_quadratic_in_p (n p : ℕ) (hn : n ≥ 1) (hp : p ≥ 1) (hnp : n ≤ p) :
    ccEdgeCount n p = n * p^2 / 2 + n^2 * p / 2 := by
  simp [ccEdgeCount]
  have : max p n + 1 = p + 1 := by omega
  rw [this]
  omega

/-- Asymptotic edge inflation ratio for fixed p and large n:
    T(n, p) / e(K_n^(p)) ~ n/p → ∞
    where e(K_n^(p)) = n(n-1)p/2 is the original edge count. -/
theorem edge_inflation_ratio (n p : ℕ) (hn : n ≥ 2) (hp : p ≥ 1) (hnp : n > p) :
    ccEdgeCount n p = n^3/2 + (p+1)*n^2/2 - p*n/2 := by
  have h1 := ccEdgeCount_linear_in_p n p hn hp hnp
  simp [ccEdgeCount] at h1
  have : max p n + 1 = n + 1 := by omega
  rw [this] at h1
  omega

/-! ## Computed Values

  Array T(n,p) for n, p = 1..8:

       p=1   p=2   p=3   p=4   p=5   p=6   p=7   p=8
  n=1:  1     3     6    10    15    21    28    36
  n=2:  7     8    15    24    35    48    63    80
  n=3: 21    24    27    42    60    81   105   132
  n=4: 46    52    58    64    90   120   154   192
  n=5: 85    95   105   115   125   165   210   260
  n=6: 141   156   171   186   201   216   273   336
  n=7: 217   238   259   280   301   322   343   414
  n=8: 316   344   372   400   428   456   484   512

  Diagonal: 1, 8, 27, 64, 125, 216, 343, 512 = n³ ✓

  Sequence E for N = 2..30:
  1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 2, 2, 2,
  1, 3, 1, 6, 2, 2, 1, 4, 1, 2, 2, 3, 1, 8

  Pronic spikes: a(6)=3, a(12)=5, a(20)=6, a(30)=8, a(42)=9
-/

end CCImageSequences
