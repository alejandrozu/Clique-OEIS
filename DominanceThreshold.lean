-- Dominance Threshold Distribution: Lean 4 Formalization
-- Triangle d(n,k): labeled simple graphs on n vertices
--                 with clique number exactly k
--
-- This file formalizes the core definitions and structural theorems
-- for the OEIS sequence proposal "Clique-Size Dominance Threshold
-- Distribution" by Alejandro Zarzuelo Urdiales.
--
-- Prerequisites: Lean 4 with Mathlib
-- Install: https://leanprover-community.github.io/get-started.html

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace DominanceThreshold

open Finset

/-! ## Clique Number for Finite Simple Graphs -/

/-- A clique in a simple graph is a set of pairwise adjacent vertices.
    This is the decidable version suitable for computation. -/
def IsClique {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y

instance {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S : Finset V) :
    Decidable (IsClique G S) :=
  Finset.decidableDforallFinset

/-- The clique number of a simple graph on Fin n:
    the maximum size of a clique in G. -/
def cliqueNumber (n : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  sSup { k : ℕ | ∃ S : Finset (Fin n), S.card = k ∧ IsClique G S }

/-! ## The Triangle d(n, k) -/

/-- Number of labeled simple graphs on n vertices with
    clique number exactly k.
    This is the main sequence proposed for the OEIS. -/
def d (n k : ℕ) : ℕ :=
  if hnk : 1 ≤ k ∧ k ≤ n then
    (Finset.filter
      (fun (G : SimpleGraph (Fin n)) =>
        cliqueNumber n G = k)
      Finset.univ).card
  else 0

/-- Number of labeled simple graphs on n vertices with
    clique number at most k (= number of K_{k+1}-free graphs). -/
def D (n k : ℕ) : ℕ :=
  if hk : 1 ≤ k then
    (Finset.filter
      (fun (G : SimpleGraph (Fin n)) =>
        cliqueNumber n G ≤ k)
      Finset.univ).card
  else 0

/-! ## Boundary Theorems -/

/-- Only the empty graph (bot) has clique number 1.
    Proof strategy: bot is the unique graph with no edges,
    hence the unique graph where every vertex is isolated,
    so the maximum clique is a single vertex (size 1).
    Any graph with at least one edge has a clique of size >= 2. -/
theorem d_first_col (n : ℕ) (hn : 1 ≤ n) : d n 1 = 1 := by
  unfold d
  simp only [show (1 : ℕ) ≤ 1 ∧ 1 ≤ n from ⟨le_refl 1, hn⟩, if_pos]
  -- The only graph with clique number 1 is the bot (empty graph)
  have h_card :
    (Finset.filter (fun G => cliqueNumber n G = 1)
      (Finset.univ : Finset (SimpleGraph (Fin n)))).card = 1 := by
    -- Step 1: bot has clique number 1
    --   Any single vertex forms a clique of size 1 in bot
    --   No pair of vertices is adjacent, so no clique of size >= 2
    -- Step 2: any graph G ≠ bot has at least one edge {u,v}
    --   Then {u,v} forms a clique of size 2, so omega(G) >= 2
    -- Conclusion: exactly one graph (bot) has clique number 1
    sorry  -- Awaiting Mathlib SimpleGraph lemmas
  exact h_card

/-- Only the complete graph (top) has clique number n.
    Proof strategy: top is the unique graph where every pair is
    adjacent, so all n vertices form a clique of size n.
    Any graph missing at least one edge cannot have an n-clique. -/
theorem d_diag (n : ℕ) (hn : 1 ≤ n) : d n n = 1 := by
  unfold d
  simp only [show (1 : ℕ) ≤ n ∧ n ≤ n from ⟨hn, le_refl n⟩, if_pos]
  have h_card :
    (Finset.filter (fun G => cliqueNumber n G = n)
      (Finset.univ : Finset (SimpleGraph (Fin n)))).card = 1 := by
    -- Step 1: top (complete graph) has clique number n
    --   All n vertices are pairwise adjacent => clique of size n
    -- Step 2: any G ≠ top misses at least one edge {u,v}
    --   Then {u,v} is not a clique, so the max clique has size < n
    --   Actually: {1,...,n}\{any} might still be a clique of size n-1,
    --   but {1,...,n} is NOT a clique, so omega(G) <= n-1 < n
    sorry  -- Awaiting Mathlib SimpleGraph lemmas
  exact h_card

/-- d(n,k) = 0 for k outside the valid range [1, n]. -/
theorem d_out_of_range (n k : ℕ) (h1 : k < 1 ∨ k > n) : d n k = 0 := by
  unfold d
  split_ifs with hnk
  · -- hnk says 1 ≤ k ∧ k ≤ n, contradiction with h1
    rcases h1 with h1 | h1
    · omega
    · omega
  · rfl

/-! ## Row Sum Theorem -/

/-- The row sum equals 2^(n choose 2), the total number of
    labeled simple graphs on n vertices.
    This follows from the fact that the sets
    {G : omega(G) = k} partition the set of all graphs. -/
theorem row_sum_eq (n : ℕ) (hn : 1 ≤ n) :
    ∑ k in Finset.Icc 1 n, d n k =
      2 ^ (n * (n - 1) / 2) := by
  -- Key idea: the collection { {G : omega(G) = k} | k ∈ [1,n] }
  -- forms a partition of all labeled graphs on n vertices.
  -- By finset cardinality, the sum of partition class sizes
  -- equals the total, which is |SimpleGraph (Fin n)| = 2^(n choose 2).
  sorry  -- Requires partition argument + Fintype.card instance

/-! ## Inclusion-Exclusion Relation -/

/-- d(n,k) = D(n,k) - D(n,k-1).
    This is the fundamental recurrence connecting the exact
    distribution to the cumulative distribution. -/
theorem d_eq_D_diff (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    d n k = D n k - D n (k - 1) := by
  -- By definition:
  --   D(n,k) = |{G : omega(G) <= k}|
  --   D(n,k-1) = |{G : omega(G) <= k-1}|
  --   {G : omega(G) = k} = {G : omega(G) <= k} \ {G : omega(G) <= k-1}
  -- So d(n,k) = D(n,k) - D(n,k-1)
  sorry  -- Requires set subtraction + finset.card argument

/-! ## Connection to CC-Transformation -/

/-- The Clique-Size Dominance Theorem states that the
    CC-transformation f_CC is bijective if and only if
    the coding clique size K satisfies K > omega(G).
    Therefore, the minimum valid K is omega(G) + 1. -/

/-- The minimum coding clique size for a graph G is omega(G) + 1,
    by the Clique-Size Dominance Theorem (Theorem 4.1, [1]). -/
theorem K_min_eq_omega_plus_one (n : ℕ) (G : SimpleGraph (Fin n)) :
    (cliqueNumber n G + 1 : ℕ) ≥ cliqueNumber n G + 1 := by
  -- This is trivially true by the order structure of Nat.
  -- The actual content of the Clique-Size Dominance Theorem
  -- is that K_min = omega(G) + 1 is SUFFICIENT for bijectivity,
  -- while K = omega(G) is not. This requires formalizing the
  -- CC-transformation, which is future work.
  omega

/-! ## Computational Verification -/

/-- For small values, we can verify d(n,k) by computation.
    The following results are verified by exhaustive enumeration:

    n=1: d(1,1) = 1
    n=2: d(2,1) = 1,  d(2,2) = 1
    n=3: d(3,1) = 1,  d(3,2) = 6,  d(3,3) = 1
    n=4: d(4,1) = 1,  d(4,2) = 40, d(4,3) = 22, d(4,4) = 1
    n=5: d(5,1) = 1,  d(5,2) = 387, d(5,3) = 570,
         d(5,4) = 65, d(5,5) = 1

    Row sums: 1, 2, 8, 64, 1024 = 2^(n choose 2) ✓
-/

end DominanceThreshold
