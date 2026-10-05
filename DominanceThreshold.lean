import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
The OEIS distributions count genuine labeled simple graphs by their clique number.
These results do not assume a clique-cluster recovery theorem. In particular,
`cliqueNumber + 1` is not claimed to be a necessary minimum for every input graph.
The empty-vertex convention is clique number zero; the OEIS rows start at n = 1.
-/

namespace DominanceThreshold
open Finset
noncomputable section

abbrev cliqueNumber (n : ℕ) (G : SimpleGraph (Fin n)) : ℕ := G.cliqueNum

theorem cliqueNumber_le (n : ℕ) (G : SimpleGraph (Fin n)) : cliqueNumber n G ≤ n := by
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  simpa [hs.card_eq] using (card_le_card (subset_univ s))

theorem cliqueNumber_pos (n : ℕ) (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) :
    1 ≤ cliqueNumber n G := by
  let v : Fin n := ⟨0, by omega⟩
  have hc : G.IsClique ({v} : Finset (Fin n)) := by simp
  simpa using hc.card_le_cliqueNum

theorem cliqueNumber_bot (n : ℕ) (hn : 1 ≤ n) :
    cliqueNumber n (⊥ : SimpleGraph (Fin n)) = 1 := by
  apply Nat.le_antisymm
  · obtain ⟨s, hs⟩ := (⊥ : SimpleGraph (Fin n)).exists_isNClique_cliqueNum
    change (⊥ : SimpleGraph (Fin n)).cliqueNum ≤ 1
    rw [← hs.card_eq]
    exact card_le_one.mpr (fun _ hx _ hy => hs.isClique.subsingleton hx hy)
  · exact cliqueNumber_pos n hn _

theorem cliqueNumber_eq_one_iff (n : ℕ) (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) :
    cliqueNumber n G = 1 ↔ G = ⊥ := by
  classical
  constructor
  · intro h
    ext u v
    simp only [SimpleGraph.bot_adj, iff_false]
    intro huv
    have hc : G.IsClique ({u, v} : Finset (Fin n)) := by
      simpa using ((SimpleGraph.isClique_pair (G := G)).mpr (fun _ => huv))
    have hcard : ({u, v} : Finset (Fin n)).card = 2 := by simp [huv.ne]
    have hle := hc.card_le_cliqueNum
    change G.cliqueNum = 1 at h
    rw [hcard, h] at hle
    omega
  · rintro rfl
    exact cliqueNumber_bot n hn

theorem cliqueNumber_top (n : ℕ) : cliqueNumber n (⊤ : SimpleGraph (Fin n)) = n := by
  apply Nat.le_antisymm (cliqueNumber_le n _)
  have hc : (⊤ : SimpleGraph (Fin n)).IsClique (univ : Finset (Fin n)) := by
    intro u _ v _ huv
    exact huv
  simpa using hc.card_le_cliqueNum

theorem cliqueNumber_eq_n_iff (n : ℕ) (G : SimpleGraph (Fin n)) :
    cliqueNumber n G = n ↔ G = ⊤ := by
  classical
  constructor
  · intro h
    obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
    have hsuniv : s = univ := eq_of_subset_of_card_le (subset_univ _) (by simp [hs.card_eq, h])
    ext u v
    simp only [SimpleGraph.top_adj]
    exact ⟨fun huv => huv.ne, fun huv => hs.isClique (by simp [hsuniv]) (by simp [hsuniv]) huv⟩
  · rintro rfl
    exact cliqueNumber_top n

def d (n k : ℕ) : ℕ := by
  classical
  exact (univ.filter (fun G : SimpleGraph (Fin n) => cliqueNumber n G = k)).card

def D (n k : ℕ) : ℕ := by
  classical
  exact (univ.filter (fun G : SimpleGraph (Fin n) => cliqueNumber n G ≤ k)).card

theorem d_first_col (n : ℕ) (hn : 1 ≤ n) : d n 1 = 1 := by
  classical
  have h : univ.filter (fun G : SimpleGraph (Fin n) => cliqueNumber n G = 1) = {⊥} := by
    ext G
    simp [cliqueNumber_eq_one_iff n hn]
  simp [d, h]

theorem d_diag (n : ℕ) : d n n = 1 := by
  classical
  have h : univ.filter (fun G : SimpleGraph (Fin n) => cliqueNumber n G = n) = {⊤} := by
    ext G
    simp [cliqueNumber_eq_n_iff]
  simp [d, h]

theorem d_out_of_range (n k : ℕ) (hn : 1 ≤ n) (hk : k < 1 ∨ n < k) : d n k = 0 := by
  classical
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_not_mem.mpr
  intro G hG
  have heq := (mem_filter.mp hG).2
  have hpos := cliqueNumber_pos n hn G
  have hle := cliqueNumber_le n G
  rcases hk with hk | hk <;> omega

theorem D_zero (n : ℕ) (hn : 1 ≤ n) : D n 0 = 0 := by
  classical
  simp only [D, card_eq_zero, eq_empty_iff_forall_not_mem, mem_filter, mem_univ, true_and]
  intro G hG
  have := cliqueNumber_pos n hn G
  omega

theorem d_eq_D_diff (n k : ℕ) (hk : 1 ≤ k) : d n k = D n k - D n (k - 1) := by
  classical
  let A := univ.filter (fun G : SimpleGraph (Fin n) => cliqueNumber n G ≤ k)
  let B := univ.filter (fun G : SimpleGraph (Fin n) => cliqueNumber n G ≤ k - 1)
  have hsub : B ⊆ A := by
    intro G hG
    simp only [A, B, mem_filter, mem_univ, true_and] at hG ⊢
    omega
  have hdiff : A \ B = univ.filter (fun G : SimpleGraph (Fin n) => cliqueNumber n G = k) := by
    ext G
    simp only [A, B, mem_sdiff, mem_filter, mem_univ, true_and]
    omega
  simpa [d, D, A, B, hdiff] using (card_sdiff hsub)

/-- Possible edges are unordered pairs of distinct labeled vertices. -/
abbrev Edge (n : ℕ) := {e : Sym2 (Fin n) // ¬e.IsDiag}

def graphEdges (n : ℕ) (G : SimpleGraph (Fin n)) : Finset (Edge n) := by
  classical
  exact univ.filter (fun e => e.val ∈ G.edgeSet)

def fromEdges (n : ℕ) (s : Finset (Edge n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (Subtype.val '' (s : Set (Edge n)))

theorem fromEdges_graphEdges (n : ℕ) (G : SimpleGraph (Fin n)) :
    fromEdges n (graphEdges n G) = G := by
  classical
  ext u v
  simp only [fromEdges, SimpleGraph.fromEdgeSet_adj, Set.mem_image, mem_coe,
    graphEdges, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨e, he, hval⟩, _⟩
    rw [hval] at he
    exact he
  · intro huv
    refine ⟨⟨⟨s(u, v), ?_⟩, ?_, rfl⟩, huv.ne⟩
    · simpa only [Sym2.mk_isDiag_iff] using huv.ne
    · exact huv

theorem graphEdges_fromEdges (n : ℕ) (s : Finset (Edge n)) :
    graphEdges n (fromEdges n s) = s := by
  classical
  ext e
  simp [graphEdges, fromEdges, SimpleGraph.edgeSet_fromEdgeSet, e.property]

def graphEdgeEquiv (n : ℕ) : SimpleGraph (Fin n) ≃ Finset (Edge n) where
  toFun := graphEdges n
  invFun := fromEdges n
  left_inv := fromEdges_graphEdges n
  right_inv := graphEdges_fromEdges n

theorem card_labeled_graphs (n : ℕ) : Fintype.card (SimpleGraph (Fin n)) = 2 ^ n.choose 2 := by
  classical
  rw [Fintype.card_congr (graphEdgeEquiv n), Fintype.card_finset,
    Sym2.card_subtype_not_diag, Fintype.card_fin]

theorem row_sum_eq (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Icc 1 n, d n k = 2 ^ n.choose 2 := by
  classical
  have h := sum_card_fiberwise_eq_card_filter (univ : Finset (SimpleGraph (Fin n)))
    (Icc 1 n) (cliqueNumber n)
  have hf : univ.filter (fun G : SimpleGraph (Fin n) => cliqueNumber n G ∈ Icc 1 n) = univ := by
    ext G
    simp only [mem_filter, mem_univ, true_and, mem_Icc, iff_true]
    exact ⟨cliqueNumber_pos n hn G, cliqueNumber_le n G⟩
  rw [hf, card_univ, card_labeled_graphs] at h
  simpa only [d] using h

/-- Counting graphs with clique number at most k agrees with the prefix sum of
the exact distribution, including k = 0. -/
theorem D_eq_sum_d (n k : ℕ) (hn : 1 ≤ n) :
    D n k = ∑ j ∈ Icc 1 k, d n j := by
  classical
  have h := sum_card_fiberwise_eq_card_filter (univ : Finset (SimpleGraph (Fin n)))
    (Icc 1 k) (cliqueNumber n)
  have hf : univ.filter (fun G : SimpleGraph (Fin n) => cliqueNumber n G ∈ Icc 1 k) =
      univ.filter (fun G : SimpleGraph (Fin n) => cliqueNumber n G ≤ k) := by
    ext G
    simp only [mem_filter, mem_univ, true_and, mem_Icc]
    have := cliqueNumber_pos n hn G
    omega
  rw [hf] at h
  simpa only [d, D] using h.symm

/-- Weighted exact distribution for maximum multiplicity p. -/
def dp (p n k : ℕ) : ℕ := by
  classical
  exact ∑ G ∈ univ.filter (fun G : SimpleGraph (Fin n) => cliqueNumber n G = k),
    p ^ (graphEdges n G).card

theorem dp_one (n k : ℕ) : dp 1 n k = d n k := by
  classical
  simp [dp, d]

theorem total_weight (p n : ℕ) :
    (∑ G : SimpleGraph (Fin n), p ^ (graphEdges n G).card) = (p + 1) ^ n.choose 2 := by
  classical
  calc
    _ = ∑ s : Finset (Edge n), p ^ s.card := (graphEdgeEquiv n).sum_comp _
    _ = (p + 1) ^ n.choose 2 := by
      have h := Fintype.sum_pow_mul_eq_add_pow (Edge n) p 1
      have hc : Fintype.card (Edge n) = n.choose 2 := by
        simpa only [Fintype.card_fin] using (Sym2.card_subtype_not_diag (α := Fin n))
      rw [hc] at h
      simpa only [one_pow, mul_one] using h

theorem weighted_row_sum (p n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Icc 1 n, dp p n k = (p + 1) ^ n.choose 2 := by
  classical
  simp only [dp, sum_filter]
  rw [sum_comm]
  calc
    _ = ∑ G : SimpleGraph (Fin n), p ^ (graphEdges n G).card := by
      apply sum_congr rfl
      intro G _
      rw [sum_eq_single (cliqueNumber n G)]
      · simp
      · intro k _ hk
        simp [hk.symm]
      · intro h
        exact False.elim (h (mem_Icc.mpr ⟨cliqueNumber_pos n hn G, cliqueNumber_le n G⟩))
    _ = _ := total_weight p n

/-- The least integer satisfying the *strict dominance inequality* is ω + 1.
This is an arithmetic fact, not a necessity theorem about injective encodings. -/
theorem least_strict_dominance (n : ℕ) (G : SimpleGraph (Fin n)) (K : ℕ) :
    cliqueNumber n G < K ↔ cliqueNumber n G + 1 ≤ K := by omega

/-- A fixed support graph permits one choice in {1,...,p} on each existing edge.
Fin p represents those positive multiplicities after adding 1 to its values. -/
abbrev PositiveAssignments (p n : ℕ) (G : SimpleGraph (Fin n)) :=
  (e : graphEdges n G) → Fin p

theorem positiveAssignments_card (p n : ℕ) (G : SimpleGraph (Fin n)) :
    Fintype.card (PositiveAssignments p n G) = p ^ (graphEdges n G).card := by
  classical
  simp [PositiveAssignments, Fintype.card_fun]

end
end DominanceThreshold
