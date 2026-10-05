import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
Arithmetic accompanying the CC-image parameter census and edge-count array.

The census counts parameter pairs. No equivalence with graph isomorphism
classes, necessary minimum coding size, or asymptotic theorem is asserted.
The prescribed rule here is K = max(p,n)+1 for complete input supports.
Edge-count identities are stated over the rationals when division is split,
so natural-number truncation cannot invalidate a polynomial identity.
-/

namespace CCImageSequences

def ccVertexCount (n p : ℕ) : ℕ := n * (max p n + 1)

def isValidVertexPair (N n p : ℕ) : Bool :=
  decide (1 ≤ n ∧ 1 ≤ p ∧ N = ccVertexCount n p)

def validVertexPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
    (fun np => 1 ≤ np.1 ∧ 1 ≤ np.2 ∧ N = ccVertexCount np.1 np.2)

def vertexCensus (N : ℕ) : ℕ := (validVertexPairs N).card

def strictlyInferiorDivisors (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun n => N % n = 0 ∧ n < N / n)).card

def pronicRoot (N : ℕ) : ℕ :=
  if N < 6 then 0 else
    let m := (Nat.sqrt (4 * N + 1) - 1) / 2
    if m * (m + 1) = N ∧ 2 ≤ m then m else 0

def pronicBonus (N : ℕ) : ℕ :=
  let m := pronicRoot N
  if m = 0 then 0 else m - 1

theorem ccVertexCount_of_n_le_p (n p : ℕ) (h : n ≤ p) :
    ccVertexCount n p = n * (p + 1) := by
  simp [ccVertexCount, max_eq_left h]

theorem ccVertexCount_of_p_le_n (n p : ℕ) (h : p ≤ n) :
    ccVertexCount n p = n * (n + 1) := by
  simp [ccVertexCount, max_eq_right h]

theorem ccVertexCount_ge (n p : ℕ) : n * (n + 1) ≤ ccVertexCount n p := by
  exact Nat.mul_le_mul_left n (Nat.add_le_add_right (le_max_right p n) 1)

/-- The finite rectangle in the census includes every positive valid pair. -/
theorem validVertexPair_bounds (N n p : ℕ) (hn : 1 ≤ n)
    (he : N = ccVertexCount n p) : n ≤ N ∧ p ≤ N := by
  have hcount := ccVertexCount_ge n p
  have hmax : p ≤ max p n := le_max_left _ _
  have hmul : max p n + 1 ≤ n * (max p n + 1) := by
    simpa using Nat.mul_le_mul_right (max p n + 1) hn
  unfold ccVertexCount at he hcount
  constructor
  · nlinarith
  · omega

theorem pronicRoot_at_pronic (m : ℕ) (hm : 2 ≤ m) :
    pronicRoot (m * (m + 1)) = m := by
  have h6 : ¬ m * (m + 1) < 6 := by nlinarith
  have hs : 4 * (m * (m + 1)) + 1 = (2 * m + 1) * (2 * m + 1) := by ring
  simp [pronicRoot, h6, hs, Nat.sqrt_eq, hm]

theorem pronicBonus_at_pronic (m : ℕ) (hm : 2 ≤ m) :
    pronicBonus (m * (m + 1)) = m - 1 := by
  simp [pronicBonus, pronicRoot_at_pronic m hm, show m ≠ 0 by omega]

theorem vertexCensus_pos (N : ℕ) (hN : 2 ≤ N) : 1 ≤ vertexCensus N := by
  apply Finset.one_le_card.mpr
  refine ⟨(1, N - 1), ?_⟩
  have hp : 1 ≤ N - 1 := by omega
  simp [validVertexPairs, ccVertexCount, max_eq_left hp]
  omega

theorem vertexCensus_prime (N : ℕ) (hN : Nat.Prime N) : vertexCensus N = 1 := by
  have hN2 : 2 ≤ N := hN.two_le
  apply Finset.card_eq_one.mpr
  refine ⟨(1, N - 1), ?_⟩
  ext x
  rcases x with ⟨n, p⟩
  simp only [validVertexPairs, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_Icc, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨⟨hn, _⟩, ⟨hp, _⟩⟩, _, _, he⟩
    have hd : n ∣ N := ⟨max p n + 1, he⟩
    have hcases := (Nat.dvd_prime hN).mp hd
    have hn1 : n = 1 := by
      rcases hcases with h | h
      · exact h
      · have hmax : n ≤ max p n := le_max_right _ _
        unfold ccVertexCount at he
        rw [h] at he hmax
        nlinarith
    have hpN : p = N - 1 := by
      simp [ccVertexCount, hn1, max_eq_left hp] at he
      omega
    exact Prod.ext hn1 hpN
  · intro hx
    have hnp := Prod.mk.inj hx
    rcases hnp with ⟨rfl, rfl⟩
    have hp : 1 ≤ N - 1 := by omega
    simp [ccVertexCount, max_eq_left hp]
    omega

theorem vertexCensus_pronic_ge (m : ℕ) (hm : 1 ≤ m) :
    m ≤ vertexCensus (m * (m + 1)) := by
  have hi : Function.Injective (fun p : ℕ => (m, p)) := by
    intro a b h
    exact (Prod.mk.inj h).2
  have hs : ((Finset.Icc 1 m).image (fun p : ℕ => (m, p))) ⊆
      validVertexPairs (m * (m + 1)) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    rcases Finset.mem_Icc.mp hp with ⟨hp1, hpm⟩
    have hmN : m ≤ m * (m + 1) := by nlinarith
    simp [validVertexPairs, ccVertexCount, max_eq_right hpm, hm, hp1,
      hmN, le_trans hpm hmN]
  calc
    m = (Finset.Icc 1 m).card := by simp
    _ = ((Finset.Icc 1 m).image (fun p : ℕ => (m, p))).card :=
      (Finset.card_image_of_injective _ hi).symm
    _ ≤ vertexCensus (m * (m + 1)) := Finset.card_le_card hs

/-- Exact number of intra-cluster and inter-cluster edges under the rule. -/
def ccEdgeCount (n p : ℕ) : ℕ :=
  n * (max p n + 1).choose 2 + p * n.choose 2

/-- The piecewise closed form over ℚ; division is exact field division. -/
def ccEdgeCountPiecewise (n p : ℕ) : ℚ :=
  if n ≤ p then (n : ℚ) * p * (p + n) / 2
  else (n : ℚ) * (n^2 + ((p : ℚ) + 1) * n - p) / 2

theorem ccEdgeCount_cast (n p : ℕ) :
    (ccEdgeCount n p : ℚ) =
      (n : ℚ) * (max p n + 1) * (max p n) / 2 +
      (p : ℚ) * n * (n - 1) / 2 := by
  simp only [ccEdgeCount, Nat.cast_add, Nat.cast_mul, Nat.cast_choose_two]
  push_cast
  ring

theorem ccEdgeCount_eq_piecewise (n p : ℕ) :
    (ccEdgeCount n p : ℚ) = ccEdgeCountPiecewise n p := by
  rw [ccEdgeCount_cast]
  unfold ccEdgeCountPiecewise
  split_ifs with h
  · rw [max_eq_left h]
    ring
  · rw [max_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))]
    ring

theorem ccEdgeCount_diag (n : ℕ) : ccEdgeCount n n = n^3 := by
  apply Nat.cast_injective (R := ℚ)
  rw [ccEdgeCount_eq_piecewise]
  simp [ccEdgeCountPiecewise]
  ring

theorem ccEdgeCount_linear_in_p (n p : ℕ) (h : p ≤ n) :
    ccEdgeCount n p = n * (n + 1).choose 2 + p * n.choose 2 := by
  simp [ccEdgeCount, max_eq_right h]

theorem ccEdgeCount_quadratic_in_p (n p : ℕ) (h : n ≤ p) :
    (ccEdgeCount n p : ℚ) = ((n : ℚ) * p^2 + (n : ℚ)^2 * p) / 2 := by
  rw [ccEdgeCount_eq_piecewise]
  simp only [ccEdgeCountPiecewise, if_pos h]
  ring

theorem ccEdgeCount_cubic_in_n (n p : ℕ) (h : p ≤ n) :
    (ccEdgeCount n p : ℚ) =
      ((n : ℚ)^3 + ((p : ℚ) + 1) * n^2 - (p : ℚ) * n) / 2 := by
  rw [ccEdgeCount_cast, max_eq_right h]
  ring

/-- At p=n, the exact edge inflation ratio tends to 2, not 1. -/
theorem balanced_edge_ratio (n : ℕ) (hn : 2 ≤ n) :
    (ccEdgeCount n n : ℚ) / ((n : ℚ) * n * (n - 1) / 2) =
      2 * n / (n - 1) := by
  rw [ccEdgeCount_diag]
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ n := by exact_mod_cast hn
    linarith
  push_cast
  field_simp [hn0, hn1]
  ring

end CCImageSequences
