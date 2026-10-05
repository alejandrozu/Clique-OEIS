import CCRecovery

/-!
Recovery of unmarked coding clusters from minimum closed-neighborhood size.
The input is a genuine bounded-multiplicity graph. An unused port exists when
p < K, without any bound on the clique number of the underlying graph.
-/

namespace CCUnusedRecovery

open Finset CCRecovery

/-- The closed neighborhood in the encoded simple graph. -/
def closedN {n p : ℕ} (M : PMultiGraph n p) (K : ℕ)
    (x : Fin n × Fin K) : Finset (Fin n × Fin K) :=
  univ.filter (fun y => y = x ∨ (cc M K).Adj x y)

@[simp] theorem mem_closedN {n p K : ℕ} (M : PMultiGraph n p)
    (x y : Fin n × Fin K) :
    y ∈ closedN M K x ↔ y = x ∨ (cc M K).Adj x y := by
  simp [closedN]

theorem cluster_subset_closedN {n p K : ℕ} (M : PMultiGraph n p)
    (x : Fin n × Fin K) : cluster n K x.1 ⊆ closedN M K x := by
  intro y hy
  apply (mem_closedN M x y).mpr
  by_cases hyx : y = x
  · exact Or.inl hyx
  · right
    have hfst : y.1 = x.1 := (mem_cluster x.1 y).mp hy
    apply Or.inl
    refine ⟨hfst.symm, ?_⟩
    intro hsnd
    exact hyx (Prod.ext hfst hsnd.symm)

theorem closedN_card_ge {n p K : ℕ} (M : PMultiGraph n p)
    (x : Fin n × Fin K) : K ≤ (closedN M K x).card := by
  simpa only [card_cluster] using card_le_card (cluster_subset_closedN M x)

/-- Port p (indices start at zero) is unused because multiplicities are <= p. -/
def unusedPort {p K : ℕ} (hp : p < K) : Fin K := ⟨p, hp⟩

theorem closedN_unusedPort_eq_cluster {n p K : ℕ} (M : PMultiGraph n p)
    (hp : p < K) (u : Fin n) :
    closedN M K (u, unusedPort hp) = cluster n K u := by
  apply subset_antisymm
  · intro y hy
    rcases (mem_closedN M (u, unusedPort hp) y).mp hy with hy | hy
    · subst y
      simp
    · rcases hy with hi | he
      · exact (mem_cluster u y).mpr hi.1.symm
      · have hlt : p < M.multiplicity u y.1 := he.2.2
        exact False.elim ((Nat.not_lt_of_ge (M.bounded u y.1)) hlt)
  · exact cluster_subset_closedN M (u, unusedPort hp)

theorem closedN_unusedPort_card {n p K : ℕ} (M : PMultiGraph n p)
    (hp : p < K) (u : Fin n) :
    (closedN M K (u, unusedPort hp)).card = K := by
  rw [closedN_unusedPort_eq_cluster M hp u, card_cluster]

/-- A closed neighborhood of cardinality K must equal its coding cluster. -/
theorem closedN_card_eq_cluster {n p K : ℕ} (M : PMultiGraph n p)
    (x : Fin n × Fin K) (hc : (closedN M K x).card = K) :
    closedN M K x = cluster n K x.1 := by
  exact (eq_of_subset_of_card_le (cluster_subset_closedN M x) (by simp [hc])).symm

theorem closedN_card_eq_iff_cluster {n p K : ℕ} (M : PMultiGraph n p)
    (x : Fin n × Fin K) :
    (closedN M K x).card = K ↔ closedN M K x = cluster n K x.1 := by
  constructor
  · exact closedN_card_eq_cluster M x
  · intro h
    rw [h, card_cluster]

/-- The decoder sees exactly the coding clusters, with no clique-number condition. -/
theorem closedN_characterizes_clusters {n p K : ℕ} (M : PMultiGraph n p)
    (hp : p < K) (s : Finset (Fin n × Fin K)) :
    (∃ x, closedN M K x = s ∧ s.card = K) ↔ ∃ u, s = cluster n K u := by
  constructor
  · rintro ⟨x, hx, hs⟩
    have hc : (closedN M K x).card = K := by simpa [hx] using hs
    exact ⟨x.1, hx.symm.trans (closedN_card_eq_cluster M x hc)⟩
  · rintro ⟨u, rfl⟩
    exact ⟨(u, unusedPort hp), closedN_unusedPort_eq_cluster M hp u, card_cluster u⟩

theorem recovered_cluster_family_eq {n p K : ℕ} (M : PMultiGraph n p)
    (hp : p < K) :
    {s : Finset (Fin n × Fin K) | ∃ x, closedN M K x = s ∧ s.card = K} =
      {s : Finset (Fin n × Fin K) | ∃ u, s = cluster n K u} := by
  ext s
  exact closedN_characterizes_clusters M hp s

/-- For nonempty input, K is the attained minimum closed-neighborhood size. -/
theorem exists_minimum_closedN_card {n p K : ℕ} (M : PMultiGraph n p)
    (hn : 0 < n) (hp : p < K) :
    ∃ x : Fin n × Fin K, (closedN M K x).card = K ∧
      ∀ y : Fin n × Fin K, K ≤ (closedN M K y).card := by
  let u : Fin n := ⟨0, hn⟩
  exact ⟨(u, unusedPort hp), closedN_unusedPort_card M hp u, closedN_card_ge M⟩

/-- Count all edges crossing the two recovered clusters, without selecting ports. -/
def interClusterCount {n p : ℕ} (M : PMultiGraph n p) (K : ℕ)
    (u v : Fin n) : ℕ :=
  (((univ : Finset (Fin K)).product univ).filter
    (fun ij => (cc M K).Adj (u, ij.1) (v, ij.2))).card

theorem interClusterCount_eq_interPortCount {n p K : ℕ} (M : PMultiGraph n p)
    (u v : Fin n) (huv : u ≠ v) :
    interClusterCount M K u v = interPortCount M K u v := by
  have hs : ((univ : Finset (Fin K)).product univ).filter
      (fun ij => (cc M K).Adj (u, ij.1) (v, ij.2)) =
      (univ.filter (fun i : Fin K => (cc M K).Adj (u, i) (v, i))).image
        (fun i => (i, i)) := by
    ext ⟨i, j⟩
    simp [cc, huv]
    aesop
  unfold interClusterCount interPortCount
  rw [hs]
  apply card_image_of_injective
  intro a b h
  exact (Prod.mk.inj h).1

/-- The total cross-cluster edge count recovers the input multiplicity. -/
theorem interClusterCount_eq_multiplicity {n p K : ℕ} (M : PMultiGraph n p)
    (hp : p ≤ K) (u v : Fin n) (huv : u ≠ v) :
    interClusterCount M K u v = M.multiplicity u v := by
  rw [interClusterCount_eq_interPortCount M u v huv]
  exact interPortCount_eq M hp u v huv

end CCUnusedRecovery
