import DominanceThreshold

/-!
The index-rigid clique-cluster construction and its sufficient recovery theorem.
The hypotheses in PMultiGraph are the defining symmetry, looplessness and bounded
multiplicity conditions, not assumed recovery facts. Necessity of strict dominance
for every individual input is deliberately not asserted.
-/

namespace CCRecovery
open Finset

@[ext] structure PMultiGraph (n p : ℕ) where
  multiplicity : Fin n → Fin n → ℕ
  symm : ∀ u v, multiplicity u v = multiplicity v u
  loopless : ∀ u, multiplicity u u = 0
  bounded : ∀ u v, multiplicity u v ≤ p

def underlying {n p : ℕ} (M : PMultiGraph n p) : SimpleGraph (Fin n) where
  Adj u v := 0 < M.multiplicity u v
  symm u v h := by simpa [M.symm u v] using h
  loopless u := by simp [M.loopless]

/-- Each original vertex has K ports. Distinct ports in a cluster are adjacent;
different clusters are joined only at equal port indices below multiplicity. -/
def cc {n p : ℕ} (M : PMultiGraph n p) (K : ℕ) : SimpleGraph (Fin n × Fin K) where
  Adj x y := (x.1 = y.1 ∧ x.2 ≠ y.2) ∨
    (x.1 ≠ y.1 ∧ x.2 = y.2 ∧ x.2.val < M.multiplicity x.1 y.1)
  symm x y h := by
    rcases h with h | h
    · exact Or.inl ⟨h.1.symm, h.2.symm⟩
    · exact Or.inr ⟨h.1.symm, h.2.1.symm, by simpa [h.2.1, M.symm x.1 y.1] using h.2.2⟩
  loopless x := by simp

instance {n p : ℕ} (M : PMultiGraph n p) (K : ℕ) : DecidableRel (cc M K).Adj :=
  fun x y => inferInstanceAs (Decidable ((x.1 = y.1 ∧ x.2 ≠ y.2) ∨
    (x.1 ≠ y.1 ∧ x.2 = y.2 ∧ x.2.val < M.multiplicity x.1 y.1)))

def cluster (n K : ℕ) (v : Fin n) : Finset (Fin n × Fin K) :=
  univ.map ⟨fun i => (v, i), by intro a b h; exact (Prod.mk.inj h).2⟩

@[simp] theorem mem_cluster {n K : ℕ} (v : Fin n) (x : Fin n × Fin K) :
    x ∈ cluster n K v ↔ x.1 = v := by
  rcases x with ⟨w, i⟩
  simp [cluster, eq_comm]

@[simp] theorem card_cluster {n K : ℕ} (v : Fin n) : (cluster n K v).card = K := by
  simp [cluster]

theorem cluster_isClique {n p K : ℕ} (M : PMultiGraph n p) (v : Fin n) :
    (cc M K).IsClique (cluster n K v) := by
  intro x hx y hy hxy
  have hxv : x.1 = v := mem_cluster v x |>.mp hx
  have hyv : y.1 = v := mem_cluster v y |>.mp hy
  apply Or.inl
  refine ⟨hxv.trans hyv.symm, ?_⟩
  intro hsnd
  exact hxy (Prod.ext (hxv.trans hyv.symm) hsnd)

/-- A clique with injective projection to original vertices has no more vertices
than a maximum clique of the underlying graph. -/
theorem projected_clique_bound {n p K : ℕ} (M : PMultiGraph n p)
    (s : Finset (Fin n × Fin K)) (hs : (cc M K).IsClique s)
    (hinj : Set.InjOn Prod.fst (s : Set (Fin n × Fin K))) :
    s.card ≤ (underlying M).cliqueNum := by
  classical
  have hc : (underlying M).IsClique (s.image Prod.fst) := by
    intro u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hu
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hv
    have hxy : x ≠ y := fun h => huv (congrArg Prod.fst h)
    rcases hs hx hy hxy with h | h
    · exact False.elim (huv h.1)
    · exact lt_of_le_of_lt (Nat.zero_le x.2.val) h.2.2
  have hcard : (s.image Prod.fst).card = s.card := card_image_of_injOn hinj
  simpa [hcard] using hc.card_le_cliqueNum

/-- Every clique either projects injectively to the underlying graph or lies
inside a single coding cluster. This is the structural mixed-clique exclusion. -/
theorem clique_bound_or_cluster {n p K : ℕ} (M : PMultiGraph n p)
    (s : Finset (Fin n × Fin K)) (hs : (cc M K).IsClique s) :
    s.card ≤ (underlying M).cliqueNum ∨ ∃ v, s ⊆ cluster n K v := by
  classical
  by_cases hinj : Set.InjOn Prod.fst (s : Set (Fin n × Fin K))
  · exact Or.inl (projected_clique_bound M s hs hinj)
  · right
    simp only [Set.InjOn] at hinj
    push_neg at hinj
    obtain ⟨x, hx, y, hy, hfst, hne⟩ := hinj
    have hsnd : x.2 ≠ y.2 := fun h => hne (Prod.ext hfst h)
    refine ⟨x.1, ?_⟩
    intro z hz
    apply (mem_cluster x.1 z).mpr
    by_contra hzx
    have hxz : x ≠ z := fun h => hzx (congrArg Prod.fst h).symm
    have hyz : y ≠ z := by
      intro h
      apply hzx
      exact (congrArg Prod.fst h).symm.trans hfst.symm
    rcases hs hx hz hxz with h | h
    · exact hzx h.1.symm
    · rcases hs hy hz hyz with h' | h'
      · exact hzx (h'.1.symm.trans hfst.symm)
      · exact hsnd (h.2.1.trans h'.2.1.symm)

/-- Under strict dominance, K-cliques are exactly the coding clusters. -/
theorem k_cliques_exactly_clusters {n p K : ℕ} (M : PMultiGraph n p)
    (hdom : (underlying M).cliqueNum < K) (s : Finset (Fin n × Fin K)) :
    (cc M K).IsNClique K s ↔ ∃ v, s = cluster n K v := by
  classical
  constructor
  · intro hs
    rcases clique_bound_or_cluster M s hs.isClique with h | ⟨v, hv⟩
    · rw [hs.card_eq] at h
      omega
    · exact ⟨v, eq_of_subset_of_card_le hv (by simp [hs.card_eq])⟩
  · rintro ⟨v, rfl⟩
    exact ⟨cluster_isClique M v, card_cluster v⟩

/-- Count equal-index inter-cluster edges between two specified coding clusters. -/
def interPortCount {n p : ℕ} (M : PMultiGraph n p) (K : ℕ) (u v : Fin n) : ℕ :=
  (univ.filter (fun i : Fin K => (cc M K).Adj (u, i) (v, i))).card

theorem interPortCount_eq {n p K : ℕ} (M : PMultiGraph n p) (hp : p ≤ K)
    (u v : Fin n) (huv : u ≠ v) : interPortCount M K u v = M.multiplicity u v := by
  classical
  have hm : M.multiplicity u v ≤ K := (M.bounded u v).trans hp
  simpa [interPortCount, cc, huv, Fintype.card_subtype] using
    (Fintype.card_fin_lt_of_le hm)

/-- With labels and port coordinates retained, capacity alone makes the encoding
injective. This is explicitly different from unmarked-cluster recovery. -/
theorem labeled_encoding_injective {n p K : ℕ} (hp : p ≤ K) :
    Function.Injective (fun M : PMultiGraph n p => cc M K) := by
  intro M N h
  apply PMultiGraph.ext
  funext u v
  by_cases huv : u = v
  · subst v
    simp [M.loopless, N.loopless]
  · have hc : interPortCount M K u v = interPortCount N K u v := by
      simp [interPortCount, h]
    rw [interPortCount_eq M hp u v huv, interPortCount_eq N hp u v huv] at hc
    exact hc

end CCRecovery
