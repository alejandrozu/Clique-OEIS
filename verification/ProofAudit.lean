import DominanceThreshold
import CCRecovery
import CCImageSequences
import CCUnusedRecovery

/-! Print the trusted axiom dependencies of the central proved results.
Expected dependencies are only Lean's standard classical foundations:
propext, Classical.choice, and Quot.sound. No theorem may depend on sorryAx.
Run after `lake build --wfail`: `lake env lean verification/ProofAudit.lean`.
-/

#print axioms DominanceThreshold.cliqueNumber_eq_one_iff
#print axioms DominanceThreshold.cliqueNumber_eq_n_iff
#print axioms DominanceThreshold.d_eq_D_diff
#print axioms DominanceThreshold.D_eq_sum_d
#print axioms DominanceThreshold.graphEdgeEquiv
#print axioms DominanceThreshold.card_labeled_graphs
#print axioms DominanceThreshold.row_sum_eq
#print axioms DominanceThreshold.total_weight
#print axioms DominanceThreshold.weighted_row_sum
#print axioms DominanceThreshold.least_strict_dominance
#print axioms DominanceThreshold.positiveAssignments_card
#print axioms CCRecovery.clique_bound_or_cluster
#print axioms CCRecovery.k_cliques_exactly_clusters
#print axioms CCRecovery.interPortCount_eq
#print axioms CCRecovery.labeled_encoding_injective
#print axioms CCUnusedRecovery.closedN_card_ge
#print axioms CCUnusedRecovery.closedN_unusedPort_eq_cluster
#print axioms CCUnusedRecovery.closedN_characterizes_clusters
#print axioms CCUnusedRecovery.recovered_cluster_family_eq
#print axioms CCUnusedRecovery.exists_minimum_closedN_card
#print axioms CCUnusedRecovery.interClusterCount_eq_interPortCount
#print axioms CCUnusedRecovery.interClusterCount_eq_multiplicity
#print axioms CCImageSequences.vertexCensus_pos
#print axioms CCImageSequences.vertexCensus_prime
#print axioms CCImageSequences.vertexCensus_pronic_ge
#print axioms CCImageSequences.pronicRoot_at_pronic
#print axioms CCImageSequences.ccEdgeCount_eq_piecewise
#print axioms CCImageSequences.ccEdgeCount_diag
#print axioms CCImageSequences.balanced_edge_ratio
