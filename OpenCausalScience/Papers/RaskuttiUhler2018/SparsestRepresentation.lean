module
public import OpenCausalScience.Discovery.OrderedMarkov
public import OpenCausalScience.Papers.RaskuttiUhler2018.SparsestPermutation
public import OpenCausalScience.Papers.VermaPearl1990.Equivalence

/-! # The sparsest Markov representation condition for oracle SP -/

namespace OpenCausalScience.Papers.RaskuttiUhler2018

open Discovery LamEtAl2022
open Chickering1995.Transformation
open VermaPearl1990.DAGEquivalence VermaPearl1990.Equivalence

@[expose] public section

variable {n : Nat}

theorem arrow_count_eq_of_same_dConnections {G H : DAG n} (same : SameDConnections G H) :
    arrowCount G = arrowCount H := by
  have moves := reversal_sequence same
  clear same
  induction moves with
  | done edges => simp [arrowCount, edges]
  | next _ rev _ ih => exact (arrow_count_eq_of_reversal rev).trans ih

/-- Lemma 2.1 supplies the Markovness premise. The search then minimizes
arrow count over all Markov DAGs, including graphs outside the candidate list. -/
theorem sparsest_order_is_globally_sparsest {independent : CIOracle n}
    (markovOfOrder : ∀ order, order.Perm (List.finRange n) → IsMarkov (graphOfOrder independent order) independent)
    {order : List (Fin n)} (selected : order ∈ sparsestOrders independent) :
    IsMarkov (graphOfOrder independent order) independent ∧
      ∀ H, IsMarkov H independent → edgeCost independent order ≤ arrowCount H :=
  ⟨markovOfOrder order ((mem_sparsest_orders_iff independent order).mp selected).1,
    fun _ h => sparsest_cost_le_of_markov h selected⟩

/-- The truth is sparser than every Markov DAG outside its equivalence class. -/
def SparsestMarkovRepresentation (G : DAG n) (independent : CIOracle n) : Prop :=
  ∀ H, IsMarkov H independent → ¬ SameDConnections H G → arrowCount G < arrowCount H

/-- Theorem 2.4 at the exact oracle level. Every returned DAG is equivalent
 to the truth precisely under the sparsest Markov representation condition. -/
theorem sparsest_orders_recover_iff_smr {G : DAG n} {independent : CIOracle n}
    (trueMarkov : IsMarkov G independent)
    (markovOfOrder : ∀ order, order.Perm (List.finRange n) → IsMarkov (graphOfOrder independent order) independent) :
    (∀ order ∈ sparsestOrders independent, SameDConnections (graphOfOrder independent order) G) ↔
      SparsestMarkovRepresentation G independent := by
  classical
  constructor
  · intro recovers H hMarkov different
    apply Classical.byContradiction
    intro notSmaller
    have violation := Nat.le_of_not_gt notSmaller
    have existsSelected : ∃ order, order ∈ sparsestOrders independent := by
      cases choices : sparsestOrders independent with
      | nil => exact (sparsest_orders_nonempty independent choices).elim
      | cons order tail => exact ⟨order, List.mem_cons_self⟩
    obtain ⟨order, selected⟩ := existsSelected
    let candidate := topologicalOrder H
    let projected := graphOfOrder independent candidate
    have subset : ∀ u v, projected.edge u v = true → H.edge u v = true := fun _ _ edge =>
      orderDAG_subgraph_of_markov _ (idxOf_injective (topological_order_perm H))
        (topological_order_increases H) hMarkov edge
    have minimum : edgeCost independent order = arrowCount G :=
      arrow_count_eq_of_same_dConnections (recovers order selected)
    have costBound : edgeCost independent candidate ≤ arrowCount H := arrow_count_le_of_subset subset
    have candidateSelected : candidate ∈ sparsestOrders independent := by
      refine (mem_sparsest_orders_iff independent candidate).mpr ⟨topological_order_perm H, ?_⟩
      intro any perm
      exact Nat.le_trans costBound (Nat.le_trans violation
        (minimum ▸ ((mem_sparsest_orders_iff independent order).mp selected).2 any perm))
    have sameCount : arrowCount projected = arrowCount H := Nat.le_antisymm costBound
      (arrow_count_eq_of_same_dConnections (recovers candidate candidateSelected) ▸ violation)
    have sameEdges := edge_eq_of_subset_of_arrow_count_eq subset sameCount
    exact different (fun cond x y => ((same_dConnections_of_edge_eq sameEdges) cond x y).symm.trans
      (recovers candidate candidateSelected cond x y))
  · intro smr order selected
    apply Classical.byContradiction
    intro different
    have ⟨markov, lower⟩ := sparsest_order_is_globally_sparsest markovOfOrder selected
    exact (Nat.not_lt_of_ge (lower G trueMarkov)) (smr _ markov different)


/-- The sparsest-permutation characterization for a graphoid CI model. -/
theorem sparsest_orders_recover_iff_smr_of_graphoid {G : DAG n} {independent : CIOracle n}
    {J : Probability.CI.Relation n} (g : Probability.CI.Graphoid J)
    (agrees : MatchesOracle J independent) (trueMarkov : IsMarkov G independent) :
    (∀ order ∈ sparsestOrders independent, SameDConnections (graphOfOrder independent order) G) ↔
      SparsestMarkovRepresentation G independent :=
  sparsest_orders_recover_iff_smr trueMarkov fun order complete =>
    induced_order_is_markov g agrees order.idxOf (idxOf_injective complete)

end

end OpenCausalScience.Papers.RaskuttiUhler2018
