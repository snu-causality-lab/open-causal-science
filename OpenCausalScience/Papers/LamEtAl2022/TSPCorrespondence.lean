module
public import OpenCausalScience.Papers.LamEtAl2022.OracleCorrectness

/-! # Covered DFS and improving TSP graphs

Lemma B.10 converts each covered tuck to a covered reversal followed by
edge deletions. Lemma B.11 supplies the reverse conversion. These proofs
compare the existence of a successful branch before choosing among branches. -/

namespace OpenCausalScience.Papers.LamEtAl2022

open Discovery Chickering1995.CoveredReversal RaskuttiUhler2018
open KimEtAl2026.BayesBallCorrectness

@[expose] public section

variable {n : Nat}

/-- Every executable covered tuck is an equivalent DAG reversal followed
by taking a subgraph of the reversed graph. -/
theorem covered_tuck_reversal_then_subset {independent : CIOracle n}
    {order next : List (Fin n)} (valid : VertexOrder order)
    (member : next ∈ moves independent .covered order)
    (markov : IsMarkov (graph independent order) independent) :
    ∃ H a b, Reversal (graph independent order) H a b ∧ ArrowSubset (graph independent next) H := by
  obtain ⟨⟨j, k⟩, _, trial⟩ := List.mem_filterMap.mp member
  change move .covered (graph independent order) order j k = some next at trial
  unfold move at trial
  split at trial
  · rename_i eligible
    have covers := (eligible_eq_true_iff .covered _ j k).mp eligible
    cases splitResult : OrderSplit.fromOrder? order j k with
    | none => simp [splitResult] at trial
    | some s =>
      simp [splitResult] at trial
      subst next
      obtain ⟨original, tail, head⟩ := OrderSplit.reconstructs_order splitResult
      have covS : Covered (graph independent order) s.tailVertex s.headVertex := by
        simpa [tail, head, Eligible] using covers
      have causal := valid.causal_order_iff.mpr (graph independent order).edge_increases
      let reversed := Reversal.flip (graph independent order) s.tailVertex s.headVertex covS.arrow covS.parents
      refine ⟨reversed, s.tailVertex, s.headVertex, Reversal.flip_is_covered_reversal _ _ _ _ _, ?_⟩
      intro u v arrow
      apply covered_tuck_subgraph s (original ▸ causal) (original ▸ valid.covers) (original ▸ valid.nodup)
        covS (fun x => hasDirectedWalk (graph independent order) x k)
        (fun x => by rw [head]; exact hasDirectedWalk_iff _ _ _) markov
      rw [covS.arrow]
      exact arrow
  · simp at trial

private theorem reversal_of_same_target_arrows {G H K : DAG n} {a b : Fin n}
    (rev : Reversal G H a b) (eq : H.edge = K.edge) : Reversal G K a b := by
  refine ⟨rev.forward, ?_, ?_, rev.parents⟩
  · rw [← eq]
    exact rev.reverse
  · intro u v h₁ h₂
    rw [← eq]
    exact rev.unchanged u v h₁ h₂

/-- Equal edge counts identify the covered reversal itself. -/
theorem covered_tuck_equal_count_is_reversal {independent : CIOracle n}
    {order next : List (Fin n)} (valid : VertexOrder order)
    (member : next ∈ moves independent .covered order)
    (markov : IsMarkov (graph independent order) independent)
    (count : arrowCount (graph independent next) = arrowCount (graph independent order)) :
    ∃ a b, Reversal (graph independent order) (graph independent next) a b := by
  obtain ⟨H, a, b, rev, sub⟩ := covered_tuck_reversal_then_subset valid member markov
  have eq := edge_eq_of_subset_of_arrow_count_eq sub (count.trans (arrow_count_eq_of_reversal rev))
  exact ⟨a, b, reversal_of_same_target_arrows rev eq.symm⟩

/-- Every improving covered branch gives a TSP trace. Its last tuck
admits strict deletion and each preceding tuck is a covered reversal. -/
theorem Search.Improvement.to_tsp_trace {independent : CIOracle n}
    {start target : List (Fin n)} {depth seen}
    (branch : Search.Improvement (moves independent .covered)
      (fun π => (graphKey independent π).length) (graphKey independent) depth seen start target)
    (valid : VertexOrder start)
    (markov : ∀ π, VertexOrder π → IsMarkov (graph independent π) independent) :
    ∃ steps, ImprovingTSP independent (graph independent start) steps ∧
      steps.getLast? = some (graph independent target) := by
  induction branch with
  | direct move _ lower =>
    obtain ⟨H, a, b, rev, sub⟩ := covered_tuck_reversal_then_subset valid move (markov _ valid)
    have fewer := Nat.lt_of_lt_of_eq (by simpa only [graphKey_length] using lower)
      (arrow_count_eq_of_reversal rev)
    have targetValid := valid.of_perm (moves_perm move)
    exact ⟨[_], .turn rev sub fewer (order_dag_sgs_minimal targetValid (markov _ targetValid)), rfl⟩
  | plateau move _ equal _ ih =>
    obtain ⟨a, b, rev⟩ := covered_tuck_equal_count_is_reversal valid move (markov _ valid)
      (by simpa only [graphKey_length] using equal)
    have nextValid := valid.of_perm (moves_perm move)
    obtain ⟨steps, tail, last⟩ := ih nextValid
    have nonempty : steps ≠ [] := by rintro rfl; simp at last
    refine ⟨_ :: steps, .plateau rev (order_dag_sgs_minimal nextValid (markov _ nextValid)) tail, ?_⟩
    cases steps with
    | nil => exact (nonempty rfl).elim
    | cons first rest => simpa using last

/-- At a depth covering all representative orders, the two searches agree
on whether an improving trace exists, regardless of traversal order. -/
theorem covered_dfs_succeeds_iff_improving_tsp {independent : CIOracle n}
    {order : List (Fin n)} (valid : VertexOrder order)
    (markov : ∀ π, VertexOrder π → IsMarkov (graph independent π) independent)
    {depth : Nat} (deep : (allOrders n).length ≤ depth) :
    (Search.firstImprovement (moves independent .covered)
      (fun π => (graphKey independent π).length) (graphKey independent) depth
      [graphKey independent order] order ≠ none) ↔
      ∃ steps, ImprovingTSP independent (graph independent order) steps := by
  constructor
  · intro found
    cases result : Search.firstImprovement (moves independent .covered)
        (fun π => (graphKey independent π).length) (graphKey independent) depth
        [graphKey independent order] order with
    | none => exact (found result).elim
    | some next =>
      obtain ⟨steps, trace, _⟩ := (Search.first_improvement_sound result).to_tsp_trace valid markov
      exact ⟨steps, trace⟩
  · rintro ⟨_, trace⟩ none
    obtain ⟨steps, shorter, distinct⟩ := trace.exists_distinct
    have size := shorter.length_le_orders (order_dag_sgs_minimal valid (markov _ valid)) distinct markov
    have fits : steps.length ≤ depth := by simp only [List.length_cons] at size; omega
    have fresh : ∀ K ∈ steps, edgeKey K ∉ [graphKey independent order] := by
      intro K present seen
      have same : edgeKey K = edgeKey (graph independent order) := by
        simpa only [graphKey_eq_edgeKey, List.mem_singleton] using seen
      exact (List.pairwise_cons.mp distinct).1 K present (edgeKey_eq_iff.mp same.symm)
    obtain ⟨next, branch⟩ := shorter.to_improvement distinct markov valid rfl fits fresh
    exact (Search.no_first_improvement_iff.mp none) next branch

end

end OpenCausalScience.Papers.LamEtAl2022
