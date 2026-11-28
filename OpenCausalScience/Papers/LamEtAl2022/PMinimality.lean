module
public import OpenCausalScience.Papers.LamEtAl2022.TSPTrace
public import OpenCausalScience.Papers.RaskuttiUhler2018.SparsestPermutation

/-! # Reachability and terminal P-minimality for GRaSP0

The inclusion transformation of Chickering (2002), Theorem 4, and
Markovness of the order-induced DAGs supply the mathematical premises.
The proof constructs an improving branch of the actual oracle algorithm,
including its visited-key checks. -/

namespace OpenCausalScience.Papers.LamEtAl2022

open Discovery Chickering1995.CoveredReversal Chickering2002 RaskuttiUhler2018

@[expose] public section

variable {n : Nat}

/-- The canonical list of arrows of a DAG. -/
def edgeKey (G : DAG n) : List (Fin n × Fin n) :=
  (vertexPairs n).filter fun p => G.edge p.1 p.2

theorem edgeKey_eq_iff {G H : DAG n} : edgeKey G = edgeKey H ↔ G.edge = H.edge := by
  constructor
  · intro eq
    funext u v
    apply Bool.eq_iff_iff.mpr
    have pair : (u, v) ∈ vertexPairs n :=
      List.mem_flatMap.mpr ⟨u, List.mem_finRange _, List.mem_map.mpr ⟨v, List.mem_finRange _, rfl⟩⟩
    have mem {K : DAG n} : (u, v) ∈ edgeKey K ↔ K.edge u v = true := by
      simp [edgeKey, List.mem_filter, pair]
    rw [← mem (K := G), ← mem (K := H), eq]
  · intro eq
    simp [edgeKey, eq]

theorem edgeKey_length (G : DAG n) : (edgeKey G).length = arrowCount G := by
  simp only [edgeKey, arrowCount, List.countP_eq_length_filter]

theorem graphKey_eq_edgeKey (independent : CIOracle n) (order : List (Fin n)) :
    graphKey independent order = edgeKey (graph independent order) := rfl

theorem graphKey_length (independent : CIOracle n) (order : List (Fin n)) :
    (graphKey independent order).length = arrowCount (graph independent order) :=
  edgeKey_length (graph independent order)

/-- Any distinct TSP trace fitting the depth yields a branch of Algorithm 1.
The final deletion phase is compressed into its preceding reversal. -/
theorem ImprovingTSP.to_improvement {independent : CIOracle n} {G : DAG n} {steps : List (DAG n)}
    (trace : ImprovingTSP independent G steps)
    (distinct : (G :: steps).Pairwise (fun H K => H.edge ≠ K.edge))
    (markov : ∀ π, VertexOrder π → IsMarkov (graph independent π) independent)
    {order : List (Fin n)} (valid : VertexOrder order)
    (repr : (graph independent order).edge = G.edge)
    {depth : Nat} (fits : steps.length ≤ depth)
    {seen : List (List (Fin n × Fin n))} (fresh : ∀ K ∈ steps, edgeKey K ∉ seen) :
    ∃ next, Search.Improvement (moves independent .covered)
      (fun π => (graphKey independent π).length) (graphKey independent) depth seen order next := by
  induction trace generalizing order depth seen with
  | @turn G H D a b rev sub fewer sgs =>
    cases depth with
    | zero => simp at fits
    | succ depth =>
      obtain ⟨next, member, represented⟩ :=
        covered_move_represents_sgs_subgraph valid repr rev sub sgs markov
      have after : graphKey independent next = edgeKey D := edgeKey_eq_iff.mpr represented
      have before : graphKey independent order = edgeKey G := edgeKey_eq_iff.mpr repr
      have lower : (graphKey independent next).length < (graphKey independent order).length := by
        rw [after, before, edgeKey_length, edgeKey_length, arrow_count_eq_of_reversal rev]
        exact fewer
      exact ⟨next, .direct member (after ▸ fresh D (by simp)) lower⟩
  | @plateau G H steps a b rev sgs tail ih =>
    cases depth with
    | zero => simp at fits
    | succ depth =>
      obtain ⟨next, member, represented⟩ :=
        covered_move_represents_sgs_subgraph valid repr rev (fun _ _ h => h) sgs markov
      have after : graphKey independent next = edgeKey H := edgeKey_eq_iff.mpr represented
      have before : graphKey independent order = edgeKey G := edgeKey_eq_iff.mpr repr
      have sameCount : (graphKey independent next).length = (graphKey independent order).length := by
        rw [after, before, edgeKey_length, edgeKey_length, arrow_count_eq_of_reversal rev]
      have freshTail : ∀ K ∈ steps, edgeKey K ∉ graphKey independent next :: seen := by
        intro K present bad
        rcases List.mem_cons.mp bad with repeated | old
        · rw [after] at repeated
          exact (List.pairwise_cons.mp (List.pairwise_cons.mp distinct).2).1 K present
            (edgeKey_eq_iff.mp repeated.symm)
        · exact fresh K (List.mem_cons_of_mem _ present) old
      have fitsTail : steps.length ≤ depth := by simpa using fits
      obtain ⟨target, branch⟩ := ih (List.pairwise_cons.mp distinct).2 (valid.of_perm (moves_perm member))
        represented fitsTail freshTail
      exact ⟨target, .plateau member (after ▸ fresh H (by simp)) sameCount branch⟩

private theorem ImprovingTSP.sgs_states {independent : CIOracle n}
    {G : DAG n} {steps : List (DAG n)} (trace : ImprovingTSP independent G steps)
    (source : SGSMinimal independent G) {D : DAG n} (present : D ∈ G :: steps) :
    SGSMinimal independent D := by
  induction trace with
  | turn _ _ _ final =>
    rcases List.mem_cons.mp present with rfl | hm
    · exact source
    · simpa using (List.mem_singleton.mp hm) ▸ final
  | plateau _ compatible _ ih =>
    rcases List.mem_cons.mp present with rfl | hm
    · exact source
    · exact ih compatible hm

/-- The distinct SGS-minimal DAGs in a trace have distinct representative
permutations because each is recovered by inducing its topological order. -/
theorem ImprovingTSP.length_le_orders {independent : CIOracle n}
    {G : DAG n} {steps : List (DAG n)} (trace : ImprovingTSP independent G steps)
    (source : SGSMinimal independent G)
    (distinct : (G :: steps).Pairwise (fun H K => H.edge ≠ K.edge))
    (markov : ∀ π, VertexOrder π → IsMarkov (graph independent π) independent) :
    (G :: steps).length ≤ (allOrders n).length := by
  have topological (D : DAG n) : VertexOrder (topologicalOrder D) :=
    ⟨fun u => (topological_order_perm D).mem_iff.mpr (List.mem_finRange u),
      (topological_order_perm D).nodup_iff.mpr (List.nodup_finRange n)⟩
  have recovered (D : DAG n) (present : D ∈ G :: steps) :
      (graph independent (topologicalOrder D)).edge = D.edge :=
    arrow_eq_of_sgs_of_causal_order (topological D)
      ((topological D).causal_order_iff.mpr (topological_order_increases D))
      (trace.sgs_states source present) (markov _ (topological D))
  have higher : (G :: steps).Pairwise (fun a b =>
      a ∈ G :: steps → b ∈ G :: steps → topologicalOrder a ≠ topologicalOrder b) := by
    apply distinct.imp
    intro a b different ha hb eq
    refine different ((recovered a ha).symm.trans ?_)
    rw [eq, recovered b hb]
  have orders : ((G :: steps).map topologicalOrder).Nodup := by
    have pairwise : (G :: steps).Pairwise (fun a b => topologicalOrder a ≠ topologicalOrder b) := by
      apply List.pairwise_iff_getElem.mpr
      intro i j hi hj lt
      exact (List.pairwise_iff_getElem.mp higher i j hi hj lt) (List.mem_of_getElem rfl) (List.mem_of_getElem rfl)
    exact List.pairwise_map.mpr pairwise
  have subset : (G :: steps).map topologicalOrder ⊆ allOrders n := by
    intro π present
    obtain ⟨D, _, rfl⟩ := List.mem_map.mp present
    exact mem_permutations_iff.mpr (topological_order_perm D)
  simpa using orders.length_le_of_subset subset

theorem order_dag_sgs_minimal {independent : CIOracle n} {order : List (Fin n)}
    (valid : VertexOrder order) (markov : IsMarkov (graph independent order) independent) :
    SGSMinimal independent (graph independent order) :=
  ⟨markov, fun _ subset => markov_subgraph_edges_eq order.idxOf valid.idx_unique subset⟩

/-- A non-P-minimal induced DAG has a strictly improving covered branch. -/
theorem improvement_of_not_pminimal {independent : CIOracle n}
    (transform : InclusionTransformation n)
    (markov : ∀ π, VertexOrder π → IsMarkov (graph independent π) independent)
    {order : List (Fin n)} (valid : VertexOrder order)
    (notMinimal : ¬ PMinimal independent (graph independent order))
    {depth : Nat} (deep : (allOrders n).length ≤ depth) :
    ∃ next, Search.Improvement (moves independent .covered)
      (fun π => (graphKey independent π).length) (graphKey independent)
      depth [graphKey independent order] order next := by
  classical
  let G := graph independent order
  have source := order_dag_sgs_minimal valid (markov _ valid)
  have witness : ∃ H, IsMarkov H independent ∧ SeparationSubset G H ∧ ¬ SeparationSubset H G := by
    by_cases found : ∃ H, IsMarkov H independent ∧ SeparationSubset G H ∧ ¬ SeparationSubset H G
    · exact found
    · exfalso
      apply notMinimal
      refine ⟨markov _ valid, fun H hm included => ?_⟩
      by_cases backwards : SeparationSubset H G
      · exact backwards
      · exact (found ⟨H, hm, included, backwards⟩).elim
  obtain ⟨H, hm, includes, strict⟩ := witness
  obtain ⟨_, trace⟩ := improving_tsp_of_chickering_sequence (transform H G includes) source hm strict
  obtain ⟨steps, shorter, distinct⟩ := trace.exists_distinct
  have fits : steps.length ≤ depth := by
    have h := shorter.length_le_orders source distinct markov
    simp only [List.length_cons] at h
    omega
  apply shorter.to_improvement distinct markov valid rfl fits
  intro K present seen
  have same : edgeKey K = edgeKey G := by simpa [G, graphKey_eq_edgeKey] using seen
  exact (List.pairwise_cons.mp distinct).1 K present (edgeKey_eq_iff.mp same.symm)

/-- GRaSP0 with sufficient depth returns a P-minimal DAG under the two
mathematical prerequisites used in the paper's proof. -/
theorem covered_search_pminimal {independent : CIOracle n}
    (transform : InclusionTransformation n)
    (markov : ∀ π, VertexOrder π → IsMarkov (graph independent π) independent)
    {initial : List (Fin n)} (valid : VertexOrder initial)
    {depth : Nat} (deep : (allOrders n).length ≤ depth) :
    PMinimal independent (graph independent (search independent depth .covered initial)) := by
  let result := search independent depth .covered initial
  have properties := search_perm_and_terminal independent depth .covered initial
  classical
  by_cases bad : PMinimal independent (graph independent result)
  · exact bad
  · obtain ⟨witness, branch⟩ := improvement_of_not_pminimal transform markov
      (valid.of_perm properties.1) bad deep
    exact False.elim ((Search.no_first_improvement_iff.mp properties.2) witness branch)

end

end OpenCausalScience.Papers.LamEtAl2022
