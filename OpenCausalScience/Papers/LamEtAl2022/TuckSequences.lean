module
public import OpenCausalScience.Papers.LamEtAl2022.ChickeringSequence

/-! # Covered tucks and reversal sequences

A covered tuck realizes the next reversal when its target is SGS-minimal.
When the reversed graph admits a proper SGS-minimal subgraph, its last
reversal and deletions can be compressed into one covered tuck. -/

namespace OpenCausalScience.Papers.LamEtAl2022

open Discovery KimEtAl2026.BayesBallCorrectness Chickering1995.CoveredReversal RaskuttiUhler2018

@[expose] public section

variable {n : Nat}

structure VertexOrder (order : List (Fin n)) : Prop where
  covers : ∀ v, v ∈ order
  nodup : order.Nodup

theorem VertexOrder.of_perm {order next : List (Fin n)} (valid : VertexOrder order)
    (perm : next.Perm order) : VertexOrder next :=
  ⟨fun v => perm.mem_iff.mpr (valid.covers v), perm.nodup_iff.mpr valid.nodup⟩

private theorem idxOf_getElem_of_nodup {order : List (Fin n)} (nodup : order.Nodup)
    (i : Nat) (bound : i < order.length) : order.idxOf order[i] = i := by
  induction order generalizing i with
  | nil => simp at bound
  | cons head rest ih =>
    cases i with
    | zero => simp
    | succ j =>
      have boundRest : j < rest.length := by simp at bound; omega
      have notHead : head ≠ rest[j] :=
        fun eq => (List.nodup_cons.mp nodup).1 (List.mem_of_getElem eq.symm)
      simpa [List.idxOf_cons, notHead] using ih (List.nodup_cons.mp nodup).2 j boundRest

theorem VertexOrder.idx_unique {order : List (Fin n)} (valid : VertexOrder order)
    (u v : Fin n) (same : order.idxOf u = order.idxOf v) : u = v := by
  have uBound := List.idxOf_lt_length_iff.mpr (valid.covers u)
  have vBound := List.idxOf_lt_length_iff.mpr (valid.covers v)
  have lookup : order[order.idxOf u]'uBound = order[order.idxOf v]'vBound := by simp only [same]
  simpa only [List.getElem_idxOf] using lookup

theorem VertexOrder.causal_order_iff {G : DAG n} {order : List (Fin n)}
    (valid : VertexOrder order) : CausalOrder G order ↔
      ∀ u v, G.edge u v = true → order.idxOf u < order.idxOf v := by
  rw [CausalOrder, List.pairwise_iff_getElem]
  constructor
  · intro pair u v edge
    have distinct : u ≠ v := fun same => G.no_directed_cycle u (.single (by simpa [← same] using edge))
    have orderNe : order.idxOf u ≠ order.idxOf v := fun same => distinct (valid.idx_unique u v same)
    by_cases right : order.idxOf u < order.idxOf v
    · exact right
    · have back : order.idxOf v < order.idxOf u := by omega
      have bad := pair _ _ (List.idxOf_lt_length_iff.mpr (valid.covers v))
        (List.idxOf_lt_length_iff.mpr (valid.covers u)) back
      simp only [List.getElem_idxOf, edge] at bad
      contradiction
  · intro rank i j hi hj earlier
    by_cases present : G.edge order[j] order[i] = true
    · have bad := rank _ _ present
      rw [idxOf_getElem_of_nodup valid.nodup j hj, idxOf_getElem_of_nodup valid.nodup i hi] at bad
      omega
    · exact Bool.eq_false_iff.mpr present

private theorem break_at_of_mem {xs : List (Fin n)} {b : Fin n} (h : b ∈ xs) :
    ∃ pair, OrderSplit.breakAt b xs = some pair := by
  induction xs with
  | nil => simp at h
  | cons hd tail ih =>
    by_cases same : hd = b
    · exact ⟨([], tail), by simp [OrderSplit.breakAt, same]⟩
    · obtain ⟨pair, found⟩ := ih ((List.mem_cons.mp h).resolve_left (Ne.symm same))
      exact ⟨(hd :: pair.1, pair.2), by simp [OrderSplit.breakAt, same, found]⟩

private theorem split_at_ordered_vertices {order : List (Fin n)} {a b : Fin n}
    (present : b ∈ order) (forward : order.idxOf a < order.idxOf b) :
    ∃ s : OrderSplit (Fin n), OrderSplit.fromOrder? order a b = some s := by
  induction order with
  | nil => simp at present
  | cons head rest ih =>
    by_cases eqA : a = head
    · subst head
      have neq : b ≠ a := by rintro rfl; omega
      have mem := (List.mem_cons.mp present).resolve_left neq
      obtain ⟨pair, found⟩ := break_at_of_mem mem
      exact ⟨⟨[], a, pair.1, b, pair.2⟩, by simp [OrderSplit.fromOrder?, OrderSplit.breakAt, found]⟩
    · have neqB : b ≠ head := by
        rintro rfl
        simp [List.idxOf_cons] at forward
      have bMem := (List.mem_cons.mp present).resolve_left neqB
      have tailRank : rest.idxOf a < rest.idxOf b := by
        simp only [List.idxOf_cons, beq_iff_eq, Ne.symm eqA, Ne.symm neqB, ↓reduceIte] at forward
        omega
      obtain ⟨next, result⟩ := ih bMem tailRank
      unfold OrderSplit.fromOrder? at result
      cases aResult : OrderSplit.breakAt a rest with
      | none => simp [aResult] at result
      | some pair =>
        cases bResult : OrderSplit.breakAt b pair.2 with
        | none => simp [aResult, bResult] at result
        | some after =>
          exact ⟨⟨head :: pair.1, a, after.1, b, after.2⟩,
            by simp [OrderSplit.fromOrder?, OrderSplit.breakAt, Ne.symm eqA, aResult, bResult]⟩

private theorem reversal_edges_eq_flip {G H : DAG n} {a b : Fin n} (rev : Reversal G H a b) :
    (Reversal.flip G a b rev.forward rev.parents).edge = H.edge := by
  funext u v
  apply Bool.eq_iff_iff.mpr
  have different : a ≠ b := fun same => G.no_directed_cycle a (.single (by simpa [← same] using rev.forward))
  by_cases backward : u = b ∧ v = a
  · rcases backward with ⟨rfl, rfl⟩
    simp [Reversal.flip, Reversal.flippedEdge, rev.reverse]
  by_cases forward : u = a ∧ v = b
  · rcases forward with ⟨rfl, rfl⟩
    have absent : H.edge u v = false := Bool.eq_false_iff.mpr fun present =>
      H.no_directed_cycle u (.extend (.single present) rev.reverse)
    simp [Reversal.flip, Reversal.flippedEdge, backward, absent]
  · simpa [Reversal.flip, Reversal.flippedEdge, backward, forward] using rev.unchanged u v forward backward

theorem arrow_eq_of_sgs_of_causal_order {independent : CIOracle n} {G : DAG n}
    {order : List (Fin n)} (valid : VertexOrder order) (causal : CausalOrder G order)
    (sgs : SGSMinimal independent G) (markov : IsMarkov (graph independent order) independent) :
    (graph independent order).edge = G.edge :=
  sgs.2 _ (fun _ _ => orderDAG_subgraph_of_markov order.idxOf valid.idx_unique
    (valid.causal_order_iff.mp causal) sgs.1) markov

/-- A covered reversal from the induced DAG is realized by a candidate
of the executable covered search. Any subgraph of the reversed DAG keeps
the resulting order. -/
theorem covered_move_orders_reversal_subgraph {independent : CIOracle n} {order : List (Fin n)}
    (valid : VertexOrder order) {G H D : DAG n} {a b : Fin n}
    (represented : (graph independent order).edge = G.edge)
    (rev : Reversal G H a b) (subgraph : ArrowSubset D H) :
    ∃ next ∈ moves independent .covered order, VertexOrder next ∧ CausalOrder D next := by
  have cov : Covered (graph independent order) a b := by
    refine ⟨?_, ?_⟩
    · rw [represented]
      exact rev.forward
    · intro u ha hb
      rw [represented]
      exact rev.parents u ha hb
  have rank := (graph independent order).edge_increases a b cov.arrow
  obtain ⟨s, found⟩ := split_at_ordered_vertices (valid.covers b) rank
  obtain ⟨original, tail, head⟩ := OrderSplit.reconstructs_order found
  let next := s.tuck true (fun u => hasDirectedWalk (graph independent order) u b)
  have isEligible := (eligible_eq_true_iff .covered _ a b).mpr cov
  have inMoves : next ∈ moves independent .covered order := by
    apply List.mem_filterMap.mpr
    refine ⟨(a, b), ?_, ?_⟩
    · exact List.mem_flatMap.mpr ⟨a, List.mem_finRange _, List.mem_map.mpr ⟨b, List.mem_finRange _, rfl⟩⟩
    · simp [move, isEligible, found, next]
  have covS : Covered (graph independent order) s.tailVertex s.headVertex := by simpa [tail, head] using cov
  have actual := (valid.causal_order_iff).mpr (graph independent order).edge_increases
  have after := covered_tuck_is_causal_order s (G := graph independent order)
    (original ▸ actual) (original ▸ valid.covers) (original ▸ valid.nodup) covS
    (fun u => hasDirectedWalk (graph independent order) u b) (fun u => by rw [head]; exact hasDirectedWalk_iff _ _ _)
  have flippedSame :
      (Reversal.flip (graph independent order) s.tailVertex s.headVertex covS.arrow covS.parents).edge = H.edge := by
    funext u v
    simp only [Reversal.flip, Reversal.flippedEdge, tail, head, represented]
    have same := congrFun (congrFun (reversal_edges_eq_flip rev) u) v
    exact same
  rw [covS.arrow] at after
  refine ⟨next, inMoves, valid.of_perm (moves_perm inMoves), ?_⟩
  exact List.Pairwise.imp (fun {u v} absent => Bool.eq_false_iff.mpr fun arrow =>
    Bool.false_ne_true (absent.symm.trans (by rw [flippedSame]; exact subgraph v u arrow))) after

/-- Compress a last covered reversal and subsequent edge deletions into
one executable tuck when the final DAG is SGS-minimal. -/
theorem covered_move_represents_sgs_subgraph {independent : CIOracle n} {order : List (Fin n)}
    (valid : VertexOrder order) {G H D : DAG n} {a b : Fin n}
    (represented : (graph independent order).edge = G.edge)
    (rev : Reversal G H a b) (subgraph : ArrowSubset D H) (sgs : SGSMinimal independent D)
    (markov : ∀ π, VertexOrder π → IsMarkov (graph independent π) independent) :
    ∃ next ∈ moves independent .covered order, (graph independent next).edge = D.edge := by
  obtain ⟨next, member, validNext, causal⟩ := covered_move_orders_reversal_subgraph valid represented rev subgraph
  exact ⟨next, member, arrow_eq_of_sgs_of_causal_order validNext causal sgs (markov _ validNext)⟩

end

end OpenCausalScience.Papers.LamEtAl2022
