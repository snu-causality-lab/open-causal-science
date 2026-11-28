module
public import OpenCausalScience.Papers.LamEtAl2022.PMinimality

/-! # The oracle reachability and correctness conclusions

The covered trace in Theorem 4.5 may contain several strictly decreasing
parts. Edge counts distinguish their plateau states, allowing their traces
to concatenate without repeating a DAG. -/

namespace OpenCausalScience.Papers.LamEtAl2022

open Discovery Chickering1995.CoveredReversal Chickering2002 RaskuttiUhler2018
open Moralization KimEtAl2026.BayesBallCorrectness

@[expose] public section

variable {n : Nat}

/-- Each step in the trace is one covered tuck of the current order. -/
inductive CoveredWalk (independent : CIOracle n) :
    List (Fin n) → List (List (Fin n)) → List (Fin n) → Prop
  | nil (order) : CoveredWalk independent order [] order
  | cons {order next rest final} : next ∈ moves independent .covered order →
      CoveredWalk independent next rest final → CoveredWalk independent order (next :: rest) final

theorem CoveredWalk.append {independent : CIOracle n} {start middle final : List (Fin n)}
    {walk tail : List (List (Fin n))} (leading : CoveredWalk independent start walk middle)
    (suffix : CoveredWalk independent middle tail final) :
    CoveredWalk independent start (walk ++ tail) final := by
  induction leading with
  | nil => exact suffix
  | cons move _ ih => exact .cons move (ih suffix)

/-- Definition 4.3 adds pairwise distinct induced DAGs to a covered walk. -/
def CtSequence (independent : CIOracle n) (start : List (Fin n))
    (walk : List (List (Fin n))) (final : List (Fin n)) : Prop :=
  CoveredWalk independent start walk final ∧ ((start :: walk).map (graphKey independent)).Nodup

private theorem Search.Improvement.to_covered_walk {independent : CIOracle n}
    {start final : List (Fin n)} {depth seen}
    (witness : Search.Improvement (moves independent .covered)
      (fun π => (graphKey independent π).length) (graphKey independent) depth seen start final) :
    ∃ plateau : List (List (Fin n)),
      CoveredWalk independent start (plateau ++ [final]) final ∧
      ((plateau ++ [final]).map (graphKey independent)).Nodup ∧
      (∀ π ∈ plateau, (graphKey independent π).length = (graphKey independent start).length) ∧
      (∀ π ∈ plateau ++ [final], graphKey independent π ∉ seen) := by
  induction witness with
  | direct move fresh _ =>
    refine ⟨[], .cons move (.nil _), by simp, by simp, ?_⟩
    intro π present
    simpa [List.mem_singleton.mp present] using fresh
  | @plateau _ seen start next _ move fresh equal _ ih =>
    obtain ⟨before, path, nodup, costs, unseen⟩ := ih
    refine ⟨next :: before, .cons move path, ?_, ?_, ?_⟩
    · simp only [List.cons_append, List.map_cons, List.nodup_cons]
      refine ⟨?_, nodup⟩
      intro repeated
      obtain ⟨w, member, key⟩ := List.mem_map.mp repeated
      exact unseen w member (by simp [key])
    · intro π member
      rcases List.mem_cons.mp member with rfl | inPlateau
      · exact equal
      · exact (costs _ inPlateau).trans equal
    · intro π member
      rcases List.mem_cons.mp member with rfl | inTail
      · exact fresh
      · exact fun old => unseen _ inTail (List.mem_cons_of_mem _ old)

/-- Reach a P-minimal DAG by a ct-sequence, as in Theorem 4.5. The
transformation and induced Markov hypotheses are separate mathematical inputs. -/
theorem exists_ct_sequence_to_pminimal {independent : CIOracle n}
    (transform : InclusionTransformation n)
    (markov : ∀ π, VertexOrder π → IsMarkov (graph independent π) independent)
    (start : List (Fin n)) (valid : VertexOrder start) :
    ∃ walk final, CtSequence independent start walk final ∧
      (∀ π ∈ walk, (graphKey independent π).length ≤ (graphKey independent start).length) ∧
      PMinimal independent (graph independent final) := by
  classical
  by_cases minimal : PMinimal independent (graph independent start)
  · exact ⟨[], start, ⟨.nil _, by simp⟩, by simp, minimal⟩
  · obtain ⟨next, branch⟩ := improvement_of_not_pminimal transform markov valid minimal
      (Nat.le_refl (allOrders n).length)
    have strict := branch.lower_cost
    have nextValid := valid.of_perm (branch.perm (fun mem => moves_perm mem))
    obtain ⟨more, final, remaining, tailCosts, minimal⟩ :=
      exists_ct_sequence_to_pminimal transform markov next nextValid
    obtain ⟨plateau, leading, nodup, costs, fresh⟩ := Search.Improvement.to_covered_walk branch
    refine ⟨plateau ++ next :: more, final, ⟨?_, ?_⟩, ?_, minimal⟩
    · simpa [List.append_assoc] using leading.append remaining.1
    · have headFresh : graphKey independent start ∉ (plateau.map (graphKey independent)) := by
        intro found
        obtain ⟨π, member, key⟩ := List.mem_map.mp found
        exact fresh π (List.mem_append_left _ member) (by simp [key])
      have leftNodup : ((start :: plateau).map (graphKey independent)).Nodup :=
        List.nodup_cons.mpr ⟨headFresh, List.Nodup.sublist (by simp) nodup⟩
      have cross : ∀ before ∈ (start :: plateau).map (graphKey independent),
          ∀ after ∈ (next :: more).map (graphKey independent), before ≠ after := by
        intro a am b bm same
        obtain ⟨p, pm, rfl⟩ := List.mem_map.mp am
        obtain ⟨q, qm, rfl⟩ := List.mem_map.mp bm
        have old : (graphKey independent p).length = (graphKey independent start).length := by
          rcases List.mem_cons.mp pm with rfl | inPlateau
          · rfl
          · exact costs _ inPlateau
        have new : (graphKey independent q).length ≤ (graphKey independent next).length := by
          rcases List.mem_cons.mp qm with rfl | inTail
          · exact Nat.le_refl _
          · exact tailCosts _ inTail
        have len := congrArg List.length same
        omega
      rw [← List.cons_append, List.map_append]
      exact List.nodup_append.mpr ⟨leftNodup, remaining.2, cross⟩
    · intro π member
      rcases List.mem_append.mp member with inPlateau | inTail
      · exact Nat.le_of_eq (costs _ inPlateau)
      · apply Nat.le_trans _ (Nat.le_of_lt strict)
        rcases List.mem_cons.mp inTail with rfl | inMore
        · exact Nat.le_refl _
        · exact tailCosts _ inMore
termination_by (graphKey independent start).length
decreasing_by exact strict

/-- Faithfulness for the distinct singleton queries used by the order search. -/
def FaithfulTo (independent : CIOracle n) (G : DAG n) : Prop :=
  ∀ x y condition, x ≠ y → condition x = false → condition y = false →
    (independent x y condition = true ↔ graphOracle G x y condition = true)

theorem FaithfulTo.is_markov {independent : CIOracle n} {G : DAG n} (faithful : FaithfulTo independent G) :
    IsMarkov G independent := fun x y c distinct left right sep =>
  (faithful x y c distinct left right).mpr sep

theorem FaithfulTo.superset {independent : CIOracle n} {G H : DAG n}
    (faithful : FaithfulTo independent G) (markov : IsMarkov H independent) : SeparationSubset H G :=
  fun x y c different left right sep =>
    (faithful x y c different left right).mp (markov x y c different left right sep)

theorem backward_sequence_arrow_count_le {G H : DAG n} (seq : BackwardSequence H G) :
    arrowCount H ≤ arrowCount G := by
  induction seq with
  | done same => exact Nat.le_of_eq (by simp [arrowCount, same])
  | reverse r _ h => exact Nat.le_trans h (Nat.le_of_eq (arrow_count_eq_of_reversal r).symm)
  | delete arrow _ h => exact Nat.le_trans h (Nat.le_of_lt (delete_arrow_decreases_count arrow))

/-- If a transformation entails a strict inclusion, it deletes an arrow. -/
theorem backward_sequence_strict_arrow_count {G H : DAG n}
    (seq : BackwardSequence H G) (strict : ¬ SeparationSubset H G) : arrowCount H < arrowCount G := by
  induction seq with
  | done same => exact (strict (.of_edge_eq same.symm)).elim
  | reverse rev _ ih =>
    rw [arrow_count_eq_of_reversal rev]
    exact ih (fun back => strict (back.trans (.of_reversal rev.symm)))
  | delete arrow rest _ =>
    exact Nat.lt_of_le_of_lt (backward_sequence_arrow_count_le rest) (delete_arrow_decreases_count arrow)

private theorem improve_preserves_edge_count (independent : CIOracle n) (depth : Nat) (tier : Tier)
    (order : List (Fin n)) : arrowCount (graph independent (improve independent tier depth order)) ≤
      arrowCount (graph independent order) := by
  simpa only [improve, graphKey_length] using
    (Search.descend_spec (moves independent tier) (fun π => (graphKey independent π).length)
      (graphKey independent) depth order).1

private theorem tier_edge_count_le_covered (independent : CIOracle n) (depth : Nat) (tier : Tier)
    (initial : List (Fin n)) : arrowCount (graph independent (search independent depth tier initial)) ≤
      arrowCount (graph independent (search independent depth .covered initial)) := by
  cases tier with
  | covered => exact Nat.le_refl _
  | singular => exact improve_preserves_edge_count independent depth .singular _
  | all =>
    exact Nat.le_trans (improve_preserves_edge_count independent depth .all _)
      (improve_preserves_edge_count independent depth .singular _)

/-- The oracle result in Corollary 4.6 for each tier. The two inclusions
are equality of the d-separation models. -/
theorem search_recovers_mec_of_faithful {independent : CIOracle n} {truth : DAG n}
    (transform : InclusionTransformation n)
    (markov : ∀ π, VertexOrder π → IsMarkov (graph independent π) independent)
    (faithful : FaithfulTo independent truth) (initial : List (Fin n)) (valid : VertexOrder initial)
    (tier : Tier) {depth : Nat} (deep : (allOrders n).length ≤ depth) :
    let result := graph independent (search independent depth tier initial)
    SeparationSubset result truth ∧ SeparationSubset truth result := by
  let covered := graph independent (search independent depth .covered initial)
  let result := graph independent (search independent depth tier initial)
  have coveredMinimal := covered_search_pminimal transform markov valid deep
  have forwardCovered := faithful.superset coveredMinimal.1
  have backCovered := coveredMinimal.2 truth faithful.is_markov forwardCovered
  have resultMarkov : IsMarkov result independent :=
    markov _ (valid.of_perm (search_perm_and_terminal independent depth tier initial).1)
  have forwardResult := faithful.superset resultMarkov
  refine ⟨forwardResult, ?_⟩
  have sameCount : arrowCount covered = arrowCount truth :=
    Nat.le_antisymm (backward_sequence_arrow_count_le (transform covered truth backCovered))
      (backward_sequence_arrow_count_le (transform truth covered forwardCovered))
  classical
  by_cases resultBack : SeparationSubset truth result
  · exact resultBack
  · have shorter := backward_sequence_strict_arrow_count (transform _ _ forwardResult) resultBack
    have resultCount := tier_edge_count_le_covered independent depth tier initial
    change arrowCount result ≤ arrowCount covered at resultCount
    omega

end

end OpenCausalScience.Papers.LamEtAl2022
