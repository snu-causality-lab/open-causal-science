module
public import OpenCausalScience.Papers.Chickering2002.InclusionBound
public import OpenCausalScience.Papers.Chickering2002.InsertionBridges
public import OpenCausalScience.Papers.Chickering2002.RelevantInsertion
public import OpenCausalScience.Papers.Chickering2002.ShortcutInsertion

/-! # Preservation under the final two insertions

Chickering (2002), Appendix A, Lemma 30. With both insertion cases
available, the one-step construction supplies the transformation in Theorem 4.
-/

namespace OpenCausalScience.Papers.Chickering2002

open Discovery Moralization KimEtAl2026.BayesBallCorrectness

@[expose] public section

variable {n : Nat}

/-- Step 8 preserves the independence-map order. The parent X of Z is
chosen distinct from Y, as required by the unshielded collider argument. -/
theorem step_eight_preserves_inclusion : Step8Preserves n := by
  intro G H K x y z d map selection _ different parent _ edit
  intro a b C _ offA offB separation
  apply (graphOracle_eq_true_iff K a b C offA offB).mpr
  intro route
  apply (graphOracle_eq_true_iff H a b C offA offB).mp separation
  by_cases conditionedY : C y = true
  · exact step_eight_conditioned_connection map selection.target_sink different parent
      selection.child edit C conditionedY route
  have offY := Bool.eq_false_iff.mpr conditionedY
  by_cases conditionedDescendant : ∃ w, Ancestor G z w ∧ C w = true
  · obtain ⟨w, descendant, conditioned⟩ := conditionedDescendant
    exact map.dConnection C a b (step_eight_conditioned_descendant_connection parent selection.child
      edit C offY descendant conditioned route)
  have descendantsOutside (w : Fin n) (descendant : Ancestor G z w) : C w = false :=
    Bool.eq_false_iff.mpr fun conditioned => conditionedDescendant ⟨w, descendant, conditioned⟩
  by_cases existing : Connected G C a b
  · exact map.dConnection C a b existing
  rcases insertion_connection_split edit C route with old | ⟨u, v, atU, atV, _, left, right⟩
  · exact (existing old).elim
  have boundary {w : Fin n} (atEnd : InsertionSegmentEnd G C x y w) : w = x ∨ w = y := by
    simpa [InsertionSegmentEnd, offY] using atEnd
  exact step8_unconditioned_without_conditioned_descendant map selection parent edit
    descendantsOutside route existing (boundary atU) (boundary atV) left right

/-- Apply-Edge-Operation produces an insertion or covered reversal
preserving the independence-map order for every distinct pair. -/
theorem forward_progress (G H : DAG n) (map : IndependenceMap G H)
    (different : G.edge ≠ H.edge) : ∃ K, ForwardStep H G K :=
  forward_progress_of_parent_completion
    (fun _ _ _ _ _ _ _ included selected xy _ edit =>
      step_seven_preserves_inclusion included selected.target_sink xy selected.child edit)
    step_eight_preserves_inclusion G H map different

/-- The finite DAG inclusion transformation, with the `r + 2m` bound
and target inclusion preserved after every operation. -/
theorem bounded_inclusion_transformation (G H : DAG n) (map : IndependenceMap G H) :
    ∃ k, k ≤ operationBound G H ∧ ForwardSequence H G k :=
  bounded_forward_sequence_of_progress forward_progress G H map

/-- The inclusion transformation of Theorem 4, read backwards. -/
theorem inclusion_transformation (n : Nat) : InclusionTransformation n := by
  intro G H map
  obtain ⟨_, _, sequence⟩ := bounded_inclusion_transformation G H map
  exact sequence.to_backward

end

end OpenCausalScience.Papers.Chickering2002
