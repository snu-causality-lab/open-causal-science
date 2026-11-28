module
public import OpenCausalScience.Papers.Chickering2002.CommonSink
public import OpenCausalScience.Papers.Chickering2002.InclusionProgress
public import OpenCausalScience.Papers.Chickering2002.InsertionAcyclicity

/-! # Selection of an operation in Chickering's inclusion transformation

The common-sink reduction lifts every certified edit back to the full graph.
The proof identifies a target sink and the source child chosen in Step 5.
The two remaining preservation claims are supplied for Steps 7 and 8. -/

namespace OpenCausalScience.Papers.Chickering2002

open LamEtAl2022 Moralization
open Chickering1995.CoveredReversal Chickering1995.FindEdge Chickering1995.Transformation
open VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n : Nat} {G H K : DAG n}

/-- Reattach a sink with its original parents to the edited graph on the
remaining vertices. -/
def restoreSink (original edited : DAG n) (s : Fin n) : DAG n where
  edge u v := if u = s then false else if v = s then original.edge u s else edited.edge u v
  rank v := if v = s then edited.rankBound else edited.rank v
  edge_increases u v edge := by
    by_cases uAt : u = s
    · simp [uAt] at edge
    · by_cases vAt : v = s
      · simpa [uAt, vAt] using edited.rank_lt_bound u
      · simp [uAt, vAt] at edge ⊢
        exact edited.edge_increases _ _ edge

private theorem self_edge_absent (G : DAG n) (u : Fin n) : G.edge u u = false :=
  Bool.eq_false_iff.mpr (fun e => G.no_directed_cycle u (.single e))

private theorem restore_is_sink (G K : DAG n) (s : Fin n) : IsSink (restoreSink G K s) s := by
  intro w
  simp [restoreSink]

private theorem restore_parents (G K : DAG n) (s p : Fin n) :
    (restoreSink G K s).edge p s = G.edge p s := by
  by_cases atS : p = s
  · subst p
    simp [restoreSink, self_edge_absent]
  · simp [restoreSink, atS]

private theorem away_isolate_eq (G : DAG n) {s u v : Fin n} (uOff : u ≠ s) (vOff : v ≠ s) :
    (isolateSink G s).edge u v = G.edge u v := by
  simp [isolateSink, uOff, vOff]

private theorem isolated_not_endpoint {G : DAG n} {s u v : Fin n}
    (edge : (isolateSink G s).edge u v = true) : u ≠ s ∧ v ≠ s := by
  have only := (Bool.and_eq_true_iff.mp edge).2
  simpa only [Bool.and_eq_true_iff, bne_iff_ne] using only

private theorem restore_map {s : Fin n} (sinkH : IsSink H s)
    (parentsEq : ∀ p, G.edge p s = H.edge p s) (included : IndependenceMap K (isolateSink H s)) :
    IndependenceMap (restoreSink G K s) H := by
  have sink := restore_is_sink G K s
  apply common_sink_lift sink sinkH
  · have first := independence_away_of_same_edges sink (H := K)
      (fun u v uOff vOff => by simp [restoreSink, uOff, vOff])
    have last := independence_away_of_same_edges (G := isolateSink H s) (H := H)
      (by intro w; simp [isolateSink]) (fun _ _ => away_isolate_eq H)
    intro Z x y xOff yOff zOff connected
    exact last Z x y xOff yOff zOff
      (included.dConnection Z x y (first Z x y xOff yOff zOff connected))
  · intro p edge
    rwa [restore_parents, parentsEq] at edge

/-- Lift a valid edit after removing a common sink with equal parents. -/
theorem lift_isolated_forward_step {s : Fin n} (sinkG : IsSink G s) (sinkH : IsSink H s)
    (parentsEq : ∀ p, G.edge p s = H.edge p s)
    (step : ForwardStep (isolateSink H s) (isolateSink G s) K) :
    ForwardStep H G (restoreSink G K s) := by
  have included := restore_map sinkH parentsEq step.map_held
  cases step with
  | @reverse x y chosen rev _ =>
    have ⟨xOff, yOff⟩ := isolated_not_endpoint chosen.1
    have forward : G.edge x y = true := (away_isolate_eq G xOff yOff).symm.trans chosen.1
    have target : H.edge y x = true := (away_isolate_eq H yOff xOff).symm.trans chosen.2
    apply ForwardStep.reverse ⟨forward, target⟩ _ included
    refine ⟨forward, by simpa [restoreSink, yOff, xOff] using rev.reverse, ?_, ?_⟩
    · intro u v notForward notReverse
      by_cases atU : u = s
      · subst u
        simp [restoreSink, sinkG v]
      · by_cases atV : v = s
        · subst v
          simp [restoreSink, atU]
        · simpa [restoreSink, atU, atV, away_isolate_eq G atU atV] using
            rev.unchanged u v notForward notReverse
    · intro u neX neY
      by_cases atU : u = s
      · subst u
        simp [sinkG x, sinkG y]
      · simpa only [away_isolate_eq G atU xOff, away_isolate_eq G atU yOff] using rev.parents u neX neY
  | @insert x y fresh insertion map =>
    have present : K.edge x y = true := (insertion x y).mpr (.inr ⟨rfl, rfl⟩)
    have adjacent := map.adjacent (x := x) (y := y) (.inl present)
    have ⟨xOff, yOff⟩ := adjacent.elim isolated_not_endpoint
      (fun opposite => (isolated_not_endpoint opposite).symm)
    apply ForwardStep.insert (u := x) (v := y) ?_ ?_ included
    · simpa only [away_isolate_eq G xOff yOff] using fresh
    · intro u v
      by_cases atU : u = s
      · subst u
        have different : s ≠ x := xOff.symm
        simp [restoreSink, different, sinkG v]
      · by_cases atV : v = s
        · subst v
          have different : s ≠ y := yOff.symm
          simp [restoreSink, atU, different]
        · simpa [restoreSink, atU, atV, away_isolate_eq G atU atV] using insertion u v


/-- The child selected in Step 5 is maximal among the children that reach
the unique root of the source descendant set in the target. -/
structure SelectedDescendantChild (G H : DAG n) (y z d : Fin n) : Prop where
  target_sink : IsSink H y
  descendant_root : DescendantRoot G H y d
  child : G.edge y z = true
  reaches : G.ancestor z d
  maximal : ∀ w, G.edge y w = true → G.ancestor w d → ¬ G.DirectedWalk w z

/-- Step 7 asks for preservation when a parent of Y is added to Z. -/
def Step7Preserves (n : Nat) : Prop :=
  ∀ (G H K : DAG n) (x y z d : Fin n), IndependenceMap G H → SelectedDescendantChild G H y z d →
    G.edge x y = true → G.edge x z = false → G.IsInsertion K x z → IndependenceMap K H

/-- Step 8 asks for preservation when an additional parent of Z, distinct
from Y, is added to Y. Every parent of Y already parents Z. -/
def Step8Preserves (n : Nat) : Prop :=
  ∀ (G H K : DAG n) (x y z d : Fin n), IndependenceMap G H → SelectedDescendantChild G H y z d →
    (∀ p, G.edge p y = true → G.edge p z = true) → x ≠ y →
    G.edge x z = true → G.edge x y = false → G.IsInsertion K x y → IndependenceMap K H

private theorem child_exists_of_not_sink {G : DAG n} {y : Fin n} (notSink : ¬ IsSink G y) :
    ∃ z, G.edge y z = true := by
  apply Classical.byContradiction
  intro noChild
  exact notSink (fun z => Bool.eq_false_iff.mpr fun edge => noChild ⟨z, edge⟩)

private theorem walk_begins_with_child {G : DAG n} {y d : Fin n} (path : G.DirectedWalk y d) :
    ∃ z, G.edge y z = true ∧ G.ancestor z d := by
  induction path with
  | single arrow => exact ⟨_, arrow, .inl rfl⟩
  | extend _ arrow ih =>
    obtain ⟨z, child, same | rest⟩ := ih
    · exact ⟨z, child, .inr (.single (same.symm ▸ arrow))⟩
    · exact ⟨z, child, .inr (.extend rest arrow)⟩

private theorem walk_of_sink_false {G : DAG n} {y z : Fin n} (sink : IsSink G y)
    (path : G.DirectedWalk y z) : False := by
  obtain ⟨u, child, _⟩ := walk_begins_with_child path
  exact Bool.false_ne_true ((sink u).symm.trans child)

private theorem maximal_child_reaching {G : DAG n} (y d z : Fin n)
    (child : G.edge y z = true) (reaches : G.ancestor z d) :
    ∃ chosen, G.edge y chosen = true ∧ G.ancestor chosen d ∧
      ∀ w, G.edge y w = true → G.ancestor w d → ¬ G.DirectedWalk w chosen := by
  classical
  by_cases preceding : ∃ w, G.edge y w = true ∧ G.ancestor w d ∧ G.DirectedWalk w z
  · obtain ⟨w, wChild, wReaches, earlier⟩ := preceding
    exact maximal_child_reaching y d w wChild wReaches
  · exact ⟨z, child, reaches, fun w isChild path earlier => preceding ⟨w, isChild, path, earlier⟩⟩
termination_by G.rank z
decreasing_by exact G.rank_lt_of_directedWalk earlier

/-- A suitable maximal child exists whenever the target sink still has a
child in the source graph. -/
theorem select_descendant_child {G H : DAG n} {y : Fin n} (included : IndependenceMap G H)
    (targetSink : IsSink H y) (sourceNotSink : ¬ IsSink G y) :
    ∃ z d, SelectedDescendantChild G H y z d := by
  obtain ⟨a, child⟩ := child_exists_of_not_sink sourceNotSink
  obtain ⟨d, root, _, allReach⟩ := included.unique_descendant_root y
  have notEqual : y ≠ d := by
    intro eq
    subst d
    rcases allReach a (.inr (.single child)) with equal | path
    · subst a
      exact G.no_directed_cycle y (.single child)
    · exact walk_of_sink_false targetSink path
  have nonempty : G.DirectedWalk y d := root.1.resolve_left notEqual
  obtain ⟨z, first, toD⟩ := walk_begins_with_child nonempty
  obtain ⟨chosen, isChild, reaches, maximal⟩ := maximal_child_reaching y d z first toD
  exact ⟨chosen, d, ⟨targetSink, root, isChild, reaches, maximal⟩⟩

private theorem fresh_extra_parent {G : DAG n} {y z : Fin n}
    (notCovered : ¬ ∀ p, p ≠ y → p ≠ z → (G.edge p y = true ↔ G.edge p z = true))
    (included : ∀ p, G.edge p y = true → G.edge p z = true) :
    ∃ x, x ≠ y ∧ G.edge x z = true ∧ G.edge x y = false := by
  apply Classical.byContradiction
  intro notExtra
  apply notCovered
  intro p neY _
  refine ⟨included p, fun edge => ?_⟩
  cases incoming : G.edge p y with
  | false => exact (notExtra ⟨p, neY, edge, incoming⟩).elim
  | true => rfl

private theorem progress_at_nonsink_source (seven : Step7Preserves n) (eight : Step8Preserves n)
    {G H : DAG n} {y : Fin n} (included : IndependenceMap G H) (targetSink : IsSink H y)
    (sourceNotSink : ¬ IsSink G y) : ∃ K, ForwardStep H G K := by
  classical
  obtain ⟨z, d, chosen⟩ := select_descendant_child included targetSink sourceNotSink
  have opposite : H.edge z y = true := by
    rcases included.adjacent (.inl chosen.child) with forward | reverse
    · exact (Bool.false_ne_true ((targetSink z).symm.trans forward)).elim
    · exact reverse
  by_cases covered : ∀ p, p ≠ y → p ≠ z → (G.edge p y = true ↔ G.edge p z = true)
  · let K := Reversal.flip G y z chosen.child covered
    have reversal : Reversal G K y z := Reversal.flip_is_covered_reversal G y z chosen.child covered
    have kept : IndependenceMap K H :=
      (IndependenceMap.of_same_dConnections (sameDConnections_of_reversal reversal.symm)).trans included
    exact ⟨K, .reverse ⟨chosen.child, opposite⟩ reversal kept⟩
  · by_cases additive : ∃ x, G.edge x y = true ∧ G.edge x z = false
    · obtain ⟨x, parent, missing⟩ := additive
      obtain ⟨K, insertion⟩ := insert_shortcut_acyclic (.extend (.single parent) chosen.child)
      exact ⟨K, .insert missing insertion (seven G H K x y z d included chosen parent missing insertion)⟩
    · have allParents (p : Fin n) (parent : G.edge p y = true) : G.edge p z = true := by
        cases h : G.edge p z with
        | false => exact (additive ⟨p, parent, h⟩).elim
        | true => rfl
      obtain ⟨x, different, parent, missing⟩ := fresh_extra_parent covered allParents
      obtain ⟨K, insertion⟩ := insert_parent_of_maximal_child_acyclic different parent chosen.reaches chosen.maximal
      exact ⟨K, .insert missing insertion (eight G H K x y z d included chosen allParents different parent missing insertion)⟩

private theorem exists_sink_with_parent {H : DAG n} (v : Fin n) (parent : ∃ p, H.edge p v = true) :
    ∃ y, IsSink H y ∧ ∃ p, H.edge p y = true := by
  classical
  by_cases sink : IsSink H v
  · exact ⟨v, sink, parent⟩
  · obtain ⟨w, child⟩ := child_exists_of_not_sink sink
    exact exists_sink_with_parent w ⟨v, child⟩
termination_by H.rankBound - H.rank v
decreasing_by
  have larger := H.edge_increases _ _ child
  have bound := H.rank_lt_bound w
  omega

private theorem target_has_edge {G H : DAG n} (included : IndependenceMap G H) (different : G.edge ≠ H.edge) :
    ∃ u v, H.edge u v = true := by
  apply Classical.byContradiction
  intro empty
  apply different
  funext u v
  have noH : H.edge u v = false := Bool.eq_false_iff.mpr (fun edge => empty ⟨u, v, edge⟩)
  have noG : G.edge u v = false := Bool.eq_false_iff.mpr (fun arrow =>
    (included.adjacent (.inl arrow)).elim (fun h => empty ⟨u, v, h⟩) (fun h => empty ⟨v, u, h⟩))
  exact noG.trans noH.symm

private theorem unequal_after_isolation {G H : DAG n} {s : Fin n} (sinkG : IsSink G s)
    (sinkH : IsSink H s) (parents : ∀ p, G.edge p s = H.edge p s) (different : G.edge ≠ H.edge) :
    (isolateSink G s).edge ≠ (isolateSink H s).edge := by
  intro equal
  apply different
  funext u v
  by_cases atU : u = s
  · subst u
    rw [sinkG v, sinkH v]
  · by_cases atV : v = s
    · subst v
      exact parents u
    · simpa only [away_isolate_eq G atU atV, away_isolate_eq H atU atV] using congrFun (congrFun equal u) v

private theorem no_equal_parents_implies_extra {G H : DAG n} {s : Fin n} (sinkH : IsSink H s)
    (included : IndependenceMap G H) (different : ¬ ∀ p, G.edge p s = H.edge p s) :
    ∃ p, G.edge p s = false ∧ H.edge p s = true := by
  apply Classical.byContradiction
  intro noneExtra
  apply different
  intro p
  apply Bool.eq_iff_iff.mpr
  refine ⟨parent_subset_of_map_at_sink sinkH included, fun edge => ?_⟩
  cases present : G.edge p s with
  | false => exact (noneExtra ⟨p, present, edge⟩).elim
  | true => rfl

/-- The source's operation selection reduces to Steps 7 and 8. Removing a
common sink with a parent strictly reduces the target arrow count. -/
theorem forward_progress_of_parent_completion (seven : Step7Preserves n) (eight : Step8Preserves n)
    (G H : DAG n) (included : IndependenceMap G H) (different : G.edge ≠ H.edge) :
    ∃ K, ForwardStep H G K := by
  classical
  obtain ⟨u, v, edge⟩ := target_has_edge included different
  obtain ⟨s, sinkH, p, parent⟩ := exists_sink_with_parent v ⟨u, edge⟩
  by_cases sinkG : IsSink G s
  · by_cases parents : ∀ x, G.edge x s = H.edge x s
    · have kept := (common_sink_reduction_iff sinkG sinkH parents).mp included
      obtain ⟨edited, operation⟩ := forward_progress_of_parent_completion seven eight (isolateSink G s)
        (isolateSink H s) kept (unequal_after_isolation sinkG sinkH parents different)
      exact ⟨restoreSink G edited s, lift_isolated_forward_step sinkG sinkH parents operation⟩
    · obtain ⟨x, missing, extra⟩ := no_equal_parents_implies_extra sinkH included parents
      obtain ⟨edited, addition, kept⟩ := exists_insert_to_common_sink sinkG sinkH included extra
      exact ⟨edited, .insert missing addition kept⟩
  · exact progress_at_nonsink_source seven eight included sinkH sinkG
termination_by arrowCount H
decreasing_by
  exact arrow_count_lt_of_strict_subset (fun _ _ arrow => (Bool.and_eq_true_iff.mp arrow).1)
    (by simp [isolateSink]) parent

end

end OpenCausalScience.Papers.Chickering2002
