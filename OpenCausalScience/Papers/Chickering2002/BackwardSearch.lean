module
public import OpenCausalScience.Papers.Chickering2002.IndependenceMap

/-! # Backward equivalence search

Chickering (2002), Lemma 10. We represent a backward neighbor by an arrow
deletion from a DAG in the current equivalence class. All strict-improvement
selections have the same correctness guarantee when the inclusion
transformation and the deletion score comparisons hold.
-/

namespace OpenCausalScience.Papers.Chickering2002

open LamEtAl2022
open Chickering1995.CoveredReversal Chickering1995.Transformation
open VermaPearl1990.DAGEquivalence VermaPearl1990.Equivalence

@[expose] public section

variable {n : Nat}

/-- The deletion neighborhood is taken over all representatives of the current MEC. -/
def DeletionNeighbor (G H : DAG n) : Prop :=
  ∃ R, SameDConnections G R ∧ ∃ u v, R.edge u v = true ∧ H = R.deleteArrow u v

theorem DeletionNeighbor.of_representative {G R H : DAG n} (same : SameDConnections G R)
    (step : DeletionNeighbor R H) : DeletionNeighbor G H := by
  obtain ⟨T, eqv, u, v, edge, rfl⟩ := step
  exact ⟨T, fun c x y => (same c x y).trans (eqv c x y), u, v, edge, rfl⟩

theorem DeletionNeighbor.decreases_count {G H : DAG n} (step : DeletionNeighbor G H) :
    arrowCount H < arrowCount G := by
  obtain ⟨R, eqv, u, v, edge, rfl⟩ := step
  have seq := reversal_sequence eqv
  have count : arrowCount G = arrowCount R := by
    clear eqv
    induction seq with
    | done same => simp [arrowCount, same]
    | next _ reversal _ ih => exact (arrow_count_eq_of_reversal reversal).trans ih
  rw [count]
  exact delete_arrow_decreases_count edge

/-- From a nonterminal I-map, Theorem 4 supplies a backward neighbor that
still contains the true model. This is the first deletion when reading the
transformation backwards through its final covered reversals. -/
theorem first_deletion_toward_target {G H : DAG n} (steps : BackwardSequence G H)
    (different : ¬ SameDConnections H G) :
    ∃ next, DeletionNeighbor H next ∧ IndependenceMap G next := by
  induction steps with
  | done equal => exact (different (same_dConnections_of_edge_eq equal)).elim
  | reverse reversal _ ih =>
    have equiv := sameDConnections_of_reversal reversal
    obtain ⟨next, step, keeps⟩ := ih (fun eqv => different (fun c x y => (equiv c x y).trans (eqv c x y)))
    exact ⟨next, step.of_representative equiv, keeps⟩
  | @delete current u v present rest _ =>
    exact ⟨current.deleteArrow u v, ⟨current, fun _ _ _ => Iff.rfl, u, v, present, rfl⟩,
      rest.implies_map⟩

/-- The score comparisons used by BES in the large-sample argument. A deletion
from a containing DAG improves the score exactly when the smaller DAG still
contains the true model. A covered reversal leaves the score unchanged. -/
structure DeletionScoreConsistent (truth : DAG n) (score : DAG n → Rat) : Prop where
  equivalent : ∀ G H, SameDConnections G H → score G = score H
  gain_iff : ∀ (G : DAG n) (u v : Fin n), G.edge u v = true → IndependenceMap truth G →
    (score G < score (G.deleteArrow u v) ↔ IndependenceMap truth (G.deleteArrow u v))

theorem DeletionScoreConsistent.neighbor_gain_iff {truth : DAG n} {score : DAG n → Rat}
    (consistent : DeletionScoreConsistent truth score) {G H : DAG n}
    (contains : IndependenceMap truth G) (step : DeletionNeighbor G H) :
    score G < score H ↔ IndependenceMap truth H := by
  obtain ⟨R, eqv, u, v, present, rfl⟩ := step
  rw [consistent.equivalent G R eqv]
  exact consistent.gain_iff R u v present (contains.trans (.of_same_dConnections eqv))

def BetterDelete (score : DAG n → Rat) (G H : DAG n) : Prop :=
  DeletionNeighbor G H ∧ score G < score H

def BackwardTerminal (score : DAG n → Rat) (G : DAG n) : Prop :=
  ∀ H, ¬ BetterDelete score G H

inductive BackwardRun (score : DAG n → Rat) : DAG n → DAG n → Prop
  | done (G) : BackwardRun score G G
  | next {G H result} : BetterDelete score G H → BackwardRun score H result → BackwardRun score G result

theorem BackwardRun.contains {truth G H : DAG n} {score : DAG n → Rat}
    (path : BackwardRun score G H) (contains : IndependenceMap truth G)
    (consistent : DeletionScoreConsistent truth score) : IndependenceMap truth H := by
  induction path with
  | done _ => exact contains
  | next step _ ih => exact ih ((consistent.neighbor_gain_iff contains step.1).mp step.2)

/-- Reference selection of an improving neighbor. Counting arrows supplies
the termination argument for any order of strict-improvement choices. -/
noncomputable def backwardSearch (score : DAG n → Rat) (G : DAG n) :
    {H : DAG n // BackwardRun score G H ∧ BackwardTerminal score H} := by
  classical
  by_cases progress : ∃ H, BetterDelete score G H
  · let H := Classical.choose progress
    have improve : BetterDelete score G H := Classical.choose_spec progress
    let result := backwardSearch score H
    exact ⟨result.val, .next improve result.property.1, result.property.2⟩
  · exact ⟨G, .done G, fun H step => progress ⟨H, step⟩⟩
termination_by arrowCount G
decreasing_by exact improve.1.decreases_count

/-- Backward search from a containing graph has the generative MEC as its
only possible terminal class under the inclusion transformation and the
score comparisons used in Chickering's Lemma 10. -/
theorem backward_terminal_is_perfect {truth G : DAG n} {score : DAG n → Rat}
    (transform : InclusionTransformation n) (consistent : DeletionScoreConsistent truth score)
    (contains : IndependenceMap truth G) (terminal : BackwardTerminal score G) :
    SameDConnections G truth := by
  apply Classical.byContradiction
  intro different
  obtain ⟨next, neighbor, keeps⟩ := first_deletion_toward_target (transform truth G contains) different
  exact terminal next ⟨neighbor, (consistent.neighbor_gain_iff contains neighbor).mpr keeps⟩

theorem backward_search_is_perfect {truth G : DAG n} {score : DAG n → Rat}
    (transform : InclusionTransformation n) (consistent : DeletionScoreConsistent truth score)
    (contains : IndependenceMap truth G) : SameDConnections (backwardSearch score G).val truth := by
  have result := (backwardSearch score G).property
  exact backward_terminal_is_perfect transform consistent (result.1.contains contains consistent) result.2

end

end OpenCausalScience.Papers.Chickering2002
