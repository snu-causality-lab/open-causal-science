module
public import OpenCausalScience.Papers.RaskuttiUhler2018.SparsestPermutation
public import OpenCausalScience.Papers.VermaPearl1990.Equivalence
public import OpenCausalScience.Graph.DirectedEdgeEdit

/-! # The independence-map order and backward transformations

Chickering (2002), Theorem 4. Forward inclusion transformations add arrows
and reverse covered arrows. Read backwards, they delete arrows and reverse
covered arrows. The common topological order case uses only deletions.
-/

namespace OpenCausalScience.Papers.Chickering2002

open Discovery RaskuttiUhler2018 LamEtAl2022
open Chickering1995.CoveredReversal Chickering1995.Transformation
open VermaPearl1990.DAGEquivalence VermaPearl1990.Equivalence
open KimEtAl2026.BayesBall KimEtAl2026.BayesBallCorrectness

@[expose] public section

variable {n : Nat}

/-- Chickering's `G ≤ H`: every graphical independence of `H` holds in `G`. -/
def IndependenceMap (G H : DAG n) : Prop := IsMarkov H (graphOracle G)

namespace IndependenceMap

variable {G H K : DAG n}

theorem of_same_dConnections (same : SameDConnections G H) : IndependenceMap G H := by
  intro x y condition _ hx hy sep
  exact (graphOracle_eq_true_iff G x y condition hx hy).mpr
    fun connected => (graphOracle_eq_true_iff H x y condition hx hy).mp sep
      ((same condition x y).mp connected)

theorem refl (G : DAG n) : IndependenceMap G G := fun _ _ _ _ _ _ sep => sep

theorem trans (first : IndependenceMap G H) (second : IndependenceMap H K) : IndependenceMap G K :=
  fun x y condition distinct hx hy sep => first x y condition distinct hx hy
    (second x y condition distinct hx hy sep)

theorem of_edge_subset (subset : ∀ u v, G.edge u v = true → H.edge u v = true) : IndependenceMap G H :=
  fun _ _ _ _ hx hy sep => graphOracle_of_edge_subset subset hx hy sep

theorem dConnection (map : IndependenceMap G H) (condition : Fin n → Bool)
    (x y : Fin n) (connected : DConnected (Conditioning.ofPredicate G condition) x y) :
    DConnected (Conditioning.ofPredicate H condition) x y := by
  by_cases same : x = y
  · subst y
    exact ⟨connected.1, connected.2.1, [], .up, .nil _, by simp⟩
  · apply Classical.byContradiction
    intro separated
    exact (graphOracle_eq_true_iff G x y condition connected.1 connected.2.1).mp
      (map x y condition same connected.1 connected.2.1
        ((graphOracle_eq_true_iff H x y condition connected.1 connected.2.1).mpr separated)) connected

theorem same_dConnections (forward : IndependenceMap G H) (reverse : IndependenceMap H G) :
    SameDConnections G H :=
  fun condition x y => ⟨forward.dConnection condition x y, reverse.dConnection condition x y⟩

theorem edge_subset_of_common_order (map : IndependenceMap G H) (order : Fin n → Nat)
    (unique : ∀ x y, order x = order y → x = y)
    (firstTopo : ∀ u v, G.edge u v = true → order u < order v)
    (secondTopo : ∀ u v, H.edge u v = true → order u < order v) :
    ∀ u v, G.edge u v = true → H.edge u v = true := by
  intro u v edge
  have selected : (orderDAG order (graphOracle G)).edge u v = true := by
    rw [orderDAG_recovers_graphOracle order unique firstTopo]
    exact edge
  exact orderDAG_subgraph_of_markov order unique secondTopo map selected

end IndependenceMap

/-- A path of elementary moves from the current DAG to a more constrained DAG. -/
inductive BackwardSequence (target : DAG n) : DAG n → Prop
  | done {G} : G.edge = target.edge → BackwardSequence target G
  | reverse {G H u v} : Reversal G H u v → BackwardSequence target H → BackwardSequence target G
  | delete {G u v} : G.edge u v = true → BackwardSequence target (G.deleteArrow u v) →
      BackwardSequence target G

/-- The existence part of Chickering's inclusion transformation, read backwards. -/
def InclusionTransformation (n : Nat) : Prop :=
  ∀ G H : DAG n, IndependenceMap G H → BackwardSequence G H

theorem delete_arrow_decreases_count {G : DAG n} {u v : Fin n} (arrow : G.edge u v = true) :
    arrowCount (G.deleteArrow u v) < arrowCount G := by
  apply arrow_count_lt_of_strict_subset (u := u) (v := v) _ _ arrow
  · exact fun a b edge => ((G.deleteArrow_edge_iff u v a b).mp edge).1
  · simp [DAG.deleteArrow]

theorem BackwardSequence.implies_map {G H : DAG n} (path : BackwardSequence G H) :
    IndependenceMap G H := by
  induction path with
  | done same => exact .of_same_dConnections (same_dConnections_of_edge_eq same.symm)
  | reverse rev _ ih => exact ih.trans (.of_same_dConnections (sameDConnections_of_reversal rev.symm))
  | delete _ _ ih =>
    exact ih.trans (.of_edge_subset fun _ _ arrow => (Bool.and_eq_true_iff.mp arrow).1)

theorem backward_sequence_of_edge_subset {G H : DAG n}
    (subset : ∀ u v, G.edge u v = true → H.edge u v = true) : BackwardSequence G H := by
  classical
  by_cases same : H.edge = G.edge
  · exact .done same
  · have existsExtra : ∃ u v, H.edge u v = true ∧ G.edge u v = false := by
      apply Classical.byContradiction
      intro absent
      apply same
      funext u v
      apply Bool.eq_iff_iff.mpr
      refine ⟨fun edge => ?_, subset u v⟩
      cases current : G.edge u v with
      | true => rfl
      | false => exact (absent ⟨u, v, edge, current⟩).elim
    obtain ⟨u, v, extra, absent⟩ := existsExtra
    have subsetAfter (a b : Fin n) (edge : G.edge a b = true) : (H.deleteArrow u v).edge a b = true := by
      rw [DAG.deleteArrow_edge_iff]
      exact ⟨subset a b edge, fun ⟨ha, hb⟩ => Bool.false_ne_true (absent.symm.trans (ha ▸ hb ▸ edge))⟩
    exact .delete extra (backward_sequence_of_edge_subset subsetAfter)
termination_by arrowCount H
decreasing_by exact delete_arrow_decreases_count extra

/-- The common-topological-order case of Theorem 4. -/
theorem backward_sequence_of_common_order {G H : DAG n} (map : IndependenceMap G H)
    (order : Fin n → Nat) (unique : ∀ x y, order x = order y → x = y)
    (firstTopo : ∀ u v, G.edge u v = true → order u < order v)
    (secondTopo : ∀ u v, H.edge u v = true → order u < order v) : BackwardSequence G H :=
  backward_sequence_of_edge_subset (map.edge_subset_of_common_order order unique firstTopo secondTopo)

end

end OpenCausalScience.Papers.Chickering2002
