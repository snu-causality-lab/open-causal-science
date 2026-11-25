import Lean
import OpenCausalScience.Graph.MoralizationExecutable

open OpenCausalScience
open OpenCausalScience.Moralization
open OpenCausalScience.Papers.KimEtAl2026.BayesBallCorrectness

private def edgeIndex (u v : Fin 4) : Nat :=
  match u.val, v.val with
  | 0, 1 => 0
  | 0, 2 => 1
  | 0, 3 => 2
  | 1, 2 => 3
  | 1, 3 => 4
  | 2, 3 => 5
  | _, _ => 6

private def dag (edges : Fin 64) : DAG 4 where
  edge u v := decide (u.val < v.val) && edges.val.testBit (edgeIndex u v)
  rank := Fin.val
  edge_increases _ _ present := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at present
    exact present.1

private def label (query : Fin 256) (v : Fin 4) : Nat :=
  query.val / 4 ^ v.val % 4

private def graphVerdicts (edges : Fin 64) : List (Nat × Bool) :=
  (List.finRange 256).filterMap fun masks =>
    let G := dag edges
    let left := fun v => label masks v == 1
    let right := fun v => label masks v == 2
    let conditioned := fun v => label masks v == 3
    let query : Query G := ⟨left, right, Conditioning.ofPredicate G conditioned⟩
    if (List.finRange 4).any left && (List.finRange 4).any right then
      some (masks.val, query.dagMoralSeparated)
    else none

/- Enumerate all four-vertex DAGs with one fixed topological vertex order
and all pairwise disjoint set queries with nonempty left and right sets. -/
#eval IO.println ((Lean.toJson ((List.finRange 64).map fun mask =>
  (mask.val, graphVerdicts mask))).compress)
