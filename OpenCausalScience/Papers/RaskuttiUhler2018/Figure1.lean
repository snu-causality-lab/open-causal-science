module
public import OpenCausalScience.Discovery.OrderDAG
public import OpenCausalScience.Graph.DSeparation

/-! # Figure 1 in the authors' sparsest permutation manuscript -/

namespace OpenCausalScience.Papers.RaskuttiUhler2018.Figure1

open OpenCausalScience.Discovery

@[expose] public section

/-- The four vertices use zero-based labels in Lean. -/
def cycle : DAG 4 where
  edge u v := (u == 0 && v == 1) || (u == 0 && v == 3) ||
    (u == 1 && v == 2) || (u == 2 && v == 3)
  rank u := u.val
  edge_increases := by decide +kernel

/-- The manuscript's d-separations together with the extra marginal CI
between the first and fourth variables. -/
def independent : CIOracle 4 := fun x y condition =>
  (cycle.dSeparated x y ((List.finRange 4).filter condition) == some true) ||
    (((x == 0 && y == 3) || (x == 3 && y == 0)) && (List.finRange 4).all (fun z => !condition z))

def original : DAG 4 := orderDAG Fin.val independent

def alternative : DAG 4 :=
  orderDAG (fun u => if u == 1 then 3 else if u == 3 then 1 else u.val) independent

def arrows (G : DAG 4) : List (Fin 4 × Fin 4) :=
  (List.finRange 4).flatMap fun u => ((List.finRange 4).filter (G.edge u)).map (u, ·)

theorem original_order_replays : arrows original = [(0, 1), (0, 3), (1, 2), (2, 3)] := by
  decide +kernel

theorem alternative_order_replays : arrows alternative = [(0, 1), (0, 2), (2, 1), (3, 2)] := by
  decide +kernel

theorem same_size_different_skeleton : (arrows original).length = (arrows alternative).length ∧
    original.edge 0 3 = true ∧ alternative.edge 0 3 = false ∧ alternative.edge 3 0 = false := by
  decide +kernel

end

end OpenCausalScience.Papers.RaskuttiUhler2018.Figure1
