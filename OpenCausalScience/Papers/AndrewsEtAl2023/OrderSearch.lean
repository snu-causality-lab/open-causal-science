module
public import OpenCausalScience.Papers.AndrewsEtAl2023.BestMove
public import OpenCausalScience.Papers.AndrewsEtAl2023.GrowShrinkTree

/-! # BOSS order search with the grow–shrink projection score -/

namespace OpenCausalScience.Papers.AndrewsEtAl2023.OrderSearch

open BestMove GrowShrinkTree

@[expose] public section

variable {n : Nat}

/-- The score of an order is the sum of the projected local scores. -/
def score (scores : Fin n → LocalScore n) (order : List (Fin n)) : Rat :=
  ((List.finRange n).map fun child => (projectVertex scores order.idxOf child).score).sum

def selectedOrder (scores : Fin n → LocalScore n) (initial : List (Fin n)) : List (Fin n) :=
  BestMove.search (score scores) initial

/-- The DAG at the end of the order-search phase of Algorithm 4. -/
def selectedDAG (scores : Fin n → LocalScore n) (initial : List (Fin n)) : DAG n :=
  project scores (selectedOrder scores initial).idxOf

theorem selected_order_perm_and_locally_optimal (scores : Fin n → LocalScore n)
    (initial : List (Fin n)) :
    (selectedOrder scores initial).Perm initial ∧ RelocationOptimal (score scores) (selectedOrder scores initial) :=
  search_perm_and_locally_optimal (score scores) initial

theorem selected_dag_uses_projected_parents (scores : Fin n → LocalScore n) (initial : List (Fin n))
    (u v : Fin n) :
    (selectedDAG scores initial).edge u v = true ↔
      u ∈ (growShrink (scores v) (precedesVertex (selectedOrder scores initial).idxOf v)
        ((List.finRange n).erase v) []).parents := by
  simp [selectedDAG, project, project_vertex_eq_uncached]

end

end OpenCausalScience.Papers.AndrewsEtAl2023.OrderSearch
