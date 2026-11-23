module
public import OpenCausalScience.Separation

/-! # D-separation on four vertices

The collider, chain, and fork below share a skeleton. Each also contains
the edge `M → D`. The checks cover the collider queries and compare the
singleton d-separation results of the chain and fork on these four vertices.
-/

namespace OpenCausalScience.Examples

@[expose] public section

def x : Fin 4 := 0
def y : Fin 4 := 1
def m : Fin 4 := 2
def d : Fin 4 := 3

def colliderEdge (u v : Fin 4) : Bool :=
  (u == x && v == m) || (u == y && v == m) || (u == m && v == d)

def colliderRank (v : Fin 4) : Nat :=
  if v == m then 1 else if v == d then 2 else 0

/-- `X → M ← Y`, `M → D`. -/
def collider : DAG 4 where
  edge := colliderEdge
  rank := colliderRank
  edge_increases := by decide

def chainEdge (u v : Fin 4) : Bool :=
  (u == x && v == m) || (u == m && v == y) || (u == m && v == d)

def chainRank (v : Fin 4) : Nat :=
  if v == x then 0 else if v == m then 1 else 2

/-- `X → M → Y`, `M → D`. -/
def chain : DAG 4 where
  edge := chainEdge
  rank := chainRank
  edge_increases := by decide

def forkEdge (u v : Fin 4) : Bool :=
  u == m && (v == x || v == y || v == d)

def forkRank (v : Fin 4) : Nat :=
  if v == m then 0 else 1

/-- `X ← M → Y`, `M → D`. -/
def fork : DAG 4 where
  edge := forkEdge
  rank := forkRank
  edge_increases := by decide

theorem collider_separated_given_empty : collider.dSeparated x y [] = some true := by decide

theorem collider_connected_given_middle : collider.dSeparated x y [m] = some false := by decide

theorem collider_connected_given_descendant : collider.dSeparated x y [d] = some false := by decide

theorem coincident_endpoints_invalid : collider.dSeparated x x [] = none := by decide

theorem conditioned_endpoint_invalid : collider.dSeparated x y [y] = none := by decide

def subsets {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: rest =>
    let smaller := subsets rest
    smaller ++ smaller.map (a :: ·)

/-- Every ordered pair of distinct endpoints, with every subset of the other vertices. -/
def singletonQueries : List (Fin 4 × Fin 4 × List (Fin 4)) :=
  let vertices := List.ofFn (fun i : Fin 4 => i)
  vertices.flatMap fun source =>
    vertices.flatMap fun target =>
      if source = target then [] else
        let candidates := vertices.filter (fun v => v != source && v != target)
        (subsets candidates).map fun conditioned => (source, target, conditioned)

def singletonSignature (graph : DAG 4) : List (Option Bool) :=
  singletonQueries.map fun (source, target, conditioned) =>
    graph.dSeparated source target conditioned

theorem singleton_query_count : singletonQueries.length = 48 := by decide

theorem chain_fork_equal_singleton_signatures :
    singletonSignature chain = singletonSignature fork := by decide

theorem chain_collider_same_skeleton :
    ∀ u v, (chain.edge u v || chain.edge v u) = (collider.edge u v || collider.edge v u) := by
  decide

theorem collider_chain_distinguished_given_empty :
    collider.dSeparated x y [] ≠ chain.dSeparated x y [] := by decide

end

end OpenCausalScience.Examples
