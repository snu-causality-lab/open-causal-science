module
public import OpenCausalScience.Graph.MixedGraph

/-! # Finite mixed graphs for comparison with CGA -/

namespace OpenCausalScience.MixedReplayGraphs

private abbrev Marks (n : Nat) := Fin n → Bool → Fin n → Bool → Bool

private def symmetricEdge {n : Nat} (upper : Marks n)
    (u : Fin n) (a : Bool) (v : Fin n) (b : Bool) : Bool :=
  if u < v then upper u a v b
  else if v < u then upper v b u a
  else false

private theorem symmetricEdge_swap {n : Nat} (upper : Marks n)
    (u : Fin n) (a : Bool) (v : Fin n) (b : Bool) :
    symmetricEdge upper u a v b = symmetricEdge upper v b u a := by
  by_cases uv : u < v
  · have vu : ¬ v < u := by omega
    simp [symmetricEdge, uv, vu]
  · by_cases vu : v < u
    · simp [symmetricEdge, uv, vu]
    · simp [symmetricEdge, uv, vu]

private def noUndirectedArrow {n : Nat} (edge : Marks n) : Bool :=
  (List.finRange n).all fun u =>
    (List.finRange n).all fun v =>
      if edge u false v false then
        (List.finRange n).all fun w => !edge u true w false && !edge u true w true
      else true

private theorem noUndirectedArrow_sound {n : Nat} (edge : Marks n)
    (valid : noUndirectedArrow edge = true)
    {u v w : Fin n} {mark : Bool} (undirected : edge u false v false = true) :
    edge u true w mark = false := by
  have atVertex := List.all_eq_true.mp valid u (List.mem_finRange u)
  have atPair := List.all_eq_true.mp atVertex v (List.mem_finRange v)
  have noArrow : (List.finRange n).all
      (fun w => !edge u true w false && !edge u true w true) = true := by
    simpa [undirected] using atPair
  have atNeighbor := List.all_eq_true.mp noArrow w (List.mem_finRange w)
  cases mark
  · simpa using (Bool.and_eq_true_iff.mp atNeighbor).1
  · simpa using (Bool.and_eq_true_iff.mp atNeighbor).2

private def graphFromUpper {n : Nat} (upper : Marks n) : Option (MixedGraph n) :=
  if valid : noUndirectedArrow (symmetricEdge upper) = true then
    some {
      edge := symmetricEdge upper
      symmetric := symmetricEdge_swap upper
      loop_free := fun u a b => by simp [symmetricEdge]
      no_arrow_of_undirected := noUndirectedArrow_sound _ valid
    }
  else none

private def pairIndex (u v : Fin 3) : Nat :=
  match u.val, v.val with
  | 0, 1 => 0
  | 0, 2 => 1
  | _, _ => 2

private def admg3Upper (mask : Nat) : Marks 3 := fun u a v b =>
  let index := pairIndex u v
  b && (if a then mask.testBit (index + 3) else mask.testBit index)

private def ancestral3Upper (code : Nat) : Marks 3 := fun u a v b =>
  let mark := match a, b with
    | false, false => 1
    | false, true => 2
    | true, false => 3
    | true, true => 4
  code / 5 ^ pairIndex u v % 5 == mark

/- On three vertices an acyclic directed path between distinct endpoints
needs at most two edges. A directed cycle of length three is caught by
testing that an arrowhead does not point to an ancestor of the opposite
endpoint. -/
private def ancestorOfNeighbor (edge : Marks 3) (u v : Fin 3) : Bool :=
  edge u false v true ||
    (List.finRange 3).any fun w => edge u false w true && edge w false v true

public def ancestral3Graph (code : Nat) : Option (MixedGraph 3) := do
  let g ← graphFromUpper (ancestral3Upper code)
  let valid := (List.finRange 3).all fun u => (List.finRange 3).all fun v =>
    !(g.edge u true v false || g.edge u true v true) || !ancestorOfNeighbor g.edge u v
  if valid then some g else none

private def bow4Upper : Marks 4 := fun u a v b =>
  match u.val, v.val with
  | 0, 1 => b
  | 1, 2 => a && b
  | 1, 3 => !a && b
  | _, _ => false

private def ancestral4Upper : Marks 4 := fun u a v b =>
  match u.val, v.val with
  | 0, 1 => !a && !b
  | 1, 2 => !a && b
  | 2, 3 => a && b
  | _, _ => false

public def admg3Graph (mask : Nat) : Option (MixedGraph 3) :=
  graphFromUpper (admg3Upper mask)

public def bow4Graph : Option (MixedGraph 4) :=
  graphFromUpper bow4Upper

public def ancestral4Graph : Option (MixedGraph 4) :=
  graphFromUpper ancestral4Upper

end OpenCausalScience.MixedReplayGraphs
