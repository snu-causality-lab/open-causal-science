module
public import OpenCausalScience.Graph.MixedGraph

/-! # The graph recursion in Identify

Tian and Pearl, R-290-L, Figure 7. The input current set induces one
c-component and contains the connected target. The graph plan either
marginalizes to the target, reaches an ancestor fixed point, or
marginalizes and restricts to the c-component containing the target
before recurring. The recursion decreases the current set size.
Source: https://ftp.cs.ucla.edu/pub/stat_ser/R290-L.pdf#page=26
-/

namespace OpenCausalScience.Papers.TianPearl2003.IdentifyRecurrence

@[expose] public section

variable {n : Nat}

abbrev Vertices (n : Nat) := List (Fin n)

def close (edge : Fin n → Fin n → Bool) (current visited : Vertices n) :
    Nat → Vertices n
  | 0 => visited
  | rounds + 1 => close edge current
      (current.filter fun v => visited.contains v || visited.any (fun u => edge u v)) rounds

def ancestors (graph : MixedGraph n) (current target : Vertices n) : Vertices n :=
  let reverseArrow u v := graph.edge v false u true
  let visited := close reverseArrow current (current.filter target.contains) current.length
  current.filter visited.contains

def district (graph : MixedGraph n) (current : Vertices n) (vertex : Fin n) : Vertices n :=
  let spouse u v := graph.edge u true v true
  let visited := close spouse current (current.filter (· == vertex)) current.length
  current.filter visited.contains

def sameVertices (left right : Vertices n) : Bool :=
  left.all right.contains && right.all left.contains

theorem ancestors_eq_current_of_no_decrease (graph : MixedGraph n) (current target : Vertices n)
    (noDecrease : ¬ (ancestors graph current target).length < current.length) :
    ancestors graph current target = current := by
  have subset : (ancestors graph current target).Sublist current := List.filter_sublist
  exact subset.eq_of_length (Nat.le_antisymm subset.length_le (Nat.le_of_not_gt noDecrease))

theorem recursive_set_smaller (graph : MixedGraph n) (current target : Vertices n) (root : Fin n)
    (smaller : (ancestors graph current target).length < current.length) :
    (district graph (ancestors graph current target) root).length < current.length :=
  Nat.lt_of_le_of_lt (List.length_filter_le _ _) smaller

inductive Instruction (n : Nat)
  | marginalize (source retained : Vertices n)
  | extractFactor (source retained : Vertices n)
  | ancestorFixedPoint (current : Vertices n)
  deriving DecidableEq

/-- Plan the operations on the supplied kernel. The given root is in the
target c-component. The original failure branch yields no expression. -/
def identifyPlan (graph : MixedGraph n) (target : Vertices n) (root : Fin n)
    (current : Vertices n) : List (Instruction n) :=
  let ancestorSet := ancestors graph current target
  if sameVertices ancestorSet target then
    [.marginalize current ancestorSet]
  else if _smaller : ancestorSet.length < current.length then
    let component := district graph ancestorSet root
    .marginalize current ancestorSet :: .extractFactor ancestorSet component ::
      identifyPlan graph target root component
  else [.ancestorFixedPoint current]
termination_by current.length
decreasing_by exact recursive_set_smaller graph current target root _smaller

end

end OpenCausalScience.Papers.TianPearl2003.IdentifyRecurrence
