module
public import OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence
public import OpenCausalScience.Graph.DSeparation

/-! # Verma and Pearl (1990), Figure 2

[The proceedings copy](https://arxiv.org/pdf/1304.1108#page=3), p. 222,
shows a diamond with a fifth vertex below it. Name its top, left, right,
middle and bottom vertices `T, L, R, M, B`. Panels (a)–(c) share the
arrows `L → M ← R` and `M → B`. The panels vary the two edges at `T`.
Reversing both arrows of panel (a) introduces `L → T ← R`.
-/

namespace OpenCausalScience.Papers.VermaPearl1990.Figure2

open OpenCausalScience
open DAGEquivalence

@[expose] public section

def top : Fin 5 := 0
def left : Fin 5 := 1
def right : Fin 5 := 2
def middle : Fin 5 := 3
def bottom : Fin 5 := 4

def figureEdge (toLeft toRight : Bool) (u v : Fin 5) : Bool :=
  (u == top && v == left && toLeft) ||
  (u == left && v == top && !toLeft) ||
  (u == top && v == right && toRight) ||
  (u == right && v == top && !toRight) ||
  (u == left && v == middle) ||
  (u == right && v == middle) ||
  (u == middle && v == bottom)

def figureRank (toLeft toRight : Bool) (v : Fin 5) : Nat :=
  if v == top then 1
  else if v == left then (if toLeft then 2 else 0)
  else if v == right then (if toRight then 2 else 0)
  else if v == middle then 3
  else 4

def figure (toLeft toRight : Bool) : DAG 5 where
  edge := figureEdge toLeft toRight
  rank := figureRank toLeft toRight
  edge_increases := by cases toLeft <;> cases toRight <;> decide

def panelA : DAG 5 := figure true true
def panelB : DAG 5 := figure false true
def panelC : DAG 5 := figure true false
def bothAtTop : DAG 5 := figure false false

theorem signatures_of_top_orientations (toLeft toRight : Bool) :
    signaturesMatch panelA (figure toLeft toRight) = (toLeft || toRight) := by
  cases toLeft <;> cases toRight <;> decide

def matchesOnEveryQuery (G H : DAG 5) : Bool :=
  let vertices := List.finRange 5
  vertices.all fun x => vertices.all fun y => (List.finRange 32).all fun mask =>
    let conditioned := vertices.filter (fun v => mask.val.testBit v.val)
    G.dSeparated x y conditioned == H.dSeparated x y conditioned

/-- Each comparison covers all 160 ordered singleton queries with valid
conditioning and also compares the invalid argument cases. -/
theorem panels_a_b_c_same_executable_queries :
    matchesOnEveryQuery panelA panelB = true ∧ matchesOnEveryQuery panelA panelC = true := by
  decide

/-- Conditioning on `T` opens the extra top collider, rather than blocking
the fork through `T` as in panel (a). -/
theorem both_at_top_distinguished_given_top :
    panelA.dSeparated left right [top] = some true ∧
      bothAtTop.dSeparated left right [top] = some false := by
  decide

end

end OpenCausalScience.Papers.VermaPearl1990.Figure2
