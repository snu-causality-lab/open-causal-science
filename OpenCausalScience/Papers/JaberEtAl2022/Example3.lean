module
public import Std

/-! # The two marginal identification steps of Example 3

Jaber, Ribeiro, Zhang and Bareinboim, R-86 (May 2022), Figure 3(a),
Proposition 2 and Algorithm 1. Starting with the full graph, the example
removes the bucket {X₁, W}, then the singleton {X₂}. Compute possible
descendants and pc-component membership from the endpoint marks and the
visible edges indicated in the figure.
Source: https://causalai.net/r86.pdf#page=6
-/

namespace OpenCausalScience.Papers.JaberEtAl2022.Example3

@[expose] public section

inductive Vertex
  | a | x₁ | x₂ | w | z | y
  deriving DecidableEq, BEq

inductive Mark
  | tail | arrow | circle
  deriving DecidableEq, BEq

def vertices : List Vertex := [.a, .x₁, .x₂, .w, .z, .y]

def edge : Vertex → Vertex → Option (Mark × Mark)
  | .a, .x₁ | .a, .w | .x₂, .w => some (.circle, .arrow)
  | .a, .y | .w, .z | .z, .y => some (.tail, .arrow)
  | .x₁, .x₂ => some (.arrow, .circle)
  | .x₁, .w => some (.circle, .circle)
  | _, _ => none

def markAt (u v : Vertex) : Option Mark :=
  (edge u v).map Prod.fst <|> (edge v u).map Prod.snd

/-- These are the two edges marked visible in the source drawing. -/
def visible (u v : Vertex) : Bool :=
  ((u == .w && v == .z) || (u == .z && v == .w)) ||
    ((u == .z && v == .y) || (u == .y && v == .z))

def invisibleEdge (u v : Vertex) : Bool :=
  (markAt u v).isSome && !visible u v

def couldPointFrom (u v : Vertex) : Bool :=
  markAt u v == some .tail || markAt u v == some .circle

/-- A monotone reachability computation. A path in a finite state graph can
be shortened to a simple one, so there are enough rounds for this example. -/
def closure {α : Type} [BEq α] (all : List α) (move : α → α → Bool)
    (seeds : α → Bool) : Nat → List α
  | 0 => all.filter seeds
  | n + 1 =>
    let known := closure all move seeds n
    all.filter fun u => known.contains u || (known.any fun v => move v u)

def possibleDescendants (current seeds : List Vertex) : List Vertex :=
  closure current couldPointFrom seeds.contains current.length

abbrev Arrival := Vertex × Bool

def advance (source target : Arrival) : Bool :=
  source.2 && invisibleEdge source.1 target.1 && (markAt source.1 target.1 == some .arrow) &&
    (target.2 == (markAt target.1 source.1 == some .arrow))

/-- For a pc-component, intermediate vertices must have two arrowheads on
the path. Arrival states remember the mark at the current endpoint. -/
def pcComponent (current seeds : List Vertex) : List Vertex :=
  let states : List Arrival := current.flatMap fun v => [(v, false), (v, true)]
  let initial (state : Arrival) := seeds.any fun u =>
    invisibleEdge u state.1 && (state.2 == (markAt state.1 u == some .arrow))
  let reached := closure states advance initial states.length
  current.filter fun v => seeds.contains v || reached.any (fun state => state.1 == v)

def firstBucket : List Vertex := [.x₁, .w]
def afterFirst : List Vertex := vertices.filter fun v => !firstBucket.contains v
def secondBucket : List Vertex := [.x₂]
def target : List Vertex := afterFirst.filter fun v => !secondBucket.contains v

def admissible (current bucket : List Vertex) : Bool :=
  let descendants := possibleDescendants current bucket
  (pcComponent current bucket).all fun v => !descendants.contains v || bucket.contains v

theorem first_bucket_graphical_step :
    pcComponent vertices firstBucket = [.a, .x₁, .x₂, .w] ∧
      possibleDescendants vertices firstBucket = [.x₁, .w, .z, .y] ∧
      admissible vertices firstBucket = true := by decide +kernel

theorem second_bucket_graphical_step :
    pcComponent afterFirst secondBucket = [.x₂] ∧
      possibleDescendants afterFirst secondBucket = [.x₂] ∧
      admissible afterFirst secondBucket = true ∧ target = [.a, .z, .y] := by decide +kernel

/-- The variables in the denominator conditioning sets of Equation (1). -/
theorem denominator_conditioning_sets :
    vertices.filter (fun v => !(possibleDescendants vertices firstBucket).contains v) =
      [.a, .x₂] ∧
    afterFirst.filter (fun v => !(possibleDescendants afterFirst secondBucket).contains v) =
      [.a, .z, .y] := by decide +kernel

end

end OpenCausalScience.Papers.JaberEtAl2022.Example3
