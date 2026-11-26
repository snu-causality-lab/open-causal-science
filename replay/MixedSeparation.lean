import Lean
import OpenCausalScience.Examples.MixedReplayGraphs
import OpenCausalScience.Graph.MixedSeparationExecutable

open OpenCausalScience OpenCausalScience.MixedReplayGraphs

private def queryLabel {n : Nat} (code : Nat) (v : Fin n) : Nat :=
  code / 4 ^ v.val % 4

private def verdicts {n : Nat} (g : MixedGraph n) : List (Nat × Bool) :=
  (List.range (4 ^ n)).filterMap fun code =>
    let left := fun v => queryLabel code v == 1
    let right := fun v => queryLabel code v == 2
    let conditioning := fun v => queryLabel code v == 3
    if (List.finRange n).any left && (List.finRange n).any right then
      some (code, g.mSeparated left right conditioning)
    else none

private def indexedVerdicts {n : Nat} (count : Nat)
    (graph : Nat → Option (MixedGraph n)) : List (Nat × List (Nat × Bool)) :=
  (List.range count).filterMap fun i => (graph i).map fun g => (i, verdicts g)

private def replay : Lean.Json :=
  Lean.Json.mkObj [
    ("admg3", Lean.toJson (indexedVerdicts 64 admg3Graph)),
    ("ancestral3", Lean.toJson (indexedVerdicts 125 ancestral3Graph)),
    ("bow4", Lean.toJson (bow4Graph.map verdicts)),
    ("ancestral4", Lean.toJson (ancestral4Graph.map verdicts))
  ]

/- Enumerate all legal ordered queries with nonempty endpoints on every
three-vertex ADMG in topological vertex order and every three-vertex ancestral
graph, followed by one four-vertex example in each domain. -/
#eval IO.println replay.compress
