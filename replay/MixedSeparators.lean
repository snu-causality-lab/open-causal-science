import Lean
import OpenCausalScience.Examples.MixedReplayGraphs
import OpenCausalScience.Graph.LatentExpansionSeparation

open OpenCausalScience OpenCausalScience.MixedReplayGraphs

private def queryLabel {n : Nat} (code : Nat) (v : Fin n) : Nat :=
  code / 5 ^ v.val % 5

private def vertices {n : Nat} (selected : Fin n → Bool) : List Nat :=
  ((List.finRange n).filter selected).map Fin.val

private def verdicts {n : Nat} (search : (Fin n → Bool) → (Fin n → Bool) →
    (Fin n → Bool) → (Fin n → Bool) → Option (Fin n → Bool)) : List Lean.Json :=
  (List.range (5 ^ n)).filterMap fun code =>
    let left := fun v => queryLabel code v == 1
    let right := fun v => queryLabel code v == 2
    let required := fun v => queryLabel code v == 3
    let allowed := fun v => decide (3 ≤ queryLabel code v)
    if (List.finRange n).any left && (List.finRange n).any right then
      let result := search left right required allowed
      some <| Lean.Json.mkObj [
        ("left", Lean.toJson (vertices left)),
        ("right", Lean.toJson (vertices right)),
        ("required", Lean.toJson (vertices required)),
        ("allowed", Lean.toJson (vertices allowed)),
        ("result", Lean.toJson (result.map vertices))
      ]
    else none

private def indexedVerdicts {n : Nat} (count : Nat) (graph : Nat → Option (MixedGraph n))
    (latent : Bool) : List (Nat × List Lean.Json) :=
  (List.range count).filterMap fun i => (graph i).map fun g =>
    (i, verdicts (if latent then g.findMinimalADMGSeparator else g.findMinimalMSeparator))

private def replay : Lean.Json :=
  Lean.Json.mkObj [
    ("admg3", Lean.toJson (indexedVerdicts 64 admg3Graph true)),
    ("ancestral3", Lean.toJson (indexedVerdicts 125 ancestral3Graph false)),
    ("bow4", Lean.toJson (bow4Graph.map fun g => verdicts g.findMinimalADMGSeparator)),
    ("ancestral4", Lean.toJson (ancestral4Graph.map fun g => verdicts g.findMinimalMSeparator))
  ]

/- Each vertex is unused, a left endpoint, a right endpoint, required,
or optionally allowed. The two endpoint sets must be nonempty. -/
#eval IO.println replay.compress
