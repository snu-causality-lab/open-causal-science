module
public import OpenCausalScience.Separation

/-! # Witte et al. (2020), Figure 2B

The published panel has arrows `X₁ → V₁ ← V₂ → Y → X₂`, with
treatments `X₁` and `X₂` and outcome `Y`. There is no directed path from
either treatment to `Y`. The proper back-door graph therefore equals
the original graph. The proper noncausal path `X₂ ← Y` has no interior
vertex and remains open for all candidate conditioning sets.
-/

namespace OpenCausalScience.WitteFigure2B

@[expose] public section

def x1 : Fin 5 := 0
def x2 : Fin 5 := 1
def v1 : Fin 5 := 2
def v2 : Fin 5 := 3
def y : Fin 5 := 4

def figure2BEdge (source target : Fin 5) : Bool :=
  (source == x1 && target == v1) ||
  (source == v2 && (target == v1 || target == y)) ||
  (source == y && target == x2)

def figure2BRank (vertex : Fin 5) : Nat :=
  if vertex == v2 then 0 else if vertex == x1 || vertex == y then 1 else 2

def figure2B : DAG 5 where
  edge := figure2BEdge
  rank := figure2BRank
  edge_increases := by decide

/-- No edge is removed when forming the proper back-door graph for `{X₁,X₂}`
and `{Y}`, because no directed treatment-to-outcome path exists. -/
theorem noDirectedTreatmentToOutcome :
    ¬ figure2B.DirectedWalk x1 y ∧ ¬ figure2B.DirectedWalk x2 y := by
  constructor
  · intro walk
    exact (show ¬ figure2B.rank x1 < figure2B.rank y by decide)
      (figure2B.rank_lt_of_directedWalk walk)
  · intro walk
    exact (show ¬ figure2B.rank x2 < figure2B.rank y by decide)
      (figure2B.rank_lt_of_directedWalk walk)

/-- The one-edge path `X₂ ← Y` is traversable with no interior vertex tests. -/
theorem reverseEdgeGivesActivePath (conditioned activated : List (Fin 5)) :
    figure2B.searchActivePath y conditioned activated 2 none x2 [y] = true := rfl

/-- All conditioning subsets disjoint from the two treatments and outcome. -/
def candidateSets : List (List (Fin 5)) := [[], [v1], [v2], [v1, v2]]

/-- Each legal candidate fails to separate `X₂` and `Y` in the proper back-door DAG. -/
theorem candidateSetsFailToSeparate :
    candidateSets.map (figure2B.dSeparated x2 y) =
      [some false, some false, some false, some false] := by decide

end

end OpenCausalScience.WitteFigure2B
