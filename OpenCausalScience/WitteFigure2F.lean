module
public import Std

/-! # Witte et al. (2020), Figure 2F

The causal nodes for `{X₁, X₂}` and `{Y}` are `V₂` and `Y`.
Only `V₂` is omitted from the forbidden projection.
The two projected arrows drawn from `V₁` to `X₂` and `Y` would require
contracting a path through the retained treatment `X₁`.
-/

namespace OpenCausalScience.WitteFigure2F

@[expose] public section

def v1 : Fin 4 := 0
def x1 : Fin 4 := 1
def x2 : Fin 4 := 2
def y : Fin 4 := 3
def v2 : Fin 5 := 4

def originalArrow (source target : Fin 5) : Bool :=
  (source == v1.castSucc && target == x1.castSucc) ||
  (source == x1.castSucc && (target == v2 || target == x2.castSucc)) ||
  (source == v2 && (target == x2.castSucc || target == y.castSucc)) ||
  (source == x2.castSucc && target == y.castSucc)

/-- With one omitted vertex, a projected arrow is direct or has one
internal vertex, `V₂`. -/
def projectedArrow (source target : Fin 4) : Bool :=
  source != target &&
  (originalArrow source.castSucc target.castSucc ||
    (originalArrow source.castSucc v2 && originalArrow v2 target.castSucc))

/-- A bidirected edge requires a noncollider interior. With one omitted
vertex this can only be `source ← V₂ → target`. -/
def projectedBidirected (source target : Fin 4) : Bool :=
  source != target &&
    originalArrow v2 source.castSucc && originalArrow v2 target.castSucc

theorem directedEdges : ∀ source target : Fin 4,
    projectedArrow source target =
      ((source == v1 && target == x1) ||
       (source == x1 && (target == x2 || target == y)) ||
       (source == x2 && target == y)) := by decide

theorem bidirectedEdges : ∀ source target : Fin 4,
    projectedBidirected source target =
      ((source == x2 && target == y) || (source == y && target == x2)) := by decide

theorem printedExtraArrowsAbsent :
    projectedArrow v1 x2 = false ∧ projectedArrow v1 y = false := by decide

/-- `Y` is a descendant of a treatment in the original DAG, and the
corrected projection still has a treatment–outcome bidirected edge. -/
theorem adjustmentObstructionRemains :
    originalArrow x2.castSucc y.castSucc = true ∧ projectedBidirected x2 y = true := by decide

end

end OpenCausalScience.WitteFigure2F
