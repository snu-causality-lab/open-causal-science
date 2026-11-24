module
public import Std

/-! # Bayes-ball downward arrivals

[Kim et al., corrected version](https://www.sanghacklee.me/ai-corrected/CRL_internal_auxiliaries_AI_corrected_2026-10-15.pdf),
Appendix C, Algorithm 2, lines 19–30. We model the two branches in the
[proceedings](https://proceedings.mlr.press/v337/kim26e.html) and corrected
versions as directed-state transitions with a supplied descendant test. The
chain shows how the original exclusive branch suppresses a d-connected
unconditioned node. This module does not prove Bayes-ball completeness.
-/

namespace OpenCausalScience.Papers.KimEtAl2026.BayesBall

@[expose] public section

inductive Direction where
  | up
  | down
  deriving DecidableEq

abbrev State (α : Type) := α × Direction

structure Neighborhood (α : Type) where
  parents : α → List α
  children : α → List α
  conditioned : α → Bool
  hasConditionedDescendant : α → Bool

def parentStates {α : Type} (graph : Neighborhood α) (node : α) : List (State α) :=
  (graph.parents node).map (·, .up)

def childStates {α : Type} (graph : Neighborhood α) (node : α) : List (State α) :=
  (graph.children node).map (·, .down)

def nextStates {α : Type} (graph : Neighborhood α) (corrected : Bool) : State α → List (State α)
  | (node, .up) =>
    if graph.conditioned node then [] else parentStates graph node ++ childStates graph node
  | (node, .down) =>
    let ascend := graph.conditioned node || graph.hasConditionedDescendant node
    let descend := if corrected then !graph.conditioned node else !ascend
    (if ascend then parentStates graph node else []) ++
      (if descend then childStates graph node else [])

/-- Both successor lists are generated when an unconditioned node has a
conditioned descendant, while the proceedings branch generates parents only. -/
theorem both_downward_moves {α : Type} (graph : Neighborhood α) (node : α)
    (unconditioned : graph.conditioned node = false)
    (descendant : graph.hasConditionedDescendant node = true) :
    nextStates graph true (node, .down) = parentStates graph node ++ childStates graph node ∧
    nextStates graph false (node, .down) = parentStates graph node := by
  simp [nextStates, unconditioned, descendant]

inductive Reachable {α : Type} (next : State α → List (State α)) (start : State α) :
    State α → Prop where
  | start : Reachable next start start
  | step {before after : State α} :
    Reachable next start before → after ∈ next before → Reachable next start after

/-- The graph is the chain `0 → 1 → 2 → 3`, conditioned on `3`. -/
def conditionedChain : Neighborhood Nat where
  parents := fun node => if 0 < node ∧ node ≤ 3 then [node - 1] else []
  children := fun node => if node < 3 then [node + 1] else []
  conditioned := (· == 3)
  hasConditionedDescendant := (· < 3)

private theorem original_chain_visited {state : State Nat}
    (reachable : Reachable (nextStates conditionedChain false) (0, .up) state) :
    state = (0, .up) ∨ state = (1, .down) := by
  induction reachable with
  | start => exact Or.inl rfl
  | @step before after _ move ih =>
    rcases ih with rfl | rfl
    · have next : nextStates conditionedChain false (0, .up) = [(1, .down)] := by decide
      exact Or.inr (by simpa only [next, List.mem_singleton] using move)
    · have next : nextStates conditionedChain false (1, .down) = [(0, .up)] := by decide
      exact Or.inl (by simpa only [next, List.mem_singleton] using move)

/-- The internal vertex `1` is outside the conditioning set, so the path
`0 → 1 → 2` is active given `3`. The original procedure misses `2` and the
corrected procedure reaches it. -/
theorem corrected_chain_reaches_unconditioned_node :
    conditionedChain.conditioned 1 = false ∧ conditionedChain.conditioned 2 = false ∧
    Reachable (nextStates conditionedChain true) (0, .up) (2, .down) ∧
    (∀ arrival, ¬ Reachable (nextStates conditionedChain false) (0, .up) (2, arrival)) := by
  refine ⟨rfl, rfl, .step (before := (1, .down)) (.step .start (by decide)) (by decide), ?_⟩
  intro arrival reachable
  rcases original_chain_visited reachable with h | h
  · exact (by decide : (2 : Nat) ≠ 0) (congrArg Prod.fst h)
  · exact (by decide : (2 : Nat) ≠ 1) (congrArg Prod.fst h)

end

end OpenCausalScience.Papers.KimEtAl2026.BayesBall
