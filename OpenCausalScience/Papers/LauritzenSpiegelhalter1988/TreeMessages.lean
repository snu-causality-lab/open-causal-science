module
public import OpenCausalScience.Probability.FiniteSummation

/-! # Exact finite messages on a clique tree

Each node lists configurations of its bag, a local potential and the
compatibility test on its separator with its parent. The upward
sum-product message contracts the same sum as exhaustive compatible
configurations. This is the division-free upward calculation.
Source: https://doi.org/10.1111/j.2517-6161.1988.tb01721.x
-/

namespace OpenCausalScience.Papers.LauritzenSpiegelhalter1988.TreeMessages

open Probability.FiniteSummation

@[expose] public section

mutual
  inductive CliqueTree (State : Type)
    | node (states : List State) (potential : State → Rat)
        (compatible : State → State → Bool) (branches : CliqueForest State)

  inductive CliqueForest (State : Type)
    | nil
    | cons (tree : CliqueTree State) (rest : CliqueForest State)
end

variable {State : Type}

mutual
  def upwardMessage (parent : State) (tree : CliqueTree State) : Rat :=
    match tree with
    | .node states potential compatible branches =>
      sumOver (states.filter (compatible parent)) fun state =>
        potential state * branchMessages state branches
  termination_by structural tree

  def branchMessages (parent : State) (branches : CliqueForest State) : Rat :=
    match branches with
    | .nil => 1
    | .cons first rest => upwardMessage parent first * branchMessages parent rest
  termination_by structural branches
end

private theorem sum_id (weights : List Rat) : sumOver weights (fun x => x) = weights.sum := by
  simp [sumOver]

mutual
  def configurationWeights (parent : State) (tree : CliqueTree State) : List Rat :=
    match tree with
    | .node states potential compatible branches =>
      (states.filter (compatible parent)).flatMap fun state =>
        (branchWeights state branches).map (potential state * ·)
  termination_by structural tree

  def branchWeights (parent : State) (branches : CliqueForest State) : List Rat :=
    match branches with
    | .nil => [1]
    | .cons first rest =>
      (configurationWeights parent first).flatMap fun weight =>
        (branchWeights parent rest).map (weight * ·)
  termination_by structural branches
end

mutual
  theorem upward_message_exact (parent : State) (tree : CliqueTree State) :
      (configurationWeights parent tree).sum = upwardMessage parent tree := by
    cases tree with
    | node states potential compatible branches =>
      rw [← sum_id, configurationWeights, upwardMessage, sum_flatMap]
      apply sum_congr
      intro state _
      rw [sum_id]
      change sumOver (branchWeights state branches) (potential state * ·) = _
      rw [sum_mul_left]
      rw [sum_id, branch_messages_exact state branches]
  termination_by structural tree

  theorem branch_messages_exact (parent : State) (branches : CliqueForest State) :
      (branchWeights parent branches).sum = branchMessages parent branches := by
    cases branches with
    | nil => exact Rat.add_zero 1
    | cons first rest =>
      rw [← sum_id, branchWeights, branchMessages, sum_flatMap]
      have factor :
          sumOver (configurationWeights parent first) (fun weight =>
            sumOver ((branchWeights parent rest).map (weight * ·)) (fun x => x)) =
          sumOver (configurationWeights parent first) (fun weight =>
            weight * (branchWeights parent rest).sum) := by
        apply sum_congr
        intro weight _
        rw [sum_id]
        have scaled := sum_mul_left (branchWeights parent rest) (fun x => x) weight
        rw [sum_id] at scaled
        exact scaled
      rw [factor, sum_mul_right]
      rw [sum_id, upward_message_exact parent first, branch_messages_exact parent rest]
  termination_by structural branches
end

/-- Exact joint evidence on the chain A — B — C, with B the separator
and each transition copying its parent with probability 3/4. -/
def chainTree : CliqueTree (Bool × Bool) :=
  let cells := [(false, false), (false, true), (true, false), (true, true)]
  let right : CliqueTree (Bool × Bool) := CliqueTree.node cells
    (fun (b, c) => if c then (if b then 3 / 4 else 1 / 4) else 0)
    (fun parent cell => parent.2 == cell.1) .nil
  .node cells (fun (a, b) => if a then (if b then 3 / 8 else 1 / 8) else 0)
    (fun _ _ => true) (.cons right .nil)

theorem chain_evidence :
    upwardMessage (false, false) chainTree = 5 / 16 ∧
      (configurationWeights (false, false) chainTree).sum = 5 / 16 := by
  have message : upwardMessage (false, false) chainTree = 5 / 16 := by decide +kernel
  exact ⟨message, (upward_message_exact _ _).trans message⟩

end
end OpenCausalScience.Papers.LauritzenSpiegelhalter1988.TreeMessages
