module
public import Std

/-!
# Kwon et al. (2025), the two-slice fixed-plan example

The corrected version (2026-10-25, Section 7, p. 10) gives two independent
fair bits and compares forcing the first action with leaving it free. Here
the rewards are in quarter units, so summing over four equally likely noise
assignments gives the numerator of the expected reward with denominator 16.

Sources:
* https://openreview.net/forum?id=F4LhOqhxkk
* https://www.sanghacklee.me/ai-corrected/NS_SCB_AI_corrected_2026-10-25.pdf
-/

namespace OpenCausalScience.Papers.KwonEtAl2025.FixedPlanCounterexample

@[expose] public section

/-- The three ways to treat a binary action: natural, forced false, forced true. -/
def value (setting : Fin 3) (noise : Bool) : Bool :=
  if setting = 0 then noise else setting = 2

def firstReward (action noise : Bool) : Nat := if action = noise then 3 else 0

def secondReward (firstAction secondAction noise : Bool) : Nat :=
  (if secondAction = noise then 3 else 0) + firstAction.toNat

def noiseAssignments : List (Bool × Bool) :=
  [(false, false), (false, true), (true, false), (true, true)]

/-- The exact mean rewards of the two slices have these numerators over 16. -/
def firstNumerator (x₁ : Fin 3) : Nat :=
  (noiseAssignments.map fun (u₁, _) => firstReward (value x₁ u₁) u₁).sum

def secondNumerator (x₁ x₂ : Fin 3) : Nat :=
  (noiseAssignments.map fun (u₁, u₂) => secondReward (value x₁ u₁) (value x₂ u₂) u₂).sum

def totalNumerator (x₁ x₂ : Fin 3) : Nat :=
  firstNumerator x₁ + secondNumerator x₁ x₂

theorem no_intervention_rewards :
    firstNumerator 0 = 12 ∧ secondNumerator 0 0 = 14 := by decide

theorem force_first_true_rewards :
    firstNumerator 2 = 6 ∧ secondNumerator 2 0 = 16 := by decide

/-- All interventions on the first action have value at most 11/8. -/
theorem forced_first_maximum :
    (∀ x₁ x₂ : Fin 3, x₁ ≠ 0 → totalNumerator x₁ x₂ ≤ 22) ∧
      totalNumerator 2 0 = 22 := by decide

/-- The empty intervention attains the unrestricted fixed-plan maximum of 13/8. -/
theorem unrestricted_maximum :
    (∀ x₁ x₂ : Fin 3, totalNumerator x₁ x₂ ≤ 26) ∧ totalNumerator 0 0 = 26 := by decide

/-- Every plan obeying the first-action restriction has strictly smaller value. -/
theorem forcing_first_loses_value (x₁ x₂ : Fin 3) (forced : x₁ ≠ 0) :
    totalNumerator x₁ x₂ < totalNumerator 0 0 := by
  exact Nat.lt_of_le_of_lt (forced_first_maximum.1 x₁ x₂ forced) (by decide)

end
end OpenCausalScience.Papers.KwonEtAl2025.FixedPlanCounterexample
