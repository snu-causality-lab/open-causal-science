module
public import Std

/-! # Kivva et al. (2022), Example 2

[Revisiting the General Identifiability Problem](https://proceedings.mlr.press/v180/kivva22a/kivva22a.pdf),
Example 2, PDF pp. 4–5. Both observational treatments copy the same
independent fair bit (U_1). The two outcomes are conditionally
independent given the fair bit (U_2) and their own treatments, with the
binary kernels displayed in the example. The new treatment values under
intervention are (X_1=0) and (X_2=1).

The intervention averages over (U_2), giving (2/9) and (5/18).
The observational laws agree and give zero weight to off-diagonal
treatment assignments. This is the example about omitting positivity in
Section 3.1. The algorithm for positive input laws is outside its scope.
-/

namespace OpenCausalScience.Papers.KivvaEtAl2022.Example2

@[expose] public section

def averageBits (f : Bool → Rat) : Rat :=
  (f false + f true) / 2

def firstOutcome (secondModel u x y : Bool) : Rat :=
  if secondModel then
    if y == Bool.xor u x then 2 / 3 else 1 / 3
  else
    if y == u then 1 / 3 else 2 / 3

def secondOutcome (secondModel u x y : Bool) : Rat :=
  if secondModel then
    if y == u then 2 / 3 else 1 / 3
  else
    if y == Bool.xor u x then 1 / 3 else 2 / 3

/-- The two intervention-replaced treatments do not read the shared bit U₁. -/
def interventional (secondModel x₁ x₂ y₁ y₂ : Bool) : Rat :=
  averageBits fun u => firstOutcome secondModel u x₁ y₁ * secondOutcome secondModel u x₂ y₂

def observational (secondModel x₁ x₂ y₁ y₂ : Bool) : Rat :=
  averageBits fun u =>
    if (x₁ == u) && (x₂ == u) then interventional secondModel x₁ x₂ y₁ y₂ else 0

theorem outcome_kernels_normalized (secondModel u x : Bool) :
    firstOutcome secondModel u x false + firstOutcome secondModel u x true = 1 ∧
      secondOutcome secondModel u x false + secondOutcome secondModel u x true = 1 := by
  cases secondModel <;> cases u <;> cases x <;> decide +kernel

theorem observational_agreement (x₁ x₂ y₁ y₂ : Bool) :
    observational false x₁ x₂ y₁ y₂ = observational true x₁ x₂ y₁ y₂ := by
  cases x₁ <;> cases x₂ <;> cases y₁ <;> cases y₂ <;> decide +kernel

theorem observational_off_diagonal_zero (secondModel x y₁ y₂ : Bool) :
    observational secondModel x (!x) y₁ y₂ = 0 := by
  cases x <;> simp [observational, averageBits] <;> decide +kernel

theorem target_values :
    interventional false false true false false = 2 / 9 ∧
      interventional true false true false false = 5 / 18 := by decide +kernel

theorem printed_values_are_twice_the_targets :
    2 * interventional false false true false false = 4 / 9 ∧
      2 * interventional true false true false false = 5 / 9 := by decide +kernel

theorem target_disagrees :
    interventional false false true false false ≠ interventional true false true false false := by
  decide +kernel

end

end OpenCausalScience.Papers.KivvaEtAl2022.Example2
