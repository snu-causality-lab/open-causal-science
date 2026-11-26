module
public import Std

/-! # Pairwise adjustment information

Runge (2021), arXiv:2102.10324v4, Lemma 1 and Appendix B.4, equations (S3)–(S5).
The conditional mutual information (CMI) chain rule is a premise. We prove
the score-difference identity, the implication of the two pairwise inequalities,
and a sufficient comparison using a separating subset of the outcome-side
adjustment variables. These deductions apply to finite-valued CMI; they do
not establish the converse's distribution modification or the graphical
implications in Theorem 3. Source: https://arxiv.org/html/2102.10324v4#App.B.SS4.
-/

namespace OpenCausalScience.Papers.Runge2021.AdjustmentInformation

open Lean.Grind

@[expose] public section

variable {n : Nat} {F : Type} [CommRing F]

/-- The vertex subsets used as arguments of conditional mutual information. -/
abbrev VertexSet (n : Nat) := Fin n → Bool

def union (a b : VertexSet n) : VertexSet n := fun v => a v || b v

def difference (a b : VertexSet n) : VertexSet n := fun v => a v && !b v

abbrev CMI (n : Nat) (F : Type) := VertexSet n → VertexSet n → VertexSet n → F

/-- The CMI chain rule in the first and second arguments. Repeated vertices
in a union identify the same variable. -/
structure HasChainRule (info : CMI n F) : Prop where
  first : ∀ a b c s, info (union a b) c s = info a c s + info b c (union s a)
  second : ∀ a b c s, info a (union b c) s = info a b s + info a c (union s b)

def adjustmentInformation (info : CMI n F) (x y fixed z : VertexSet n) : F :=
  info z y (union x fixed) - info x z fixed

/-- Equation (S5) for two arbitrary adjustment sets and a fixed conditioning
set. This isolates the outcome and treatment comparisons in the proof. -/
theorem adjustment_information_difference (info : CMI n F) (chain : HasChainRule info)
    (x y fixed z other : VertexSet n) :
    adjustmentInformation info x y fixed z - adjustmentInformation info x y fixed other =
      info (difference z other) y (union (union x fixed) other) +
      info x (difference other z) (union fixed z) -
      info (difference other z) y (union (union x fixed) z) -
      info x (difference z other) (union fixed other) := by
  have same : union z (difference other z) = union other (difference z other) := by
    funext v
    simp only [union, difference]
    cases z v <;> cases other v <;> rfl
  have outcomes := (chain.first z (difference other z) y (union x fixed)).symm.trans
    (congrArg (fun set => info set y (union x fixed)) same)
  have treatments := (chain.second x z (difference other z) fixed).symm.trans
    (congrArg (fun set => info x set fixed) same)
  rw [chain.first other (difference z other) y (union x fixed)] at outcomes
  rw [chain.second x other (difference z other) fixed] at treatments
  unfold adjustmentInformation
  grind

variable [LE F] [LT F] [Std.LawfulOrderLT F] [Std.IsLinearOrder F] [OrderedRing F]

/-- Sufficiency in Lemma 1 for a pair of sets at each model. -/
theorem comparison_of_two_inequalities (info : CMI n F) (chain : HasChainRule info)
    (x y fixed z other : VertexSet n)
    (outcomeComparison : info (difference other z) y (union (union x fixed) z) ≤
      info (difference z other) y (union (union x fixed) other))
    (treatmentComparison : info x (difference z other) (union fixed other) ≤
      info x (difference other z) (union fixed z)) :
    adjustmentInformation info x y fixed other ≤ adjustmentInformation info x y fixed z := by
  have difference_eq := adjustment_information_difference info chain x y fixed z other
  grind

/-- Adding a subset that separates the comparison variables from the outcome
can establish the outcome bracket without asserting that the unconditioned
CMI is zero. `outside` consists of the candidate variables beyond `subset`.
`separates` is the CMI-zero consequence under the Markov premise. -/
theorem outcome_comparison_of_separating_subset (info : CMI n F) (chain : HasChainRule info)
    (outcome given added subset outside : VertexSet n)
    (separates : info added outcome (union given subset) = 0)
    (nonnegGivenAdded : 0 ≤ info subset outcome (union given added))
    (nonnegOutside : 0 ≤ info outside outcome (union given subset)) :
    info added outcome given ≤ info (union subset outside) outcome given := by
  have same : union added subset = union subset added := by
    funext v
    exact Bool.or_comm (added v) (subset v)
  have exchange := (chain.first added subset outcome given).symm.trans
    (congrArg (fun set => info set outcome given) same)
  rw [chain.first subset added outcome given, separates] at exchange
  rw [chain.first subset outside outcome given]
  grind

end

end OpenCausalScience.Papers.Runge2021.AdjustmentInformation
