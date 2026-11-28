module
public import OpenCausalScience.Papers.AndrewsEtAl2023.CoveredScore
public import OpenCausalScience.Papers.AndrewsEtAl2023.PenalizedLikelihood
public import OpenCausalScience.Papers.AndrewsEtAl2023.WithBackwardSearch
public import OpenCausalScience.Papers.LamEtAl2022.ScoredSearch

/-! # Recovery under local likelihood bounds

The fixed-comparison bounds supply the score signs for the scored GRaSP
tiers and for BOSS followed by backward equivalence search. The finite
sample law and score equivalence are separate assumptions.
-/

namespace OpenCausalScience.Papers.AndrewsEtAl2023.PenalizedLikelihood

open Discovery Discovery.FiniteCIQueries Probability Probability.CI
open GrowShrinkTree DeletionScore SampleScoreSigns
open LamEtAl2022 RaskuttiUhler2018 VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n : Nat} {Ω : Nat → Type}

/-- Log likelihood and dimension increments of joint-set potentials
give an exactly score-equivalent penalized local score in each sample. -/
theorem penalized_score_equivalent_of_potentials (dimension : Mask n → Rat) (penalty : Nat → Rat)
    (logLikelihood : ∀ m, Ω m → Mask n → Rat) (m : Nat) (a : Ω m) :
    ScoreEquivalent (penalizedScore (potentialScore dimension) penalty
      (fun s data => potentialScore (logLikelihood s data)) m a) := by
  have same : penalizedScore (potentialScore dimension) penalty
      (fun s data => potentialScore (logLikelihood s data)) m a =
      potentialScore (fun S => logLikelihood m a S - penalty m * dimension S) := by
    funext child parents
    simp only [penalizedScore, potentialScore, Rat.sub_eq_add_neg, Rat.mul_add]
    grind
  rw [same]
  exact potential_score_equivalent _

/-- Sufficient likelihood and dimension conditions for all parent-addition comparisons. -/
structure LocalLikelihoodBounds (J : Relation n) (law : ∀ m, FiniteLaw (Ω m))
    (dimension : Fin n → LocalScore n) (penalty : Nat → Rat)
    (logLikelihood : ∀ m, Ω m → Fin n → LocalScore n) : Prop where
  dimensionSets : SetScores dimension
  likelihoodSets : ∀ m a, SetScores (logLikelihood m a)
  growth : PenaltyGrowth penalty
  increase : ∀ q, ValidComparison q → 0 < dimensionGain dimension q
  null : ∀ q, ValidComparison q → IndependentComparison J q →
    LikelihoodTightAbove law (likelihoodGain logLikelihood q)
  alternative : ∀ q, ValidComparison q → ¬ IndependentComparison J q →
    LikelihoodLinearGap law (likelihoodGain logLikelihood q)

variable {J : Relation n} {law : ∀ m, FiniteLaw (Ω m)} {dimension : Fin n → LocalScore n}
  {penalty : Nat → Rat} {logLikelihood : ∀ m, Ω m → Fin n → LocalScore n} {truth : DAG n}

theorem LocalLikelihoodBounds.set_scores
    (bounds : LocalLikelihoodBounds J law dimension penalty logLikelihood) (m : Nat) (a : Ω m) :
    SetScores (penalizedScore dimension penalty logLikelihood m a) := by
  intro child P Q same
  unfold penalizedScore
  rw [bounds.likelihoodSets m a child P Q same, bounds.dimensionSets child P Q same]

theorem boss_bes_sample_failure_vanishes_of_likelihood_bounds
    (sg : Semigraphoid J) (faithful : DAGFaithful truth J)
    (bounds : LocalLikelihoodBounds J law dimension penalty logLikelihood)
    (equivalent : ∀ m a, ScoreEquivalent (penalizedScore dimension penalty logLikelihood m a))
    (initial : ∀ m, Ω m → List (Fin n)) (complete : ∀ m a v, v ∈ initial m a) :
    ∀ ε : Rat, 0 < ε → ∃ N, ∀ m, N ≤ m → (law m).mass
      (fun a => @decide (¬ SameDConnections
        (withBackwardSearch (penalizedScore dimension penalty logLikelihood m a) (initial m a)) truth)
        (Classical.propDecidable _)) < ε :=
  boss_bes_sample_failure_vanishes sg faithful law _ bounds.set_scores equivalent initial complete
    (fun q _ => comparison_error_vanishes_of_likelihood_tails law dimension penalty logLikelihood
      bounds.growth q (bounds.increase q) (bounds.null q) (bounds.alternative q))

theorem scored_grasp_sample_failure_vanishes_of_likelihood_bounds
    (sg : Semigraphoid J) (faithful : DAGFaithful truth J)
    (bounds : LocalLikelihoodBounds J law dimension penalty logLikelihood)
    (equivalent : ∀ m a, ScoreEquivalent (penalizedScore dimension penalty logLikelihood m a))
    (initial : ∀ m, Ω m → List (Fin n)) (valid : ∀ m a, VertexOrder (initial m a))
    (tier : Tier) {depth : Nat} (deep : (allOrders n).length ≤ depth) :
    ∀ ε : Rat, 0 < ε → ∃ N, ∀ m, N ≤ m → (law m).mass
      (fun a => @decide (¬ SameDConnections
        (scoredDAG (penalizedScore dimension penalty logLikelihood m a) depth tier (initial m a)) truth)
        (Classical.propDecidable _)) < ε :=
  scored_grasp_sample_failure_vanishes sg faithful law _ bounds.set_scores equivalent initial valid tier deep
    (fun q _ => comparison_error_vanishes_of_likelihood_tails law dimension penalty logLikelihood
      bounds.growth q (bounds.increase q) (bounds.null q) (bounds.alternative q))

end

end OpenCausalScience.Papers.AndrewsEtAl2023.PenalizedLikelihood
