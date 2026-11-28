module
public import OpenCausalScience.Papers.AndrewsEtAl2023.SampleScoreSigns

/-! # Local penalized-likelihood signs

The model comparison subtracts a diverging, sublinear penalty per extra
parameter, as in the Schwarz (1978) score and its use in Chickering (2002),
Lemma 7. We take the two likelihood-tail bounds as hypotheses. For regular
nested models, the null bound can be supplied by a likelihood ratio limit;
the alternative bound follows from a positive linear likelihood gap.

[Schwarz (1978)](https://doi.org/10.1214/aos/1176344136)
[Haughton (1988)](https://doi.org/10.1214/aos/1176350709)
[Wilks (1938)](https://doi.org/10.1214/aoms/1177732360)
-/

namespace OpenCausalScience.Papers.AndrewsEtAl2023.PenalizedLikelihood

open Probability Probability.CI Discovery.FiniteCIQueries
open GrowShrinkTree SampleScoreSigns

@[expose] public section

variable {n : Nat} {Ω : Nat → Type}

def penalizedScore (dimension : Fin n → LocalScore n) (penalty : Nat → Rat)
    (logLikelihood : ∀ m, Ω m → Fin n → LocalScore n) (m : Nat) (a : Ω m) : Fin n → LocalScore n :=
  fun child P => logLikelihood m a child P - penalty m * dimension child P

structure PenaltyGrowth (penalty : Nat → Rat) : Prop where
  diverges : ∀ B : Rat, ∃ N, ∀ m, N ≤ m → B < penalty m
  sublinear : ∀ k : Rat, 0 < k → ∃ N, ∀ m, N ≤ m → penalty m < k * (m : Rat)

def dimensionGain (dimension : Fin n → LocalScore n) (q : Comparison n) : Rat :=
  let (child, parent, P) := q
  let canonical := (List.finRange n).filter P
  dimension child (parent :: canonical) - dimension child canonical

def likelihoodGain (logLikelihood : ∀ m, Ω m → Fin n → LocalScore n)
    (q : Comparison n) (m : Nat) (a : Ω m) : Rat :=
  let (child, parent, P) := q
  let canonical := (List.finRange n).filter P
  logLikelihood m a child (parent :: canonical) - logLikelihood m a child canonical

def ValidComparison (q : Comparison n) : Prop :=
  let (child, parent, P) := q
  parent ≠ child ∧ P child = false ∧ P parent = false

def IndependentComparison (J : Relation n) (q : Comparison n) : Prop :=
  let (child, parent, P) := q
  J (single child) (single parent) P

/-- The null likelihood improvement has an eventually bounded upper tail. -/
def LikelihoodTightAbove (law : ∀ m, FiniteLaw (Ω m)) (gain : ∀ m, Ω m → Rat) : Prop :=
  ∀ ε : Rat, 0 < ε → ∃ B : Rat, ∃ N, ∀ m, N ≤ m →
    (law m).mass (fun a => decide (B < gain m a)) < ε

/-- Under the alternative, a fixed strictly positive slope is beaten with
probability tending to one. -/
def LikelihoodLinearGap (law : ∀ m, FiniteLaw (Ω m)) (gain : ∀ m, Ω m → Rat) : Prop :=
  ∃ κ : Rat, 0 < κ ∧ ∀ ε : Rat, 0 < ε → ∃ N, ∀ m, N ≤ m →
    (law m).mass (fun a => decide (gain m a < κ * (m : Rat))) < ε

private theorem penalty_scale (penalty : Nat → Rat) (growth : PenaltyGrowth penalty)
    {d : Rat} (positive : 0 < d) : PenaltyGrowth (fun m => penalty m * d) := by
  refine ⟨?_, ?_⟩
  · intro B
    obtain ⟨N, larger⟩ := growth.diverges (B / d)
    refine ⟨N, fun m hm => ?_⟩
    simpa only [Rat.div_mul_cancel (Rat.ne_of_gt positive)] using
      Rat.mul_lt_mul_of_pos_right (larger m hm) positive
  · intro k hk
    have zero : (0 : Rat) < k / d := (Rat.lt_div_iff positive).mpr (by simpa using hk)
    obtain ⟨N, smaller⟩ := growth.sublinear (k / d) zero
    refine ⟨N, fun m hm => ?_⟩
    have h := Rat.mul_lt_mul_of_pos_right (smaller m hm) positive
    rw [Rat.mul_assoc, Rat.mul_comm (m : Rat) d, ← Rat.mul_assoc,
      Rat.div_mul_cancel (Rat.ne_of_gt positive)] at h
    exact h

private theorem penalized_comparisons (small big p d₀ d₁ : Rat) :
    (big - p * d₁ < small - p * d₀ ↔ big - small < p * (d₁ - d₀)) ∧
      (small - p * d₀ < big - p * d₁ ↔ p * (d₁ - d₀) < big - small) := by
  have split : p * d₁ = p * d₀ + p * (d₁ - d₀) := by
    rw [Rat.add_comm, ← Rat.mul_add, Rat.sub_add_cancel]
  have left : (big - p * d₁) + p * d₁ = big := Rat.sub_add_cancel
  have right : (small - p * d₀) + p * d₁ = p * (d₁ - d₀) + small := by
    calc
      (small - p * d₀) + p * d₁ = (small - p * d₀) + (p * d₀ + p * (d₁ - d₀)) := congrArg _ split
      _ = small + p * (d₁ - d₀) := by rw [← Rat.add_assoc, Rat.sub_add_cancel]
      _ = p * (d₁ - d₀) + small := Rat.add_comm _ _
  have restore : (big - small) + small = big := Rat.sub_add_cancel
  constructor
  · calc
      _ ↔ (big - p * d₁) + p * d₁ < (small - p * d₀) + p * d₁ := Rat.add_lt_add_right.symm
      _ ↔ big < p * (d₁ - d₀) + small := by rw [left, right]
      _ ↔ _ := by
        simpa only [restore] using (Rat.add_lt_add_right (a := big - small)
          (b := p * (d₁ - d₀)) (c := small))
  · calc
      _ ↔ (small - p * d₀) + p * d₁ < (big - p * d₁) + p * d₁ := Rat.add_lt_add_right.symm
      _ ↔ p * (d₁ - d₀) + small < big := by rw [left, right]
      _ ↔ _ := by
        simpa only [restore] using (Rat.add_lt_add_right (a := p * (d₁ - d₀))
          (b := big - small) (c := small))

private theorem correct_sign_of_gain {J : Relation n} {dimension : Fin n → LocalScore n}
    {penalty : Nat → Rat} {logLikelihood : ∀ m, Ω m → Fin n → LocalScore n} {q : Comparison n}
    (m : Nat) (a : Ω m)
    (null : IndependentComparison J q → likelihoodGain logLikelihood q m a < penalty m * dimensionGain dimension q)
    (alternative : ¬ IndependentComparison J q → penalty m * dimensionGain dimension q < likelihoodGain logLikelihood q m a) :
    CorrectSign J (penalizedScore dimension penalty logLikelihood m a) q := by
  rcases q with ⟨child, parent, P⟩
  intro _ _ _
  refine ⟨?_, ?_⟩
  · intro ci
    exact (penalized_comparisons _ _ _ _ _).1.mpr (null ci)
  · intro dep
    exact (penalized_comparisons _ _ _ _ _).2.mpr (alternative dep)

/-- For a fixed parent comparison, the two likelihood regimes and the
penalty rates imply vanishing probability of a wrong or tied score sign. -/
theorem comparison_error_vanishes_of_likelihood_tails {J : Relation n}
    (law : ∀ m, FiniteLaw (Ω m)) (dimension : Fin n → LocalScore n) (penalty : Nat → Rat)
    (logLikelihood : ∀ m, Ω m → Fin n → LocalScore n) (growth : PenaltyGrowth penalty) (q : Comparison n)
    (increase : ValidComparison q → 0 < dimensionGain dimension q)
    (null : ValidComparison q → IndependentComparison J q → LikelihoodTightAbove law (likelihoodGain logLikelihood q))
    (alternative : ValidComparison q → ¬ IndependentComparison J q → LikelihoodLinearGap law (likelihoodGain logLikelihood q)) :
    ∀ ε : Rat, 0 < ε → ∃ N, ∀ m, N ≤ m →
      (law m).mass (fun a => comparisonError J (penalizedScore dimension penalty logLikelihood m a) q) < ε := by
  classical
  intro ε positive
  by_cases valid : ValidComparison q
  · have scaled := penalty_scale penalty growth (increase valid)
    by_cases ci : IndependentComparison J q
    · obtain ⟨B, N₀, tail⟩ := null valid ci ε positive
      obtain ⟨N₁, larger⟩ := scaled.diverges B
      refine ⟨max N₀ N₁, fun m late => rat_lt_of_le_of_lt ?_ (tail m (Nat.le_trans (Nat.le_max_left _ _) late))⟩
      apply FiniteLaw.mass_mono
      intro a _ error
      apply decide_eq_true
      apply Classical.byContradiction
      intro noTail
      have threshold := larger m (Nat.le_trans (Nat.le_max_right _ _) late)
      have signs := correct_sign_of_gain (J := J) (dimension := dimension) (q := q) (penalty := penalty) m a
        (fun _ => rat_lt_of_le_of_lt (Rat.not_lt.mp noTail) threshold) (fun fail => (fail ci).elim)
      simp [comparisonError, signs] at error
    · obtain ⟨κ, κpos, gap⟩ := alternative valid ci
      obtain ⟨N₀, tail⟩ := gap ε positive
      obtain ⟨N₁, smaller⟩ := scaled.sublinear κ κpos
      refine ⟨max N₀ N₁, fun m late => rat_lt_of_le_of_lt ?_ (tail m (Nat.le_trans (Nat.le_max_left _ _) late))⟩
      apply FiniteLaw.mass_mono
      intro a _ error
      apply decide_eq_true
      apply Classical.byContradiction
      intro noGap
      have threshold := smaller m (Nat.le_trans (Nat.le_max_right _ _) late)
      have signs := correct_sign_of_gain (J := J) (dimension := dimension) (q := q) (penalty := penalty) m a
        (fun independent => (ci independent).elim)
        (fun _ => Rat.not_le.mp (fun wrong => Rat.not_lt.mpr (Rat.le_trans (Rat.not_lt.mp noGap) wrong) threshold))
      simp [comparisonError, signs] at error
  · have allValid (scores : Fin n → LocalScore n) : CorrectSign J scores q := by
      rcases q with ⟨child, parent, P⟩
      intro different outChild outParent
      exact (valid ⟨different, outChild, outParent⟩).elim
    refine ⟨0, fun m _ => ?_⟩
    have zero : (law m).mass (fun _ => false) = 0 := by
      unfold FiniteLaw.mass FiniteMass.mass
      have sumZero (xs : List (Ω m)) : (xs.map (fun _ => (0 : Rat))).sum = 0 := by
        induction xs <;> simp_all [Rat.zero_add]
      simpa using sumZero (law m).atoms
    simpa [comparisonError, allValid, zero] using positive

end

end OpenCausalScience.Papers.AndrewsEtAl2023.PenalizedLikelihood
