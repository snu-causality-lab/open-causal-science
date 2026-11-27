module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Constraint-aware canonical-domain reduction

Choe, Kwon, Park and Lee (UAI 2026), Proposition 3.1 and Appendix I.1.
https://proceedings.mlr.press/v337/choe26a.html

The finite linear program has a probability vector, one objective, and linear
information rows. When the objective and every row factor through a surjective
state map, summing over its fibers preserves the attainable objective values.
A right inverse lifts each reduced probability vector to a full vector.
-/

namespace OpenCausalScienceAnalysis.CanonicalDomainReduction

@[expose] public section

open scoped BigOperators

/-- Nonnegative masses summing to one on a finite state space. -/
def IsProbability {Ω : Type*} [Fintype Ω] (weight : Ω → ℝ) : Prop :=
  (∀ u, 0 ≤ weight u) ∧ ∑ u, weight u = 1

/-- The linear functional specified by one row of coefficients. -/
noncomputable def linearValue {Ω : Type*} [Fintype Ω] (weight coefficient : Ω → ℝ) : ℝ :=
  ∑ u, coefficient u * weight u

/-- The probability simplex intersected with the information equalities. -/
def Feasible {Ω I : Type*} [Fintype Ω] (rows : I → Ω → ℝ) (observed : I → ℝ)
    (weight : Ω → ℝ) : Prop :=
  IsProbability weight ∧ ∀ i, linearValue weight (rows i) = observed i

/-- All objective values realized by a feasible probability vector. -/
def attainableValues {Ω I : Type*} [Fintype Ω] (query : Ω → ℝ) (rows : I → Ω → ℝ)
    (observed : I → ℝ) : Set ℝ :=
  {value | ∃ weight, Feasible rows observed weight ∧ linearValue weight query = value}

/-- Multiplication by the paper's pushforward matrix Π. -/
noncomputable def pushforward {Full Reduced : Type*} [Fintype Full]
    (π : Full → Reduced) (weight : Full → ℝ) (t : Reduced) : ℝ := by
  classical
  exact ∑ u, if π u = t then weight u else 0

/-- Evaluating a reduced row after pushforward equals evaluating its pullback. -/
theorem linear_value_pushforward {Full Reduced : Type*} [Fintype Full] [Fintype Reduced]
    (π : Full → Reduced) (weight : Full → ℝ) (coefficient : Reduced → ℝ) :
    linearValue (pushforward π weight) coefficient = linearValue weight (coefficient ∘ π) := by
  classical
  unfold linearValue pushforward
  simp only [Finset.mul_sum]
  calc
    _ = ∑ t, ∑ u, if π u = t then coefficient t * weight u else 0 := by
      refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun u _ => ?_))
      by_cases h : π u = t <;> simp [h]
    _ = ∑ u, ∑ t, if π u = t then coefficient t * weight u else 0 := Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [Finset.sum_eq_single (π u)]
      · simp
      · intro t _ h
        simp [Ne.symm h]
      · simp

private theorem total_mass_pushforward {Full Reduced : Type*} [Fintype Full] [Fintype Reduced]
    (π : Full → Reduced) (weight : Full → ℝ) :
    (∑ t, pushforward π weight t) = ∑ u, weight u := by
  simpa only [linearValue, Function.comp_apply, one_mul] using
    linear_value_pushforward π weight (fun _ => 1)

/-- Pushing a probability vector forward preserves its nonnegativity and unit mass. -/
theorem probability_pushforward {Full Reduced : Type*} [Fintype Full] [Fintype Reduced]
    (π : Full → Reduced) {weight : Full → ℝ} (hweight : IsProbability weight) :
    IsProbability (pushforward π weight) := by
  classical
  refine ⟨?_, (total_mass_pushforward π weight).trans hweight.2⟩
  intro t
  unfold pushforward
  apply Finset.sum_nonneg
  intro u _
  split
  · exact hweight.1 u
  · exact le_rfl

/-- Give each chosen representative the mass of its reduced state. -/
noncomputable def lift {Full Reduced : Type*} (π : Full → Reduced) (representative : Reduced → Full)
    (weight : Reduced → ℝ) (u : Full) : ℝ := by
  classical
  exact if representative (π u) = u then weight (π u) else 0

/-- The selector lift recovers the entire reduced probability vector. -/
theorem pushforward_lift {Full Reduced : Type*} [Fintype Full]
    (π : Full → Reduced) (representative : Reduced → Full)
    (rightInverse : Function.RightInverse representative π) (weight : Reduced → ℝ) :
    pushforward π (lift π representative weight) = weight := by
  classical
  funext t
  unfold pushforward
  rw [Finset.sum_eq_single (representative t)]
  · simp [lift, rightInverse t]
  · intro u _ hu
    by_cases h : π u = t
    · simp [lift, h, Ne.symm hu]
    · simp [h]
  · simp

private theorem probability_lift {Full Reduced : Type*} [Fintype Full] [Fintype Reduced]
    (π : Full → Reduced) (representative : Reduced → Full)
    (rightInverse : Function.RightInverse representative π) {weight : Reduced → ℝ}
    (hweight : IsProbability weight) : IsProbability (lift π representative weight) := by
  classical
  refine ⟨?_, ?_⟩
  · intro u
    unfold lift
    split
    · exact hweight.1 (π u)
    · exact le_rfl
  · have total := total_mass_pushforward π (lift π representative weight)
    rw [pushforward_lift π representative rightInverse weight] at total
    exact total.symm.trans hweight.2

private theorem feasible_pushforward_iff {Full Reduced I : Type*} [Fintype Full] [Fintype Reduced]
    (π : Full → Reduced) {ψ : Full → ℝ} (probability : IsProbability ψ)
    (M : I → Full → ℝ) (reducedM : I → Reduced → ℝ) (p : I → ℝ)
    (hRows : ∀ i, M i = reducedM i ∘ π) :
    Feasible reducedM p (pushforward π ψ) ↔ Feasible M p ψ := by
  unfold Feasible
  simp only [linear_value_pushforward, ← hRows, probability_pushforward π probability,
    probability, true_and]

/-- Proposition 3.1. The objective and all information rows must factor through
the same surjective map. The two feasible sets attain exactly the same values. -/
theorem attainable_values_eq {Full Reduced I : Type*} [Fintype Full] [Fintype Reduced]
    (π : Full → Reduced) (surjective : Function.Surjective π)
    (c : Full → ℝ) (reducedC : Reduced → ℝ) (M : I → Full → ℝ) (reducedM : I → Reduced → ℝ)
    (p : I → ℝ) (hQuery : c = reducedC ∘ π) (hRows : ∀ i, M i = reducedM i ∘ π) :
    attainableValues c M p = attainableValues reducedC reducedM p := by
  ext value
  constructor
  · rintro ⟨ψ, hψ, objective⟩
    refine ⟨pushforward π ψ, (feasible_pushforward_iff π hψ.1 M reducedM p hRows).mpr hψ, ?_⟩
    rwa [linear_value_pushforward, ← hQuery]
  · rintro ⟨φ, hφ, objective⟩
    let representative : Reduced → Full := fun t => Classical.choose (surjective t)
    have rightInverse : Function.RightInverse representative π :=
      fun t => Classical.choose_spec (surjective t)
    let ψ := lift π representative φ
    have pushed : pushforward π ψ = φ := pushforward_lift π representative rightInverse φ
    have probability : IsProbability ψ := probability_lift π representative rightInverse hφ.1
    refine ⟨ψ, (feasible_pushforward_iff π probability M reducedM p hRows).mp ?_, ?_⟩
    · rwa [pushed]
    · rwa [hQuery, ← linear_value_pushforward, pushed]

/-- The lower and upper bounds agree, as do the full sets of attainable values. -/
theorem sharp_bounds_eq {Full Reduced I : Type*} [Fintype Full] [Fintype Reduced]
    (π : Full → Reduced) (surjective : Function.Surjective π)
    (c : Full → ℝ) (reducedC : Reduced → ℝ) (M : I → Full → ℝ) (reducedM : I → Reduced → ℝ)
    (p : I → ℝ) (hQuery : c = reducedC ∘ π) (hRows : ∀ i, M i = reducedM i ∘ π) :
    sInf (attainableValues c M p) = sInf (attainableValues reducedC reducedM p) ∧
      sSup (attainableValues c M p) = sSup (attainableValues reducedC reducedM p) := by
  rw [attainable_values_eq π surjective c reducedC M reducedM p hQuery hRows]
  exact ⟨rfl, rfl⟩

end

end OpenCausalScienceAnalysis.CanonicalDomainReduction
