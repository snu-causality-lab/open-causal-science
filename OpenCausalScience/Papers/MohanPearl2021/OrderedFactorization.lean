module
public import OpenCausalScience.Graph.DSeparation
public import OpenCausalScience.Papers.BareinboimTianPearl2014.ConditionalRecovery

/-! Mohan and Pearl (2021), Theorem 1, Corollary 2, and Figure 4(a).
An admissible factor may condition on partially observed variables;
the supplied response event records all entries that the factor uses. -/

namespace OpenCausalScience.Papers.MohanPearl2021.OrderedFactorization

open BareinboimTianPearl2014.ConditionalRecovery
  (atSelection conditional joint IndependentIn selected_conditional_eq_population)

@[expose] public section

variable {Ω : Type}

/-- The recorded and underlying events agree when all variables used by
the factor are observed. This includes partially observed conditions. -/
structure Factor (Ω : Type) where
  target : Ω → Bool
  condition : Ω → Bool
  recordedTarget : Ω → Bool
  recordedCondition : Ω → Bool
  responses : Ω → Bool
  targetAgreement : ∀ unit, responses unit = true → recordedTarget unit = target unit
  conditionAgreement : ∀ unit, responses unit = true → recordedCondition unit = condition unit

def Factor.observable (mass : (Ω → Bool) → Rat) (f : Factor Ω) : Rat :=
  conditional mass f.recordedTarget (atSelection f.recordedCondition f.responses)

def Factor.underlying (mass : (Ω → Bool) → Rat) (f : Factor Ω) : Rat :=
  conditional mass f.target f.condition

def Factor.supportedIndependent (mass : (Ω → Bool) → Rat) (f : Factor Ω) : Prop :=
  mass f.condition ≠ 0 ∧ mass (atSelection f.condition f.responses) ≠ 0 ∧
    IndependentIn mass f.target f.condition f.responses

theorem factor_recovers (mass : (Ω → Bool) → Rat) (f : Factor Ω)
    (hypotheses : f.supportedIndependent mass) :
    f.observable mass = f.underlying mass := by
  obtain ⟨targetSupport, observedSupport, independent⟩ := hypotheses
  have givenEq : atSelection f.recordedCondition f.responses = atSelection f.condition f.responses := by
    funext u
    cases h : f.responses u
    · simp [atSelection, h]
    · simp [atSelection, h, f.conditionAgreement _ h]
  have eventEq :
      (fun u => f.recordedTarget u && atSelection f.condition f.responses u) =
      (fun u => f.target u && atSelection f.condition f.responses u) := by
    funext u
    cases h : f.responses u
    · simp [atSelection, h]
    · simp [atSelection, h, f.targetAgreement _ h]
  have equalProjections : f.observable mass =
      conditional mass f.target (atSelection f.condition f.responses) := by
    unfold Factor.observable
    rw [givenEq]
    unfold conditional joint
    rw [eventEq]
  exact equalProjections.trans (selected_conditional_eq_population mass _ _ _ observedSupport
    targetSupport independent)

/-- Theorem 1 permits both individual ordered products and sums of
ordered products, with the specified observation event for each factor. -/
theorem sum_of_admissible_factorizations_recovers (mass : (Ω → Bool) → Rat)
    (terms : List (List (Factor Ω)))
    (admissible : ∀ term ∈ terms, ∀ factor ∈ term, factor.supportedIndependent mass) :
    (terms.map fun term => (term.map (Factor.observable mass)).prod).sum =
      (terms.map fun term => (term.map (Factor.underlying mass)).prod).sum := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro term ht
  apply congrArg List.prod
  apply List.map_congr_left
  intro factor hf
  exact factor_recovers mass factor (admissible term ht factor hf)

/-- Corollary 2. Under the indicated conditional independence, a
manifest complete-case conditional times a fully observed marginal
gives the population joint cell. -/
theorem mar_joint_from_manifest (mass : (Ω → Bool) → Rat) (f : Factor Ω)
    (admissible : f.supportedIndependent mass) :
    f.observable mass * mass f.condition = joint mass f.target f.condition := by
  rw [factor_recovers mass f admissible, Factor.underlying, conditional,
    Rat.div_mul_cancel admissible.1]

/-- Figure 4(a) with vertices Y, X, R_X, R_Y. -/
def figure4a : DAG 4 where
  edge u v := ([(0, 1), (1, 3)] : List (Fin 4 × Fin 4)).contains (u, v)
  rank v := v.val
  edge_increases := by decide

theorem figure4a_separations :
    figure4a.dSeparated 0 2 [1] = some true ∧
    figure4a.dSeparated 0 3 [1] = some true ∧
    figure4a.dSeparated 1 2 [] = some true ∧
    figure4a.dSeparated 0 3 [] = some false := by decide +kernel

end
end OpenCausalScience.Papers.MohanPearl2021.OrderedFactorization
