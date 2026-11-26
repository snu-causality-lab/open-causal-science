module
public import OpenCausalScience.Papers.TianPearl2003.AncestralMarginal

/-! The external intervention equality used in Eq. (6) of Elahi et al.
(2024), Appendix C.2. All directed external parents of the retained
vertices are already clamped, and both settings leave the retained
vertices untouched. -/

@[expose] public section

namespace OpenCausalScience.Papers.ElahiEtAl2024.ExternalIntervention

open TianPearl2003.AncestralMarginal

variable {n : Nat} {Ω : Type}

/-- When a setting clamps every external parent of S, extending it with
interventions outside S preserves each response on S, unit by unit. -/
theorem same_target_response_after_external_intervention (G : DAG n)
    (mechanism : Ω → Fin n → (Fin n → Bool) → Bool) (unit : Ω)
    (keep : Fin n → Bool) (parents expanded : Setting n)
    (closed : ancestralAmongFree G keep parents)
    (agrees : ∀ v, parents v ≠ none → expanded v = parents v)
    (parentsFree : ∀ v, keep v = true → parents v = none)
    (expandedFree : ∀ v, keep v = true → expanded v = none)
    (v : Fin n) (retained : keep v = true) :
    evaluate G mechanism unit parents v = evaluate G mechanism unit expanded v := by
  let outsideValue : Fin n → Bool := fun u => (expanded u).getD false
  have closedExpanded : ancestralAmongFree G keep expanded := by
    intro a b edge inside
    rcases closed a b edge inside with insideA | fixed
    · exact .inl insideA
    · exact .inr ((agrees a fixed).symm ▸ fixed)
  have fullAgreement :
      addClamps keep outsideValue parents = addClamps keep outsideValue expanded := by
    funext a
    by_cases inTarget : keep a = true
    · simp [addClamps, inTarget, parentsFree a inTarget, expandedFree a inTarget]
    · cases parentValue : parents a with
      | none =>
          cases expandedValue : expanded a with
          | none => simp [addClamps, inTarget, parentValue, expandedValue]
          | some value =>
              simp [addClamps, inTarget, parentValue, expandedValue, outsideValue]
      | some value =>
          have fixed : parents a ≠ none := fun h => by simp [parentValue] at h
          have expandedValue : expanded a = some value := (agrees a fixed).trans parentValue
          simp [addClamps, inTarget, expandedValue, parentValue]
  calc
    evaluate G mechanism unit parents v =
        evaluate G mechanism unit (addClamps keep outsideValue parents) v :=
      retained_evaluation_unchanged G mechanism unit keep outsideValue parents closed v retained
    _ = evaluate G mechanism unit (addClamps keep outsideValue expanded) v :=
      congrArg (fun setting => evaluate G mechanism unit setting v) fullAgreement
    _ = evaluate G mechanism unit expanded v :=
      (retained_evaluation_unchanged G mechanism unit keep outsideValue expanded
        closedExpanded v retained).symm

/-- The same statement for events on S, under a shared finite exogenous
law. The exogenous weights need not factor across structural equations. -/
theorem same_target_mass_after_external_intervention (G : DAG n)
    (mechanism : Ω → Fin n → (Fin n → Bool) → Bool) (units : List Ω) (weight : Ω → Rat)
    (keep : Fin n → Bool) (parents expanded : Setting n)
    (closed : ancestralAmongFree G keep parents)
    (agrees : ∀ v, parents v ≠ none → expanded v = parents v)
    (parentsFree : ∀ v, keep v = true → parents v = none)
    (expandedFree : ∀ v, keep v = true → expanded v = none)
    (event : (Fin n → Bool) → Bool) (reads : readsOnly event keep) :
    mass units weight (fun unit => event (evaluate G mechanism unit parents)) =
      mass units weight (fun unit => event (evaluate G mechanism unit expanded)) := by
  apply congrArg (mass units weight)
  funext unit
  apply reads
  intro v retained
  exact same_target_response_after_external_intervention G mechanism unit keep parents
    expanded closed agrees parentsFree expandedFree v retained

end OpenCausalScience.Papers.ElahiEtAl2024.ExternalIntervention
