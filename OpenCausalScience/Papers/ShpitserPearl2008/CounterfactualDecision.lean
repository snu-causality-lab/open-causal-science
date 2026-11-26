module
public import OpenCausalScience.Papers.ShpitserPearl2008.ParallelWorlds

/-! # Counterfactual identification base cases

Shpitser and Pearl (2008), Figure 12 and Appendix A.3, Lemma 42.
The first three lines of ID* use the empty conjunction and effectiveness.
A single compatible intervention represents several world queries when it
agrees with each world at the variables that can affect the queried response.
A conditional mass is undefined at zero evidence mass.
https://www.jmlr.org/papers/volume9/shpitser08a/shpitser08a.pdf#page=21
-/

namespace OpenCausalScience.Papers.ShpitserPearl2008.CounterfactualDecision

open TianPearl2003.AncestralMarginal (Setting evaluate mass)
open ParallelWorlds

@[expose] public section

variable {n : Nat} {W Ω : Type}

/-- Reflexive ancestry after removing arrows into fixed variables. -/
inductive Relevant (G : DAG n) (setting : Setting n) : Fin n → Fin n → Prop
  | self (v) : Relevant G setting v v
  | through {u p v} : Relevant G setting u p → G.edge p v = true →
      setting v = none → Relevant G setting u v

theorem response_eq_of_agreeing_settings (G : DAG n) (mechanism : Mechanism Ω n)
    (unit : Ω) (source target : Setting n) (v : Fin n)
    (agree : ∀ u, Relevant G source u v → source u = target u) :
    evaluate G mechanism unit source v = evaluate G mechanism unit target v := by
  induction height : G.rank v using Nat.strongRecOn generalizing v with
  | ind rank ih =>
    rw [evaluate, evaluate, ← agree v (.self v)]
    cases free : source v with
    | some value => rfl
    | none =>
      apply congrArg (mechanism unit v)
      funext p
      by_cases arrow : G.edge p v = true
      · simp only [dite_eq_left arrow]
        apply ih (G.rank p) (height ▸ G.edge_increases _ _ arrow) p _ rfl
        exact fun u path => agree u (.through path arrow free)
      · simp [arrow]

/-- Using the union of world assignments in the successful base case is
valid when it agrees on each queried atom's fixed-graph ancestry. -/
theorem union_action_mass (G : DAG n) (mechanism : Mechanism Ω n)
    (settings : W → Setting n) (union : Setting n) (units : List Ω) (weight : Ω → Rat)
    (query : List (Atom W n))
    (agree : ∀ atom ∈ query, ∀ u, Relevant G (settings atom.copy.1) u atom.copy.2 →
      settings atom.copy.1 u = union u) :
    mass units weight (fun unit => holds (response G mechanism settings unit) query) =
      mass units weight (fun unit => holds (fun c => evaluate G mechanism unit union c.2) query) := by
  apply congrArg (mass units weight)
  funext unit
  apply holds_congr
  intro atom member
  exact response_eq_of_agreeing_settings G mechanism unit (settings atom.copy.1) union
    atom.copy.2 (agree atom member)

private theorem mass_false (units : List Ω) (weight : Ω → Rat) :
    mass units weight (fun _ => false) = 0 := by
  induction units with
  | nil => rfl
  | cons unit units ih => simp [mass, Rat.zero_add] at ih ⊢; exact ih

theorem empty_query_mass (G : DAG n) (mechanism : Mechanism Ω n)
    (settings : W → Setting n) (units : List Ω) (weight : Ω → Rat)
    (normalized : (units.map weight).sum = 1) :
    mass units weight (fun unit => holds (response G mechanism settings unit) []) = 1 := by
  simpa [holds, mass] using normalized

theorem conflicting_own_setting_mass (G : DAG n) (mechanism : Mechanism Ω n)
    (settings : W → Setting n) (units : List Ω) (weight : Ω → Rat)
    (atom : Atom W n) (rest : List (Atom W n)) {fixed : Bool}
    (clamp : settings atom.copy.1 atom.copy.2 = some fixed) (distinct : fixed ≠ atom.value) :
    mass units weight (fun unit => holds (response G mechanism settings unit) (atom :: rest)) = 0 := by
  have impossible (unit : Ω) : holds (response G mechanism settings unit) (atom :: rest) = false := by
    have fixedResponse : response G mechanism settings unit atom.copy = fixed := by
      unfold response
      rw [evaluate, clamp]
    have diff : (fixed == atom.value) = false := beq_eq_false_iff_ne.mpr distinct
    simp [holds, fixedResponse, diff]
  simp only [impossible, mass_false]

theorem remove_own_setting_mass (G : DAG n) (mechanism : Mechanism Ω n)
    (settings : W → Setting n) (units : List Ω) (weight : Ω → Rat)
    (atom : Atom W n) (rest : List (Atom W n))
    (clamp : settings atom.copy.1 atom.copy.2 = some atom.value) :
    mass units weight (fun unit => holds (response G mechanism settings unit) (atom :: rest)) =
      mass units weight (fun unit => holds (response G mechanism settings unit) rest) := by
  apply congrArg (mass units weight)
  funext unit
  have fixedResponse : response G mechanism settings unit atom.copy = atom.value := by
    unfold response
    rw [evaluate, clamp]
  simp [holds, fixedResponse]

/-- Base-variable labels and interventions for a factor after irrelevant
subscripts and tautological atoms are removed. -/
structure FactorAtom (n : Nat) where
  vertex : Fin n
  value : Bool
  settings : Setting n

def interventionValues (factor : List (FactorAtom n)) : List (Fin n × Bool) :=
  factor.flatMap fun atom => (List.finRange n).filterMap fun v =>
    (atom.settings v).map fun value => (v, value)

def observedValues (factor : List (FactorAtom n)) : List (Fin n × Bool) :=
  factor.map fun atom => (atom.vertex, atom.value)

/-- The Fig. 12 line 8 test on an already simplified single-district
factor, including a conflict between two intervened values. -/
def hasConflict (factor : List (FactorAtom n)) : Bool :=
  let settings := interventionValues factor
  settings.any fun imposed => (settings ++ observedValues factor).any fun other =>
    imposed.1 == other.1 && imposed.2 != other.2

theorem has_conflict_iff (factor : List (FactorAtom n)) :
    hasConflict factor = true ↔ ∃ imposed ∈ interventionValues factor,
      ∃ other ∈ interventionValues factor ++ observedValues factor,
        imposed.1 = other.1 ∧ imposed.2 ≠ other.2 := by
  simp [hasConflict, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]

/-- The line 9 intervention, available when the line 8 test passes. -/
def baseAction (factor : List (FactorAtom n)) : Option (Setting n) :=
  if hasConflict factor then none
  else some fun v => (interventionValues factor).findSome? fun setting =>
    if setting.1 = v then some setting.2 else none

theorem base_action_fails_iff_conflict (factor : List (FactorAtom n)) :
    baseAction factor = none ↔ hasConflict factor = true := by
  cases conflict : hasConflict factor <;> simp [baseAction, conflict]

theorem base_action_preserves_settings {factor : List (FactorAtom n)} {action : Setting n}
    (success : baseAction factor = some action) {v : Fin n} {value : Bool}
    (member : (v, value) ∈ interventionValues factor) : action v = some value := by
  cases conflict : hasConflict factor with
  | true => simp [baseAction, conflict] at success
  | false =>
    simp only [baseAction, conflict, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at success
    rw [← success]
    let read : Fin n × Bool → Option Bool := fun setting =>
      if setting.1 = v then some setting.2 else none
    change (interventionValues factor).findSome? read = some value
    cases looked : (interventionValues factor).findSome? read with
    | none =>
      have absent := (List.findSome?_eq_none_iff.mp looked) (v, value) member
      simp [read] at absent
    | some found =>
      obtain ⟨before, imposed, after, decomposition, selected, _⟩ :=
        List.findSome?_eq_some_iff.mp looked
      have imposedMem : imposed ∈ interventionValues factor := by
        rw [decomposition]
        exact List.mem_append_right _ List.mem_cons_self
      have varMatch : imposed.1 = v := by
        by_cases same : imposed.1 = v
        · exact same
        · simp [read, same] at selected
      have selectedValue : imposed.2 = found := by
        simpa [read, varMatch] using selected
      have matchesValue : imposed.2 = value := by
        by_cases same : imposed.2 = value
        · exact same
        · have refused := (has_conflict_iff factor).mpr
            ⟨imposed, imposedMem, (v, value), List.mem_append_left _ member, varMatch, same⟩
          simp [conflict] at refused
      exact congrArg some (selectedValue.symm.trans matchesValue)

/-- The evidence denominator must be checked before conditional division. -/
def conditionalMass (units : List Ω) (weight : Ω → Rat) (outcome evidence : Ω → Bool) : Option Rat :=
  let denominator := mass units weight evidence
  if denominator = 0 then none
  else some (mass units weight (fun unit => outcome unit && evidence unit) / denominator)

theorem conditional_mass_undefined (units : List Ω) (weight : Ω → Rat)
    (outcome evidence : Ω → Bool) :
    conditionalMass units weight outcome evidence = none ↔ mass units weight evidence = 0 := by
  by_cases zero : mass units weight evidence = 0 <;> simp [conditionalMass, zero]

end
end OpenCausalScience.Papers.ShpitserPearl2008.CounterfactualDecision
