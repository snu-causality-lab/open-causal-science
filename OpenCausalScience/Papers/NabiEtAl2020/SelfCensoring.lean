module
public import Std

/-! The one-variable self-censoring case of Nabi, Bhattacharya and Shpitser (2020),
Theorems 1–2. The single partially observed binary variable is X¹, its response
indicator is R, and the deterministic proxy is X = X¹ if R is true. -/

@[expose] public section

namespace OpenCausalScience.Papers.NabiEtAl2020.SelfCensoring

structure Law where
  cell : Bool → Bool → Rat
  positive : ∀ x r, 0 < cell x r
  normalized : (cell false false + cell false true) + (cell true false + cell true true) = 1

def Law.target (p : Law) (x : Bool) : Rat :=
  p.cell x false + p.cell x true

def Law.response (p : Law) (x r : Bool) : Rat :=
  p.cell x r / p.target x

/-- The observed pair (X,R) has exactly three possible values. -/
def Law.observed (p : Law) : Option Bool → Rat
  | none => p.cell false false + p.cell true false
  | some x => p.cell x true

theorem Law.factorizes (p : Law) (x r : Bool) :
    p.cell x r = p.response x r * p.target x := by
  have supported : p.target x ≠ 0 := by
    have low := p.positive x false
    have high := p.positive x true
    unfold Law.target
    grind
  rw [Law.response, Rat.div_def, Rat.mul_assoc, Rat.inv_mul_cancel _ supported, Rat.mul_one]

theorem observed_eq_iff (p q : Law) :
    p.observed = q.observed ↔
      p.cell false true = q.cell false true ∧ p.cell true true = q.cell true true ∧
      p.cell false false + p.cell true false = q.cell false false + q.cell true false := by
  constructor
  · intro h
    exact ⟨congrFun h (some false), congrFun h (some true), congrFun h none⟩
  · rintro ⟨low, high, missing⟩
    funext observed
    cases observed with
    | none => exact missing
    | some x => cases x
                · exact low
                · exact high

def balanced : Law where
  cell := fun _ _ => 1 / 4
  positive := by intro x r; decide +kernel
  normalized := by decide +kernel

def selfCensoring : Law where
  cell x r := if r then 1 / 4 else if x then 3 / 8 else 1 / 8
  positive := by intro x r; cases x <;> cases r <;> decide +kernel
  normalized := by decide +kernel

theorem positive_self_censoring_counterpair :
    balanced.observed = selfCensoring.observed ∧
    balanced.cell true false ≠ selfCensoring.cell true false ∧
    balanced.target true ≠ selfCensoring.target true := by
  refine ⟨(observed_eq_iff _ _).2 ⟨?_, ?_, ?_⟩, ?_, ?_⟩ <;> decide +kernel

theorem counterpair_response_support (x r : Bool) :
    1 / 4 < balanced.response x r ∧ 1 / 4 < selfCensoring.response x r := by
  cases x <;> cases r <;> decide +kernel

theorem no_universal_target_recovery :
    ¬ ∃ recover : (Option Bool → Rat) → Rat, ∀ p : Law, recover p.observed = p.target true := by
  rintro ⟨recover, valid⟩
  obtain ⟨observed, _, target⟩ := positive_self_censoring_counterpair
  exact target ((valid balanced).symm.trans ((congrArg recover observed).trans (valid selfCensoring)))

end OpenCausalScience.Papers.NabiEtAl2020.SelfCensoring
