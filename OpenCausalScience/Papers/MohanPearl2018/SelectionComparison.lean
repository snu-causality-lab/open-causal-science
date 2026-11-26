module
public import OpenCausalScience.Papers.MohanPearl2018.ConditionalRecovery

/-! Comparison with selected-sample recovery for Figure 1(a). The manifest
records the fully observed stratum even when the proxy is missing. -/

namespace OpenCausalScience.Papers.MohanPearl2018.SelectionComparison

open BareinboimTianPearl2014.ConditionalRecovery
  (atSelection conditional IndependentIn joint)
open MohanPearl2018.ConditionalRecovery (proxy proxy_conditional_recovers_target)

@[expose] public section

theorem complete_case_conditional_times_population_margin {Ω A : Type} [DecidableEq A]
    (mass : (Ω → Bool) → Rat) (x : Ω → A) (response stratum : Ω → Bool) (a : A)
    (selectedSupport : mass (atSelection stratum response) ≠ 0)
    (populationSupport : mass stratum ≠ 0)
    (independent : IndependentIn mass (fun u => decide (x u = a)) stratum response) :
    conditional mass (fun u => decide (proxy x response u = some a))
        (atSelection stratum response) * mass stratum =
      joint mass (fun u => decide (x u = a)) stratum := by
  rw [proxy_conditional_recovers_target mass x response stratum a selectedSupport
    populationSupport independent, conditional, Rat.div_mul_cancel populationSupport]

def stratumMass (tilted y : Bool) : Rat :=
  if tilted then (if y then 5 / 8 else 3 / 8) else 1 / 2

def conditionalCell (x y : Bool) : Rat :=
  if x == y then 3 / 4 else 1 / 4

def responseRate (tilted y : Bool) : Rat :=
  if tilted then (if y then 2 / 5 else 2 / 3) else 1 / 2

def populationCell (tilted x y : Bool) : Rat :=
  stratumMass tilted y * conditionalCell x y

def completeCaseCell (tilted x y : Bool) : Rat :=
  populationCell tilted x y * responseRate tilted y

def manifestCell (tilted : Bool) (recorded : Option Bool) (y : Bool) : Rat :=
  match recorded with
  | some x => completeCaseCell tilted x y
  | none => stratumMass tilted y * (1 - responseRate tilted y)

theorem both_models_positive_and_normalized (tilted x y r : Bool) :
    0 < populationCell tilted x y *
          (if r then responseRate tilted y else 1 - responseRate tilted y) ∧
      (([false, true].flatMap fun u => [false, true].map
        (fun v => populationCell tilted u v))).sum = 1 := by
  cases tilted <;> cases x <;> cases y <;> cases r <;> decide +kernel

theorem equal_complete_case_measures (x y : Bool) :
    completeCaseCell false x y = completeCaseCell true x y := by
  cases x <;> cases y <;> decide +kernel

theorem different_population_and_incomplete_cases :
    populationCell false true true ≠ populationCell true true true ∧
      manifestCell false none true ≠ manifestCell true none true := by
  decide +kernel

theorem joint_cell_from_complete_and_incomplete_cases (tilted x y : Bool) :
    (manifestCell tilted (some x) y /
      (manifestCell tilted (some false) y + manifestCell tilted (some true) y)) *
    (manifestCell tilted (some false) y + manifestCell tilted (some true) y +
      manifestCell tilted none y) = populationCell tilted x y := by
  cases tilted <;> cases x <;> cases y <;> decide +kernel

theorem no_recovery_from_only_complete_cases :
    ¬ ∃ recover : (Bool → Bool → Rat) → Rat,
      ∀ tilted, recover (completeCaseCell tilted) = populationCell tilted true true := by
  rintro ⟨recover, valid⟩
  have same : completeCaseCell false = completeCaseCell true := by
    funext x y
    exact equal_complete_case_measures x y
  exact different_population_and_incomplete_cases.1
    ((valid false).symm.trans ((congrArg recover same).trans (valid true)))

end

end OpenCausalScience.Papers.MohanPearl2018.SelectionComparison
