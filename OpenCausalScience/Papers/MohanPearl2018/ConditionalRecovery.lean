module
public import OpenCausalScience.Graph.DSeparation
public import OpenCausalScience.Papers.BareinboimTian2015.KernelIdentities
public import OpenCausalScience.Papers.BareinboimTianPearl2014.ConditionalRecovery

/-! Mohan and Pearl (2018), Figures 1(a)–(b), Examples 1–2.
`true` means a response is observed, corresponding to R=0 in the paper. -/

namespace OpenCausalScience.Papers.MohanPearl2018.ConditionalRecovery

open BareinboimTian2015.KernelIdentities (selected_prefix_ratio_eq_population)
open BareinboimTianPearl2014.ConditionalRecovery
  (atSelection conditional IndependentIn selected_conditional_eq_population)

@[expose] public section

variable {Ω A : Type}

/-- Equation (1). The observed proxy retains the value exactly for a response. -/
def proxy (x : Ω → A) (seeX : Ω → Bool) (unit : Ω) : Option A :=
  if seeX unit then some (x unit) else none

theorem proxy_matches_observed_value [DecidableEq A] (x : Ω → A)
    (seeX : Ω → Bool) (a : A) (unit : Ω) :
    decide (proxy x seeX unit = some a) = (decide (x unit = a) && seeX unit) := by
  cases h : seeX unit <;> simp [proxy, h]

/-- Example 1, at a given outcome Y and supported stratum. The left
conditional uses only the manifest proxy and observed events. -/
theorem proxy_conditional_recovers_target [DecidableEq A] (mass : (Ω → Bool) → Rat)
    (x : Ω → A) (seeX givenY : Ω → Bool) (a : A)
    (sourceSupport : mass (atSelection givenY seeX) ≠ 0)
    (targetSupport : mass givenY ≠ 0)
    (independent : IndependentIn mass (fun u => decide (x u = a)) givenY seeX) :
    conditional mass (fun u => decide (proxy x seeX u = some a)) (atSelection givenY seeX) =
      conditional mass (fun u => decide (x u = a)) givenY := by
  have equalEvents :
      (fun u => decide (proxy x seeX u = some a) && atSelection givenY seeX u) =
      (fun u => decide (x u = a) && atSelection givenY seeX u) := by
    funext u
    cases h : seeX u <;> simp [atSelection, proxy_matches_observed_value, h]
  have same : conditional mass (fun u => decide (proxy x seeX u = some a))
      (atSelection givenY seeX) =
      conditional mass (fun u => decide (x u = a)) (atSelection givenY seeX) := by
    unfold conditional BareinboimTianPearl2014.ConditionalRecovery.joint
    rw [equalEvents]
  exact same.trans (selected_conditional_eq_population mass _ _ _ sourceSupport targetSupport
    independent)

/-- Example 2. Once X is recorded, the Y response rate is an observable
conditional on the X proxy. The source independence permits dropping
the stratum of the underlying Y from that rate. -/
theorem response_rate_from_observed_x [DecidableEq A] (mass : (Ω → Bool) → Rat)
    (x : Ω → A) (seeX seeY givenY : Ω → Bool) (a : A)
    (observedSupport : mass (atSelection (fun u => decide (x u = a)) seeX) ≠ 0)
    (stratumSupport : mass
      (atSelection (atSelection (fun u => decide (x u = a)) seeX) givenY) ≠ 0)
    (independent : IndependentIn mass seeY
      (atSelection (fun u => decide (x u = a)) seeX) givenY) :
    conditional mass seeY
        (atSelection (atSelection (fun u => decide (x u = a)) seeX) givenY) =
      conditional mass seeY (fun u => decide (proxy x seeX u = some a)) := by
  have observedCondition :
      (fun u => decide (proxy x seeX u = some a)) = atSelection (fun u => decide (x u = a)) seeX :=
    funext (proxy_matches_observed_value x seeX a)
  rw [observedCondition]
  exact selected_conditional_eq_population mass seeY _ givenY stratumSupport
    observedSupport independent

/-- Observed masses of the proxy and the fully observed Y in Table 1. -/
def manifest (x : Option Bool) : Rat :=
  match x with
  | none => 2/10
  | some false => 2/10
  | some true => 1/10

def table1Recover (x : Bool) : Rat :=
  manifest (some x) / (manifest (some false) + manifest (some true)) *
    (manifest (some false) + manifest (some true) + manifest none)

theorem tables1_and2_exact (x : Bool) :
    table1Recover x = (if x then 1/6 else 1/3) := by
  cases x <;> decide +kernel

/-- The substantive/response subgraph in Figure 1(a), with vertices
X, Y and R_X. The omitted proxy has no children. -/
def figure1a : DAG 3 where
  edge u v := ([(0, 1), (1, 2)] : List (Fin 3 × Fin 3)).contains (u, v)
  rank v := v.val
  edge_increases := by decide

theorem figure1a_separation :
    figure1a.dSeparated 0 2 [1] = some true ∧
    figure1a.dSeparated 0 2 [] = some false := by decide +kernel

/-- Figure 1(b), with vertices Y, X, R_X and R_Y. -/
def figure1b : DAG 4 where
  edge u v := ([(0, 1), (0, 2), (1, 3), (2, 3)] : List (Fin 4 × Fin 4)).contains (u, v)
  rank v := v.val
  edge_increases := by decide

theorem figure1b_separations :
    figure1b.dSeparated 2 1 [0] = some true ∧
    figure1b.dSeparated 3 0 [1, 2] = some true ∧
    figure1b.dSeparated 2 1 [0, 3] = some false := by decide +kernel

/-- A positive factorization of Figure 1(b). The two substantive values and
R_X each have conditional probability one half. R_Y is more likely to
be observed when X and R_X are both true. -/
def exampleCell (_y x seeX seeY : Bool) : Rat :=
  let rate : Rat := if x && seeX then 3/4 else 1/4
  (1/2) * (1/2) * (1/2) * (if seeY then rate else 1 - rate)

theorem example_cells_positive (y x seeX seeY : Bool) : 0 < exampleCell y x seeX seeY := by
  cases y <;> cases x <;> cases seeX <;> cases seeY <;> decide +kernel

theorem example_law_normalized :
    (([false, true].flatMap fun y => [false, true].flatMap fun x =>
      [false, true].flatMap fun seeX => [false, true].map (exampleCell y x seeX))).sum = 1 := by
  decide +kernel

theorem example_collider_dependence :
    exampleCell false false false true * exampleCell false true true true ≠
      exampleCell false true false true * exampleCell false false true true := by
  decide +kernel

/-- Normalize the complete-case cells after removing the observable R_Y
response probability. The R_X rate is constant in the Y stratum and
therefore cancels. Each cell represents a possible value of X at this Y. -/
theorem conditional_from_complete_cases (x : A) (values : List A)
    (joint complete seenY : A → Rat) (seenX : Rat)
    (factorized : ∀ a ∈ x :: values, complete a = seenX * joint a * seenY a)
    (seenYSupport : ∀ a ∈ x :: values, seenY a ≠ 0)
    (seenXSupport : seenX ≠ 0)
    (stratumSupport : (values.map joint).sum ≠ 0) :
    (complete x / seenY x) / (values.map (fun a => complete a / seenY a)).sum =
      joint x / (values.map joint).sum := by
  have corrected : ∀ a ∈ x :: values, complete a / seenY a = seenX * joint a := by
    intro a h
    rw [factorized a h, Rat.mul_div_cancel (seenYSupport a h)]
  rw [corrected x List.mem_cons_self]
  have denom : (values.map (fun a => complete a / seenY a)) =
      values.map (fun a => seenX * joint a) := by
    apply List.map_congr_left
    intro a h
    exact corrected a (List.mem_cons_of_mem _ h)
  rw [denom]
  simpa [Rat.add_zero] using selected_prefix_ratio_eq_population [x] values joint (fun _ => seenX)
      seenX (by simp) seenXSupport stratumSupport

end
end OpenCausalScience.Papers.MohanPearl2018.ConditionalRecovery
