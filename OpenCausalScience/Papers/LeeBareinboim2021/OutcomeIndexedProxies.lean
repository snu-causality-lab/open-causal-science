module
public import OpenCausalScience.Papers.LeeBareinboim2021.ProxyInversion

/-! # Outcome-indexed proxies for identification

[Lee and Bareinboim, corrected version](https://www.sanghacklee.me/ai-corrected/matrix_equations_AI_corrected_2026-10-25.pdf),
Theorem 1 case (2b), Appendix C, equations (8)–(12). Vectors have a common
latent column domain. Each outcome slice has its own left inverse. One
must use these separate inverses before taking the observed latent marginal.
The target latent weights use the inverse at the queried outcome.
-/

namespace OpenCausalScience.Papers.LeeBareinboim2021.OutcomeIndexedProxies

open OpenCausalScience.Papers.LeeBareinboim2021.ProxyInversion (adjustmentTerm)

@[expose] public section

abbrev Vector (n : Nat) := Fin n → Rat
abbrev Matrix (rows cols : Nat) := Fin rows → Fin cols → Rat

def sum (terms : Vector n) : Rat := (List.ofFn terms).sum

def multiply (matrix : Matrix rows cols) (vector : Vector cols) : Vector rows :=
  fun i => sum fun j => matrix i j * vector j

/-- A left inverse acts on the same latent column domain in each application. -/
def Inverts (proxy : Matrix w u) (inverse : Matrix u w) : Prop :=
  ∀ v, multiply inverse (multiply proxy v) = v

def recoverJoint (inverse : Fin y → Matrix u w) (observed : Fin y → Vector w) : Fin y → Vector u :=
  fun outcome => multiply (inverse outcome) (observed outcome)

def marginalizeOutcome (joint : Fin y → Vector u) : Vector u :=
  fun latent => sum fun outcome => joint outcome latent

def estimate (inverse : Fin y → Matrix u w) (observed : Fin y → Vector w)
    (atOutcome : Fin y) (surrogate : Vector w) : Rat :=
  sum fun latent => adjustmentTerm (recoverJoint inverse observed atOutcome latent)
    (marginalizeOutcome (recoverJoint inverse observed) latent)
    (multiply (inverse atOutcome) surrogate latent)

/-- Equation (8) recovers the joint latent law separately at every outcome. -/
theorem recover_joint_slices {proxy : Fin y → Matrix w u} {inverse : Fin y → Matrix u w}
    (left : ∀ outcome, Inverts (proxy outcome) (inverse outcome))
    {observed : Fin y → Vector w} {joint : Fin y → Vector u}
    (observedFactor : ∀ outcome, observed outcome = multiply (proxy outcome) (joint outcome)) :
    recoverJoint inverse observed = joint := by
  funext outcome
  rw [recoverJoint, observedFactor outcome, left outcome _]

/-- Equation (9) obtains `Q(U | x)` by summing the deconvolved slices. -/
theorem recover_observed_marginal {proxy : Fin y → Matrix w u} {inverse : Fin y → Matrix u w}
    (left : ∀ outcome, Inverts (proxy outcome) (inverse outcome))
    {observed : Fin y → Vector w} {joint : Fin y → Vector u}
    (observedFactor : ∀ outcome, observed outcome = multiply (proxy outcome) (joint outcome)) :
    marginalizeOutcome (recoverJoint inverse observed) = marginalizeOutcome joint := by
  rw [recover_joint_slices left observedFactor]

/-- Equations (8)–(12) give the scalar interventional probability once
the observable joint and surrogate vectors have the stated factorizations.
The surrogate factorization and equality with the adjustment sum are the
graphical inputs. The left inverses can be pseudoinverses from the rank
condition. Zero target weight requires neither division nor conditional
response values on those states. -/
theorem outcome_indexed_identification {proxy : Fin y → Matrix w u} {inverse : Fin y → Matrix u w}
    (left : ∀ outcome, Inverts (proxy outcome) (inverse outcome))
    {observed : Fin y → Vector w} {joint : Fin y → Vector u}
    (observedFactor : ∀ outcome, observed outcome = multiply (proxy outcome) (joint outcome))
    (atOutcome : Fin y) (surrogate : Vector w) (target response : Vector u) (causalQuery : Rat)
    (surrogateFactor : surrogate = multiply (proxy atOutcome) target)
    (overlap : ∀ latent, target latent ≠ 0 → 0 < marginalizeOutcome joint latent)
    (chain : ∀ latent, target latent ≠ 0 →
      joint atOutcome latent = response latent * marginalizeOutcome joint latent)
    (adjustment : causalQuery = sum fun latent => response latent * target latent) :
    estimate inverse observed atOutcome surrogate = causalQuery := by
  rw [estimate, adjustment, recover_joint_slices left observedFactor, surrogateFactor, left atOutcome _]
  congr 1
  funext latent
  by_cases hs : target latent = 0
  · simp [adjustmentTerm, hs]
  · simp only [adjustmentTerm, ite_eq_right hs, chain latent hs]
    rw [Rat.mul_div_cancel (Rat.ne_of_gt (overlap latent hs))]

/-- A three-row proxy for two latent states. The outcome changes which of
the first two proxy levels is likeliest for each latent state. -/
def exampleProxy (outcome : Fin 2) : Matrix 3 2 :=
  fun w u => if w = 2 then 1 / 4 else if w.val = (outcome.val + u.val) % 2 then 1 / 2 else 1 / 4

def exampleInverse (outcome : Fin 2) : Matrix 2 3 :=
  fun u w => if w = 2 then 0 else if w.val = (outcome.val + u.val) % 2 then 8 / 3 else -4 / 3

theorem example_inverses (outcome : Fin 2) : Inverts (exampleProxy outcome) (exampleInverse outcome) := by
  intro v
  funext u
  have outcomes : outcome = 0 ∨ outcome = 1 := by omega
  have latents : u = 0 ∨ u = 1 := by omega
  rcases outcomes with rfl | rfl <;> rcases latents with rfl | rfl <;>
    simp only [multiply, sum, List.ofFn_succ, List.ofFn_zero, List.sum_cons, List.sum_nil] <;>
    simp [exampleInverse, exampleProxy] <;> grind

def exampleJoint (outcome : Fin 2) : Vector 2 :=
  fun u => if u = 1 then 0 else if outcome = 0 then 1 / 4 else 3 / 4

def exampleTarget : Vector 2 := fun u => if u = 0 then 1 else 0

/-- Correct inversion yields `Qx(0) = 1/4`. Inverting the already-marginalized
observed proxy with the queried slice produces a different denominator and
the value `1`. The second latent state has zero observed and target weights. -/
theorem outcome_varying_proxy_witness :
    let observed := fun outcome => multiply (exampleProxy outcome) (exampleJoint outcome)
    let surrogate := multiply (exampleProxy 0) exampleTarget
    estimate exampleInverse observed 0 surrogate = 1 / 4 ∧
      marginalizeOutcome exampleJoint 1 = 0 ∧ exampleTarget 1 = 0 ∧
      sum (fun latent => adjustmentTerm (recoverJoint exampleInverse observed 0 latent)
        (multiply (exampleInverse 0) (marginalizeOutcome observed) latent)
        (multiply (exampleInverse 0) surrogate latent)) = 1 := by
  decide +kernel

end

end OpenCausalScience.Papers.LeeBareinboim2021.OutcomeIndexedProxies
