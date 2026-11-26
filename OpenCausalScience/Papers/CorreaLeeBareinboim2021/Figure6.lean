module
public import OpenCausalScience.Papers.CorreaLeeBareinboim2021.ConditionalNormalization

/-! # Conditional cancellation on Figure 6(a)

Correa, Lee and Bareinboim (2021), Figure 6(a) and equation (23).
The shared exogenous block for X and Z is independent of the
private response block for Y. On the cross-world evidence, fixing
X to x gives Y the parent inputs x and z. The same parent inputs
are present at the observational evidence X = x, Z = z.

Source: https://proceedings.neurips.cc/paper/2021/file/36bedb6eb7152f39b16328448942822b-Paper.pdf#page=9
-/

namespace OpenCausalScience.Papers.CorreaLeeBareinboim2021.Figure6

open TianPearl2003.AncestralMarginal (mass)
open ConditionalNormalization

@[expose] public section

variable {Ω Ξ : Type}

def productAtoms (first : List Ω) (second : List Ξ) : List (Ω × Ξ) :=
  first.flatMap (fun a => second.map (a, ·))

def productWeight (first : Ω → Rat) (second : Ξ → Rat) (atom : Ω × Ξ) : Rat :=
  first atom.1 * second atom.2

private theorem sum_scale (atoms : List Ξ) (f : Ξ → Rat) (scale : Rat) :
    (atoms.map fun a => scale * f a).sum = scale * (atoms.map f).sum := by
  induction atoms with
  | nil => simp [Rat.mul_zero]
  | cons _ _ ih => simp [ih, Rat.mul_add]

theorem product_event_mass (first : List Ω) (second : List Ξ)
    (firstWeight : Ω → Rat) (secondWeight : Ξ → Rat)
    (firstEvent : Ω → Bool) (secondEvent : Ξ → Bool) :
    mass (productAtoms first second) (productWeight firstWeight secondWeight)
      (fun atom => firstEvent atom.1 && secondEvent atom.2) =
    mass first firstWeight firstEvent * mass second secondWeight secondEvent := by
  induction first with
  | nil => simp [productAtoms, mass, Probability.FiniteMass.mass, Rat.zero_mul]
  | cons head rest ih =>
    simp only [productAtoms, List.flatMap_cons, mass, Probability.FiniteMass.mass, List.map_append,
      List.sum_append, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Rat.add_mul]
    congr 1
    rw [List.map_map, ← sum_scale]
    congr 1
    apply List.map_congr_left
    intro value _
    simp only [Function.comp_apply, productWeight]
    cases firstEvent head <;> cases secondEvent value <;> simp [Rat.zero_mul, Rat.mul_zero]

/-- Figure 6(a), with finite rational measures and independent roots
for the Y equation and the common X/Z block. -/
structure Model (Ω Ξ : Type) where
  xzAtoms : List Ω
  yAtoms : List Ξ
  xzWeight : Ω → Rat
  yWeight : Ξ → Rat
  yNormalized : mass yAtoms yWeight (fun _ => true) = 1
  x : Ω → Bool
  z : Bool → Ω → Bool
  y : Bool → Bool → Ξ → Bool

def Model.prob (m : Model Ω Ξ) : (Ω × Ξ → Bool) → Rat :=
  mass (productAtoms m.xzAtoms m.yAtoms) (productWeight m.xzWeight m.yWeight)

def Model.given (m : Model Ω Ξ) (event : Ω × Ξ → Bool) (evidence : Ω → Bool) : Option Rat :=
  conditionalOn (m.prob (fun unit => event unit && evidence unit.1))
    (m.prob (fun unit => evidence unit.1))

private theorem Model.conditional_of_private_response (m : Model Ω Ξ)
    (event : Ξ → Bool) (evidence : Ω → Bool) (supported : 0 < m.prob (fun unit => evidence unit.1)) :
    m.given (fun unit => event unit.2) evidence = some (mass m.yAtoms m.yWeight event) := by
  have denominator : m.prob (fun unit => evidence unit.1) =
      mass m.xzAtoms m.xzWeight evidence := by
    simpa only [Model.prob, Bool.and_true, m.yNormalized, Rat.mul_one] using
      (product_event_mass m.xzAtoms m.yAtoms m.xzWeight m.yWeight evidence (fun _ => true))
  have numerator := product_event_mass m.xzAtoms m.yAtoms m.xzWeight m.yWeight evidence event
  unfold Model.given
  rw [show m.prob (fun unit => event unit.2 && evidence unit.1) =
        mass m.xzAtoms m.xzWeight evidence * mass m.yAtoms m.yWeight event by
          simpa only [Model.prob, Bool.and_comm] using numerator]
  rw [← denominator, Rat.mul_comm (m.prob _)]
  let factor := m.prob (fun unit => evidence unit.1)
  change conditionalOn (mass m.yAtoms m.yWeight event * factor) factor = _
  calc
    _ = conditionalOn (mass m.yAtoms m.yWeight event * factor) (1 * factor) :=
      congrArg (conditionalOn _) (Rat.one_mul factor).symm
    _ = conditionalOn (mass m.yAtoms m.yWeight event) 1 :=
      conditional_on_common_factor _ _ _ (by decide) supported
    _ = _ := by
      have posOne : 0 < (1 : Rat) := by decide
      have invOne : (1 : Rat)⁻¹ = 1 := by
        simpa only [Rat.mul_one] using Rat.inv_mul_cancel 1 (Rat.ne_of_gt posOne)
      rw [conditionalOn, ite_eq_left posOne, Rat.div_def, invOne, Rat.mul_one]

theorem figure6a_eq_observational_conditional (m : Model Ω Ξ) (x xObserved z y : Bool)
    (crossSupport :
      0 < m.prob (fun unit => (m.z x unit.1 == z) && (m.x unit.1 == xObserved)))
    (obsSupport :
      0 < m.prob (fun unit => (m.x unit.1 == x) && (m.z (m.x unit.1) unit.1 == z))) :
    m.given (fun unit => m.y x (m.z x unit.1) unit.2 == y)
        (fun u => (m.z x u == z) && (m.x u == xObserved)) =
      m.given (fun unit => m.y (m.x unit.1) (m.z (m.x unit.1) unit.1) unit.2 == y)
        (fun u => (m.x u == x) && (m.z (m.x u) u == z)) := by
  have inCross : m.given (fun unit => m.y x (m.z x unit.1) unit.2 == y)
      (fun u => (m.z x u == z) && (m.x u == xObserved)) =
    m.given (fun unit => m.y x z unit.2 == y)
      (fun u => (m.z x u == z) && (m.x u == xObserved)) := by
    apply conditional_on_event_congr
    intro unit condition
    have sameZ := beq_iff_eq.mp (Bool.and_eq_true_iff.mp condition).1
    rw [sameZ]
  have inObs : m.given (fun unit => m.y (m.x unit.1) (m.z (m.x unit.1) unit.1) unit.2 == y)
      (fun u => (m.x u == x) && (m.z (m.x u) u == z)) =
    m.given (fun unit => m.y x z unit.2 == y)
      (fun u => (m.x u == x) && (m.z (m.x u) u == z)) := by
    apply conditional_on_event_congr
    intro unit condition
    obtain ⟨xEqual, zEqual⟩ := Bool.and_eq_true_iff.mp condition
    rw [beq_iff_eq.mp zEqual, beq_iff_eq.mp xEqual]
  have cross := m.conditional_of_private_response (fun u => m.y x z u == y)
    (fun u => (m.z x u == z) && (m.x u == xObserved)) crossSupport
  have obs := m.conditional_of_private_response (fun u => m.y x z u == y)
    (fun u => (m.x u == x) && (m.z (m.x u) u == z)) obsSupport
  rw [inCross, inObs, cross, obs]

end
end OpenCausalScience.Papers.CorreaLeeBareinboim2021.Figure6
