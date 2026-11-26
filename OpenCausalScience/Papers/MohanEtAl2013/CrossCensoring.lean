module
public import OpenCausalScience.Graph.DSeparation
public import OpenCausalScience.Papers.MohanEtAl2013.JointRecovery

/-! Mohan, Pearl and Tian (2013), Figure 3(b), Example 5 and Equation (5).
The numerical probabilities illustrate the published graph. -/

namespace OpenCausalScience.Papers.MohanEtAl2013.CrossCensoring

open JointRecovery (responseRatio response_ratio_eq)

@[expose] public section

/-- Vertices X, Y, R_X, R_Y in topological order. The proxy children
are deterministic and omitted from the published figure. -/
def graph : DAG 4 where
  edge u v := ([(0, 1), (0, 3), (1, 2)] : List (Fin 4 × Fin 4)).contains (u, v)
  rank v := v.val
  edge_increases := by decide

theorem figure3b_separations :
    graph.dSeparated 2 0 [1] = some true ∧
    graph.dSeparated 2 3 [1] = some true ∧
    graph.dSeparated 3 1 [0] = some true ∧
    graph.dSeparated 3 2 [0] = some true ∧
    graph.dSeparated 2 0 [] = some false ∧
    graph.dSeparated 3 1 [] = some false := by
  decide +kernel

/-- A binary factorization for the published cross-censoring graph.
The response functions give probabilities of observed values. -/
structure CrossLaw where
  target : Bool → Bool → Rat
  seeX : Bool → Rat
  seeY : Bool → Rat

def CrossLaw.observedY (m : CrossLaw) (x y : Bool) : Rat := m.seeY x * m.target x y
def CrossLaw.observedX (m : CrossLaw) (x y : Bool) : Rat := m.seeX y * m.target x y
def CrossLaw.complete (m : CrossLaw) (x y : Bool) : Rat := m.seeX y * m.observedY x y

def CrossLaw.xResponseGivenObservedY (m : CrossLaw) (y : Bool) : Rat :=
  (m.complete false y + m.complete true y) / (m.observedY false y + m.observedY true y)

def CrossLaw.yResponseGivenObservedX (m : CrossLaw) (x : Bool) : Rat :=
  (m.complete x false + m.complete x true) / (m.observedX x false + m.observedX x true)

def CrossLaw.recover (m : CrossLaw) (x y : Bool) : Rat :=
  m.complete x y / (m.xResponseGivenObservedY y * m.yResponseGivenObservedX x)

theorem recover_cross_censoring (m : CrossLaw) (x y : Bool)
    (ySupport : m.observedY false y + m.observedY true y ≠ 0)
    (xSupport : m.observedX x false + m.observedX x true ≠ 0)
    (seeX : m.seeX y ≠ 0) (seeY : m.seeY x ≠ 0) :
    m.recover x y = m.target x y := by
  have rx : m.xResponseGivenObservedY y = m.seeX y := by
    simpa [Rat.add_zero, CrossLaw.xResponseGivenObservedY, CrossLaw.complete, responseRatio] using
      response_ratio_eq [false, true] (m.observedY · y) (fun _ => m.seeX y) (m.seeX y)
        (by simp) (by simpa [Rat.add_zero] using ySupport)
  have ry : m.yResponseGivenObservedX x = m.seeY x := by
    have completeSwap (y' : Bool) : m.complete x y' = m.seeY x * m.observedX x y' := by
      simp [CrossLaw.complete, CrossLaw.observedX, CrossLaw.observedY,
        ← Rat.mul_assoc, Rat.mul_comm (m.seeX y') (m.seeY x)]
    simpa [Rat.add_zero, CrossLaw.yResponseGivenObservedX, completeSwap, responseRatio] using
      response_ratio_eq [false, true] (m.observedX x) (fun _ => m.seeY x) (m.seeY x)
        (by simp) (by simpa [Rat.add_zero] using xSupport)
  have both : m.seeX y * m.seeY x ≠ 0 := by
    intro h
    have canceled := Rat.mul_div_cancel (a := m.seeX y) seeY
    rw [h] at canceled
    exact seeX (by simpa [Rat.add_zero, Rat.div_def, Rat.zero_mul] using canceled.symm)
  rw [CrossLaw.recover, rx, ry, CrossLaw.complete, CrossLaw.observedY, ← Rat.mul_assoc,
    Rat.mul_comm (m.seeX y * m.seeY x), Rat.mul_div_cancel both]

def exampleLaw : CrossLaw where
  target
    | false, _ => 1/8
    | true, false => 1/4
    | true, true => 1/2
  seeX y := if y then 3/4 else 1/2
  seeY x := if x then 3/4 else 1/4

theorem example_recovered (x y : Bool) :
    exampleLaw.recover x y = exampleLaw.target x y := by
  cases x <;> cases y <;> decide +kernel

theorem example_complete_cases_biased :
    exampleLaw.complete false true / (exampleLaw.complete false false +
      exampleLaw.complete false true + exampleLaw.complete true false + exampleLaw.complete true true) ≠
      exampleLaw.target false true := by decide +kernel

end
end OpenCausalScience.Papers.MohanEtAl2013.CrossCensoring
