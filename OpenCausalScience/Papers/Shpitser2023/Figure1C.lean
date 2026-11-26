module
public import OpenCausalScience.Papers.TianPearl2003.IdentifyRecurrence

/-! # Applying the hedge criterion to the exact query

Ilya Shpitser, When does the ID algorithm fail?, arXiv:2307.03750v1,
Figure 1(b–c), Section 3 and Proposition 1. Both response models below
use the published graph's parent sets. They have equal strictly
positive observations and different results when only A₂ is set.
Their results agree when both A₁ and A₂ are set. The ratio printed
for the full query also gives the intervention in these two models.
Source: https://arxiv.org/pdf/2307.03750v1
-/

namespace OpenCausalScience.Papers.Shpitser2023.Figure1C

@[expose] public section

open TianPearl2003.IdentifyRecurrence

/-- The latent projection in Figure 1(c), with vertex order A₁, W, A₂, Y. -/
def markedEdge (u : Fin 4) (atU : Bool) (v : Fin 4) (atV : Bool) : Bool :=
  match u.val, v.val with
  | 0, 3 | 1, 0 | 2, 3 => !atU && atV
  | 3, 0 | 0, 1 | 3, 2 => atU && !atV
  | 1, 2 | 2, 1 | 1, 3 | 3, 1 => atU && atV
  | _, _ => false

def graph : MixedGraph 4 where
  edge := markedEdge
  symmetric := by decide +kernel
  loop_free := by decide +kernel
  no_arrow_of_undirected := by
    intro u v _ _ undirected
    have none : ∀ a b, markedEdge a false b false = false := by decide +kernel
    rw [none] at undirected
    contradiction

/-- The observations supply the c-factor on W, A₂, Y. The full query
requires just the factor on Y. The smaller intervention set requires
the joint factor on W, Y. -/
def sourceComponent : Vertices 4 := [1, 2, 3]

theorem full_query_trace :
    identifyPlan graph [3] 3 sourceComponent =
      [.marginalize [1, 2, 3] [2, 3], .extractFactor [2, 3] [3], .marginalize [3] [3]] := by
  rw [identifyPlan, show ancestors graph sourceComponent [3] = [2, 3] by decide +kernel]
  change .marginalize [1, 2, 3] [2, 3] :: .extractFactor [2, 3] [3] ::
    identifyPlan graph [3] 3 [3] = _
  rw [identifyPlan]
  decide +kernel

theorem strict_subquery_trace :
    identifyPlan graph [1, 3] 3 sourceComponent = [.ancestorFixedPoint [1, 2, 3]] := by
  rw [identifyPlan]
  decide +kernel

/-- The private noises of A₁ and Y are independent of the two shared
roots. The first root can enter W and Y, and the second W and A₂. -/
structure Noise where
  u₁ : Bool
  u₂ : Bool
  a₁ : Bool
  y : Bool

def atoms : List Noise :=
  [false, true].flatMap fun u₁ =>
    [false, true].flatMap fun u₂ =>
      [false, true].flatMap fun a₁ =>
        [false, true].map fun y => ⟨u₁, u₂, a₁, y⟩

def privateMass (bit : Bool) : Rat := if bit then 1/4 else 3/4

def mass (event : Noise → Bool) : Rat :=
  (atoms.map fun atom => if event atom then 1/4 * privateMass atom.a₁ * privateMass atom.y
    else 0).sum

/-- In the second model an allowed parent may be inactive. -/
def wValue (second : Bool) (atom : Noise) : Bool :=
  if second then atom.u₁ else Bool.xor atom.u₁ atom.u₂

def a₁Value (second : Bool) (atom : Noise) : Bool :=
  Bool.xor (wValue second atom) atom.a₁

def yValue (second : Bool) (a₁ a₂ : Bool) (atom : Noise) : Bool :=
  let signal := if second then atom.u₁ else Bool.xor atom.u₁ a₂
  Bool.xor (signal && a₁) atom.y

def observed (second w a₁ a₂ y : Bool) : Rat :=
  mass fun atom => (wValue second atom == w) && (a₁Value second atom == a₁) &&
    (atom.u₂ == a₂) && (yValue second a₁ a₂ atom == y)

def doBoth (second a₁ a₂ y : Bool) : Rat :=
  mass fun atom => yValue second a₁ a₂ atom == y

def doA₂ (second a₂ y : Bool) : Rat :=
  mass fun atom => yValue second (a₁Value second atom) a₂ atom == y

theorem noise_normalized : mass (fun _ => true) = 1 := by decide +kernel

theorem positive_observational_agreement (w a₁ a₂ y : Bool) :
    0 < observed false w a₁ a₂ y ∧ observed false w a₁ a₂ y = observed true w a₁ a₂ y := by
  cases w <;> cases a₁ <;> cases a₂ <;> cases y <;> decide +kernel

theorem strict_subquery_disagrees :
    doA₂ false false true = 3/8 ∧ doA₂ true false true = 7/16 := by decide +kernel

def weightedJoint (second a₁ a₂ y : Bool) : Rat :=
  ([false, true].map fun w =>
    let numerator := observed second w a₁ a₂ y
    let a₁AndW := mass fun atom => (wValue second atom == w) && (a₁Value second atom == a₁)
    let wMass := mass fun atom => wValue second atom == w
    numerator / a₁AndW * wMass).sum

/-- The paper prints C for the observed vertex labeled W in Figure 1(c). -/
def observationalFormula (second a₁ a₂ y : Bool) : Rat :=
  weightedJoint second a₁ a₂ y /
    (weightedJoint second a₁ a₂ false + weightedJoint second a₁ a₂ true)

theorem full_query_formula (second a₁ a₂ y : Bool) :
    observationalFormula second a₁ a₂ y = doBoth second a₁ a₂ y := by
  cases second <;> cases a₁ <;> cases a₂ <;> cases y <;> decide +kernel

theorem full_query_agrees (a₁ a₂ y : Bool) :
    doBoth false a₁ a₂ y = doBoth true a₁ a₂ y := by
  cases a₁ <;> cases a₂ <;> cases y <;> decide +kernel

end

end OpenCausalScience.Papers.Shpitser2023.Figure1C
