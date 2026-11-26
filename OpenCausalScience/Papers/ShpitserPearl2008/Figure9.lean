module
public import OpenCausalScience.Papers.ShpitserPearl2008.CounterfactualDecision
public import OpenCausalScience.Papers.Pearl1995.RuleTwoGraph

/-! # Three worlds in Figures 9 and 11

Shpitser and Pearl (2008), Figures 9(a–c), 10 and 11. In the example
`P(Yₓ = y | X = x′, Z_d = z, D = d)`, the latent link `X ↔ Y`
shares one noise input. The other branches have separate noise inputs.
The `Z_d` merge uses `D = d` on the original evidence event.
https://www.jmlr.org/papers/volume9/shpitser08a/shpitser08a.pdf#page=17
-/

namespace OpenCausalScience.Papers.ShpitserPearl2008.Figure9

open TianPearl2003.AncestralMarginal (Setting evaluate mass sum_masses_of_partition)
open ParallelWorlds
open CounterfactualDecision (conditionalMass)
open Pearl1995.RuleTwoGraph (Law)

@[expose] public section

abbrev d : Fin 5 := 0
abbrev x : Fin 5 := 1
abbrev w : Fin 5 := 2
abbrev z : Fin 5 := 3
abbrev y : Fin 5 := 4

inductive World where
  | factual | setX | setD
  deriving DecidableEq, Repr

/-- The observed arrows are X → W → Y and D → Z → Y. The shared
noise of X and Y supplies the bidirected edge of its latent projection. -/
def graph : DAG 5 where
  edge u v := (u == x && v == w) || (u == d && v == z) ||
    (u == w && v == y) || (u == z && v == y)
  rank := Fin.val
  edge_increases := by decide +kernel

/-- `A` gives the noises for D and Z, `B` for W, and `C` for X and Y. -/
structure Equations (A B C : Type) where
  dValue : A → Bool
  xValue : C → Bool
  wValue : B → Bool → Bool
  zValue : A → Bool → Bool
  yValue : C → Bool → Bool → Bool

variable {A B C : Type}

abbrev Noise (A B C : Type) := A × (B × C)

def Equations.mechanism (model : Equations A B C) (unit : Noise A B C)
    (v : Fin 5) (parents : Fin 5 → Bool) : Bool :=
  if v = d then model.dValue unit.1
  else if v = x then model.xValue unit.2.2
  else if v = w then model.wValue unit.2.1 (parents x)
  else if v = z then model.zValue unit.1 (parents d)
  else model.yValue unit.2.2 (parents w) (parents z)

def settings (xSet dSet : Bool) : World → Setting 5
  | .factual => fun _ => none
  | .setX => fun v => if v = x then some xSet else none
  | .setD => fun v => if v = d then some dSet else none

abbrev value (model : Equations A B C) (xSet dSet : Bool) (unit : Noise A B C) :=
  response graph model.mechanism (settings xSet dSet) unit

private theorem d_response (model : Equations A B C) (xSet dSet : Bool)
    (unit : Noise A B C) (world : World) :
    value model xSet dSet unit (world, d) =
      if world = .setD then dSet else model.dValue unit.1 := by
  unfold value response
  rw [evaluate]
  cases world <;> rfl

private theorem x_response (model : Equations A B C) (xSet dSet : Bool)
    (unit : Noise A B C) (world : World) :
    value model xSet dSet unit (world, x) =
      if world = .setX then xSet else model.xValue unit.2.2 := by
  unfold value response
  rw [evaluate]
  cases world <;> rfl

private theorem w_response (model : Equations A B C) (xSet dSet : Bool)
    (unit : Noise A B C) (world : World) :
    value model xSet dSet unit (world, w) =
      model.wValue unit.2.1 (value model xSet dSet unit (world, x)) := by
  unfold value response
  conv => lhs; rw [evaluate]
  cases world <;> rfl

private theorem z_response (model : Equations A B C) (xSet dSet : Bool)
    (unit : Noise A B C) (world : World) :
    value model xSet dSet unit (world, z) =
      model.zValue unit.1 (value model xSet dSet unit (world, d)) := by
  unfold value response
  conv => lhs; rw [evaluate]
  cases world <;> rfl

private theorem y_response (model : Equations A B C) (xSet dSet : Bool)
    (unit : Noise A B C) (world : World) :
    value model xSet dSet unit (world, y) =
      model.yValue unit.2.2 (value model xSet dSet unit (world, w))
        (value model xSet dSet unit (world, z)) := by
  unfold value response
  conv => lhs; rw [evaluate]
  cases world <;> rfl

/-- The designated representatives after the three steps in Figure 11.
The constant nodes for the two interventions are retained separately. -/
def representatives (step : Nat) (copy : Copy World 5) : World :=
  match copy with
  | (.setX, v) =>
    if 1 ≤ step && v == d || 2 ≤ step && v == z then .factual else .setX
  | (.setD, v) =>
    if 1 ≤ step && v == x || 2 ≤ step && (v == w || v == z) || 3 ≤ step && v == y
    then .factual else .setD
  | (.factual, _) => .factual

/-- Verifies each merge stage pointwise on the observed event D = d. -/
theorem all_figure11_merges_valid (model : Equations A B C) (xSet dSet : Bool)
    (unit : Noise A B C) (observed : model.dValue unit.1 = dSet) (step : Nat) :
    ∀ copy, value model xSet dSet unit (representatives step copy, copy.2) =
      value model xSet dSet unit copy := by
  rintro ⟨world, vertex⟩
  have vertexIndex : vertex = d ∨ vertex = x ∨ vertex = w ∨ vertex = z ∨ vertex = y := by
    rcases vertex with ⟨i, bound⟩
    simp [d, x, w, z, y, Fin.ext_iff]
    omega
  rcases vertexIndex with rfl | rfl | rfl | rfl | rfl <;> cases world <;>
    simp [representatives, d, x, w, z, y] <;>
    try split <;>
    simp [d_response, x_response, w_response, z_response, y_response, observed]

/-- Figure 9(b)'s event after the original observation of D. -/
def originalQuery (xObs zObs yObs : Bool) : List (Atom World 5) :=
  [⟨(.setX, y), yObs⟩, ⟨(.factual, x), xObs⟩, ⟨(.setD, z), zObs⟩]

theorem figure9_relabels_query (xObs zObs yObs : Bool) :
    rename (representatives 3) (originalQuery xObs zObs yObs) =
      [⟨(.setX, y), yObs⟩, ⟨(.factual, x), xObs⟩, ⟨(.factual, z), zObs⟩] := rfl

theorem figure9_joint_mass_preserved (model : Equations A B C) (xSet dSet xObs zObs yObs : Bool)
    (units : List (Noise A B C)) (weight : Noise A B C → Rat) :
    mass units weight (fun unit => (model.dValue unit.1 == dSet) &&
      holds (value model xSet dSet unit) (originalQuery xObs zObs yObs)) =
    mass units weight (fun unit => (model.dValue unit.1 == dSet) &&
      holds (mergedResponse graph model.mechanism (settings xSet dSet) (representatives 3) unit)
        [⟨(.setX, y), yObs⟩, ⟨(.factual, x), xObs⟩, ⟨(.factual, z), zObs⟩]) := by
  rw [← figure9_relabels_query]
  exact merge_preserves_mass graph model.mechanism (settings xSet dSet) (representatives 3)
    units weight _ (fun unit h => all_figure11_merges_valid model xSet dSet unit (beq_iff_eq.mp h) 3)
    (originalQuery xObs zObs yObs)

/-- The original Figure 9(b) query uses D = d, Z_d = z, and factual X. -/
def evidence (model : Equations A B C) (xSet dSet xObs zObs : Bool)
    (unit : Noise A B C) : Bool :=
  (value model xSet dSet unit (.factual, d) == dSet) &&
    (value model xSet dSet unit (.setD, z) == zObs) &&
    (value model xSet dSet unit (.factual, x) == xObs)

/-- The single-world term `P_{z,w}(y,x′)` in the paper's ID* output. -/
def outcomeKernel (model : Equations A B C) (law : Law C)
    (zObs wObs yObs xObs : Bool) : Rat :=
  law.mass (fun c => (model.yValue c wObs zObs == yObs) && (model.xValue c == xObs))

/-- The one-variable intervention term `P_x(w)`. -/
def mediatorKernel (model : Equations A B C) (law : Law B) (xSet wObs : Bool) : Rat :=
  law.mass (fun b => model.wValue b xSet == wObs)

/-- The joint mass from the `ID*` call after both Figure 9(c) exchanges. -/
def reducedJoint (model : Equations A B C) (lawW : Law B) (lawXY : Law C)
    (xSet zObs xObs yObs : Bool) : Rat :=
  (lawW.product lawXY).mass (fun p =>
    (model.yValue p.2 (model.wValue p.1 xSet) zObs == yObs) && (model.xValue p.2 == xObs))

/-- ID* line 6 marginalizes W, whose two values separate the factors
from the two districts. In each summand, both factors are single-world. -/
theorem id_star_worked_joint (model : Equations A B C) (lawW : Law B) (lawXY : Law C)
    (xSet zObs xObs yObs : Bool) :
    reducedJoint model lawW lawXY xSet zObs xObs yObs =
      ([false, true].map fun wObs =>
        outcomeKernel model lawXY zObs wObs yObs xObs * mediatorKernel model lawW xSet wObs).sum := by
  let law := lawW.product lawXY
  let joint (p : B × C) :=
    (model.yValue p.2 (model.wValue p.1 xSet) zObs == yObs) && (model.xValue p.2 == xObs)
  let mediator (p : B × C) := model.wValue p.1 xSet
  have partition := sum_masses_of_partition [false, true] (by decide) law.atoms law.weight
    mediator (by intro p _; cases mediator p <;> simp) joint
  change law.mass joint = _
  change ([false, true].map fun wObs => law.mass (fun p => joint p && decide (mediator p = wObs))).sum =
    law.mass joint at partition
  rw [← partition]
  apply congrArg List.sum
  apply List.map_congr_left
  intro wObs _
  unfold outcomeKernel mediatorKernel
  rw [Rat.mul_comm, ← Law.mass_product]
  apply congrArg law.mass
  funext p
  dsimp only [joint, mediator]
  have boolEquality (a b : Bool) : decide (a = b) = (a == b) := by
    cases a <;> cases b <;> rfl
  rw [boolEquality]
  cases model.wValue p.1 xSet <;> cases wObs <;> simp

private theorem cancel_common {a b c : Rat} (hne : a ≠ 0) : (a * b) / (a * c) = b / c := by
  rw [Rat.div_def, Rat.inv_mul_rev]
  calc
    a * b * (c⁻¹ * a⁻¹) = (a * b * c⁻¹) * a⁻¹ := (Rat.mul_assoc _ _ _).symm
    _ = (a * (b * c⁻¹)) * a⁻¹ := by rw [Rat.mul_assoc a b c⁻¹]
    _ = a⁻¹ * (a * (b * c⁻¹)) := Rat.mul_comm _ _
    _ = (a⁻¹ * a) * (b * c⁻¹) := (Rat.mul_assoc _ _ _).symm
    _ = b / c := by
      have invert : a⁻¹ * a = 1 := by
        simpa [Rat.div_def, Rat.one_mul] using (Rat.div_mul_cancel (a := 1) hne)
      rw [invert, Rat.one_mul, Rat.div_def]

/-- The worked IDC* formula under original evidence support. The law
factors into mutually independent D/Z, W and X/Y noise blocks. -/
theorem idc_star_worked_formula (model : Equations A B C)
    (lawDZ : Law A) (lawW : Law B) (lawXY : Law C)
    (xSet dSet xObs zObs yObs : Bool)
    (supported : (lawDZ.product (lawW.product lawXY)).mass (evidence model xSet dSet xObs zObs) ≠ 0) :
    conditionalMass (lawDZ.product (lawW.product lawXY)).atoms
      (lawDZ.product (lawW.product lawXY)).weight
      (fun unit => value model xSet dSet unit (.setX, y) == yObs)
      (evidence model xSet dSet xObs zObs) =
      some ((([false, true].map fun wObs => outcomeKernel model lawXY zObs wObs yObs xObs *
        mediatorKernel model lawW xSet wObs).sum) / lawXY.mass (fun c => model.xValue c == xObs)) := by
  let law := lawDZ.product (lawW.product lawXY)
  let context (a : A) := (model.dValue a == dSet) && (model.zValue a dSet == zObs)
  let factual (p : B × C) := model.xValue p.2 == xObs
  let target (p : B × C) := model.yValue p.2 (model.wValue p.1 xSet) zObs == yObs
  have denominator : law.mass (evidence model xSet dSet xObs zObs) =
      lawDZ.mass context * lawXY.mass (fun c => model.xValue c == xObs) := by
    have factorization : law.mass (evidence model xSet dSet xObs zObs) =
        lawDZ.mass context * (lawW.product lawXY).mass factual := by
      rw [← Law.mass_product]
      apply congrArg law.mass
      funext unit
      simp [evidence, d_response, x_response, z_response, context, factual]
    have factualMass : (lawW.product lawXY).mass factual = lawXY.mass (fun c => model.xValue c == xObs) := by
      change (lawW.product lawXY).mass (fun p => true && (model.xValue p.2 == xObs)) = _
      rw [Law.mass_product lawW lawXY (fun _ => true) (fun c => model.xValue c == xObs),
        Law.mass_all, Rat.one_mul]
    rw [factorization, factualMass]
  have numerator : law.mass (fun unit => (value model xSet dSet unit (.setX, y) == yObs) &&
      evidence model xSet dSet xObs zObs unit) =
      lawDZ.mass context * reducedJoint model lawW lawXY xSet zObs xObs yObs := by
    change _ = lawDZ.mass context * (lawW.product lawXY).mass (fun p => target p && factual p)
    rw [← Law.mass_product]
    apply congrArg law.mass
    funext unit
    simp only [evidence, d_response, x_response, z_response, y_response, w_response,
      reduceCtorEq, ↓reduceIte, target, context, factual]
    cases obsD : (model.dValue unit.1 == dSet) <;> simp only [Bool.false_and, Bool.true_and,
      Bool.and_false]
    cases obsZ : (model.zValue unit.1 dSet == zObs) with
    | false => simp
    | true =>
      have matchedD := beq_iff_eq.mp obsD
      have matchedZ := beq_iff_eq.mp obsZ
      simp [matchedD, matchedZ]
  have contextSupported : lawDZ.mass context ≠ 0 := by
    intro absent
    exact supported (by rw [denominator, absent, Rat.zero_mul])
  change (if law.mass (evidence model xSet dSet xObs zObs) = 0 then none else _) = _
  rw [ite_eq_right supported]
  congr 1
  change law.mass (fun unit => (value model xSet dSet unit (.setX, y) == yObs) &&
      evidence model xSet dSet xObs zObs unit) / law.mass (evidence model xSet dSet xObs zObs) = _
  rw [numerator, denominator, cancel_common contextSupported, id_star_worked_joint]

end
end OpenCausalScience.Papers.ShpitserPearl2008.Figure9
