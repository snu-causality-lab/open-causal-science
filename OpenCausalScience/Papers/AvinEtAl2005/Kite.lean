module
public import OpenCausalScience.Papers.TianPearl2003.DistrictProduct

/-! # The recanting witness in the kite graph

Avin, Shpitser, and Pearl (2005), Table 1, Figure 5(a), Lemma 2 and
Theorem 3. We keep the two response tables for R and instantiate the
common downstream mechanisms of the proof with positive rational
channels. The structural parents are Z → R, R → V, R → Y and V → Y.
The path-specific response sets Z to its active value along Z → R → V → Y
and its baseline value along Z → R → Y.
Source: https://ijcai.org/proceedings/2005/100
-/

namespace OpenCausalScience.Papers.AvinEtAl2005.Kite

open TianPearl2003.DistrictProduct

@[expose] public section

abbrev Outcome := Bool × Bool

structure Values where
  z : Bool
  r : Bool
  v : Bool
  y : Outcome
  deriving DecidableEq

structure Actions where
  z : Option Bool := none
  r : Option Bool := none
  v : Option Bool := none
  y : Option Outcome := none

/-- Independent noises for the four structural equations. The two Y
bits have separate private noise with the same flip probability. -/
structure Noise where
  z : Bool
  r : Fin 3
  v : Bool
  yLeft : Bool
  yRight : Bool

/-- The two deterministic R responses in Table 1. Its noise states 1,
2 and 3 are represented by indices 0, 1 and 2. -/
def rResponse (second z : Bool) (noise : Fin 3) : Bool :=
  if z then noise == 0 else
    if second then noise != 2 else noise != 0

def vResponse (r noise : Bool) : Bool := Bool.xor r noise

def yResponse (r v yLeft yRight : Bool) : Outcome :=
  (Bool.xor r yLeft, Bool.xor v yRight)

def evaluate (second : Bool) (doSet : Actions) (noise : Noise) : Values :=
  let z := doSet.z.getD noise.z
  let r := doSet.r.getD (rResponse second z noise.r)
  let v := doSet.v.getD (vResponse r noise.v)
  let y := doSet.y.getD (yResponse r v noise.yLeft noise.yRight)
  ⟨z, r, v, y⟩

/-- A complete output cell is the intersection of its four local noise
constraints, with parent values read from that cell. Each constraint
uses only the primitive noise of its own vertex. -/
theorem evaluate_eq_iff (second : Bool) (doSet : Actions) (noise : Noise) (cell : Values) :
    evaluate second doSet noise = cell ↔
      doSet.z.getD noise.z = cell.z ∧
      doSet.r.getD (rResponse second cell.z noise.r) = cell.r ∧
      doSet.v.getD (vResponse cell.r noise.v) = cell.v ∧
      doSet.y.getD (yResponse cell.r cell.v noise.yLeft noise.yRight) = cell.y := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, rfl, rfl⟩
  · obtain ⟨z, r, v, y⟩ := cell
    rintro ⟨hz, hr, hv, hy⟩
    dsimp at hz hr hv hy
    simp only [evaluate, hz, hr, hv, hy]

def rMass (second z r : Bool) : Rat :=
  ((List.finRange 3).map fun u => if rResponse second z u == r then (1/3 : Rat) else 0).sum

def flipMass (parent value : Bool) : Rat := if parent == value then 3/4 else 1/4

def yMass (r v : Bool) (y : Outcome) : Rat := flipMass r y.1 * flipMass v y.2

def assignedMass {α : Type} [DecidableEq α] (setting : Option α) (value : α)
    (unclamped : Rat) : Rat :=
  match setting with
  | none => unclamped
  | some fixed => if fixed = value then 1 else 0

/-- Product of the local constraint probabilities in `evaluate_eq_iff`.
Z is uniform, U_R is uniform, and each downstream bit flips its parent
with probability 1/4. Intervened-on equations impose point masses. -/
def regimeCell (second : Bool) (doSet : Actions) (cell : Values) : Rat :=
  assignedMass doSet.z cell.z (1/2) *
  assignedMass doSet.r cell.r (rMass second cell.z cell.r) *
  assignedMass doSet.v cell.v (flipMass cell.r cell.v) *
  assignedMass doSet.y cell.y (yMass cell.r cell.v cell.y)

def indicator (b : Bool) : Rat := if b then 1 else 0

def flipNoise (b : Bool) : Rat := if b then 1/4 else 3/4

theorem flip_mass_is_response_mass (parent value : Bool) :
    flipMass parent value =
      ([false, true].map fun u => if vResponse parent u == value then flipNoise u else 0).sum := by
  cases parent <;> cases value <;> decide +kernel

/-- We encode all primitive noise values using one four-element type.
Only the first two atoms are used for each Boolean root, and the
first three for R. The four Y atoms encode its two private bits. -/
def bitAtom (u : Fin 4) : Bool := u.val % 2 == 1

def rAtom (u : Fin 4) : Fin 3 := ⟨u.val % 3, Nat.mod_lt _ (by decide)⟩

def outcomeAtom (u : Fin 4) : Outcome := (2 ≤ u.val, bitAtom u)

def zBlock (setting : Option Bool) (z : Bool) : RootBlock (Fin 4) where
  atoms := [0, 1]
  weight _ := 1/2
  cellLikelihood u := indicator (setting.getD (bitAtom u) == z)
  nonnegative := by decide +kernel
  normalized := by decide +kernel

def rBlock (second z : Bool) (setting : Option Bool) (r : Bool) : RootBlock (Fin 4) where
  atoms := [0, 1, 2]
  weight _ := 1/3
  cellLikelihood u := indicator (setting.getD (rResponse second z (rAtom u)) == r)
  nonnegative := by decide +kernel
  normalized := by decide +kernel

def vBlock (r : Bool) (setting : Option Bool) (v : Bool) : RootBlock (Fin 4) where
  atoms := [0, 1]
  weight u := flipNoise (bitAtom u)
  cellLikelihood u := indicator (setting.getD (vResponse r (bitAtom u)) == v)
  nonnegative := by decide +kernel
  normalized := by decide +kernel

def yBlock (r v : Bool) (setting : Option Outcome) (y : Outcome) : RootBlock (Fin 4) where
  atoms := List.finRange 4
  weight u := flipNoise (outcomeAtom u).1 * flipNoise (outcomeAtom u).2
  cellLikelihood u := indicator (setting.getD (yResponse r v (outcomeAtom u).1 (outcomeAtom u).2) == y)
  nonnegative := by decide +kernel
  normalized := by decide +kernel

private theorem z_factor (setting : Option Bool) (z : Bool) :
    (zBlock setting z).factor = assignedMass setting z (1/2) := by
  cases setting with
  | none => cases z <;> decide +kernel
  | some fixed => cases fixed <;> cases z <;> decide +kernel

private theorem r_factor (second z : Bool) (setting : Option Bool) (r : Bool) :
    (rBlock second z setting r).factor = assignedMass setting r (rMass second z r) := by
  cases setting with
  | none => cases second <;> cases z <;> cases r <;> decide +kernel
  | some fixed => cases fixed <;> cases second <;> cases z <;> cases r <;> decide +kernel

private theorem v_factor (r : Bool) (setting : Option Bool) (v : Bool) :
    (vBlock r setting v).factor = assignedMass setting v (flipMass r v) := by
  cases setting with
  | none => cases r <;> cases v <;> decide +kernel
  | some fixed => cases fixed <;> cases r <;> cases v <;> decide +kernel

private theorem y_factor (r v : Bool) (setting : Option Outcome) (y : Outcome) :
    (yBlock r v setting y).factor = assignedMass setting y (yMass r v y) := by
  obtain ⟨left, right⟩ := y
  cases setting with
  | none => cases r <;> cases v <;> cases left <;> cases right <;> decide +kernel
  | some fixed =>
    obtain ⟨a, b⟩ := fixed
    cases a <;> cases b <;> cases r <;> cases v <;> cases left <;> cases right <;> decide +kernel

/-- Direct Cartesian summation over the independent primitive roots,
with local likelihoods taken from `evaluate_eq_iff`. -/
def interventionalMass (second : Bool) (doSet : Actions) (cell : Values) : Rat :=
  jointMass [zBlock doSet.z cell.z, rBlock second cell.z doSet.r cell.r,
    vBlock cell.r doSet.v cell.v, yBlock cell.r cell.v doSet.y cell.y]

theorem regime_factorization (second : Bool) (doSet : Actions) (cell : Values) :
    interventionalMass second doSet cell = regimeCell second doSet cell := by
  rw [interventionalMass, joint_mass_eq_product_factors]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, z_factor, r_factor,
    v_factor, y_factor, Rat.mul_one, regimeCell, Rat.mul_assoc]

theorem r_response_marginals_agree (z r : Bool) : rMass false z r = rMass true z r := by
  cases z <;> cases r <;> decide +kernel

/-- Includes observational agreement by taking every action to be `none`.
Equality of complete cells also gives equality of all random margins. -/
theorem all_interventional_cells_agree (doSet : Actions) (cell : Values) :
    regimeCell false doSet cell = regimeCell true doSet cell := by
  rw [regimeCell, regimeCell, r_response_marginals_agree]

theorem observational_cells_positive (second : Bool) (cell : Values) :
    0 < regimeCell second {} cell := by
  obtain ⟨z, r, v, a, b⟩ := cell
  cases second <;> cases z <;> cases r <;> cases v <;> cases a <;> cases b <;> decide +kernel

/-- The same private R noise is used in both copies of R. -/
def crossWorldR (second zBaseline zActive rBaseline rActive : Bool) : Rat :=
  ((List.finRange 3).map fun u =>
    if (rResponse second zBaseline u == rBaseline) && (rResponse second zActive u == rActive)
    then (1/3 : Rat) else 0).sum

theorem cross_world_responses_disagree :
    crossWorldR false false true true true = 0 ∧
      crossWorldR true false true true true = 1/3 := by decide +kernel

/-- The two routes from Z to Y feed different copies of R to the two
inputs of Y. The route through V carries the active treatment value. -/
def pathResponse (second zBaseline zActive : Bool) (noise : Noise) : Outcome :=
  let rBaseline := rResponse second zBaseline noise.r
  let v := vResponse (rResponse second zActive noise.r) noise.v
  yResponse rBaseline v noise.yLeft noise.yRight

/-- Probability of the path response using the same summation as
Theorem 3, over the R pair and the intermediate response of V. -/
def pathCell (second zBaseline zActive : Bool) (y : Outcome) : Rat :=
  let bits := [false, true]
  (bits.flatMap fun rBaseline => bits.flatMap fun rActive => bits.map fun v =>
    crossWorldR second zBaseline zActive rBaseline rActive * flipMass rActive v *
      yMass rBaseline v y).sum

/-- Direct summation over the independent primitive responses for the
path counterfactual. The treatment's natural root does not enter it. -/
def pathResponseMass (second zBaseline zActive : Bool) (y : Outcome) : Rat :=
  let bits := [false, true]
  ((List.finRange 3).flatMap fun uR => bits.flatMap fun uV => bits.flatMap fun uYLeft =>
    bits.map fun uYRight =>
      if pathResponse second zBaseline zActive ⟨false, uR, uV, uYLeft, uYRight⟩ == y
      then (1/3 : Rat) * flipNoise uV * flipNoise uYLeft * flipNoise uYRight else 0).sum

theorem path_formula_matches_structural_response (second zBaseline zActive : Bool) (y : Outcome) :
    pathCell second zBaseline zActive y = pathResponseMass second zBaseline zActive y := by
  obtain ⟨left, right⟩ := y
  cases second <;> cases zBaseline <;> cases zActive <;> cases left <;> cases right <;> decide +kernel

theorem path_specific_cells_disagree :
    pathCell false false true (true, true) = 23/96 ∧
      pathCell true false true (true, true) = 9/32 := by decide +kernel

theorem figure5a_nonidentification :
    (∀ doSet cell, interventionalMass false doSet cell = interventionalMass true doSet cell) ∧
      pathResponseMass false false true (true, true) ≠ pathResponseMass true false true (true, true) := by
  constructor
  · intro doSet cell
    rw [regime_factorization, regime_factorization, all_interventional_cells_agree]
  · rw [← path_formula_matches_structural_response, ← path_formula_matches_structural_response]
    decide +kernel

end
end OpenCausalScience.Papers.AvinEtAl2005.Kite
