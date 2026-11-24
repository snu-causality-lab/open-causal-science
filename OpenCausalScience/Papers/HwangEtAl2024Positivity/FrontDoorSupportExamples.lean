module
public import Std
public import OpenCausalScience.Graph.DAG

/-!
# Hwang et al. (2024), Appendix D.2: supports in the back-door and front-door graph

[Hwang et al., corrected version](https://www.sanghacklee.me/ai-corrected/positivity_AI_corrected_2026-09-20.pdf),
the unofficial AI-corrected version dated 2026-09-20 of the ICML 2024 paper
([proceedings](https://proceedings.mlr.press/v235/hwang24a.html)). Appendix D.2,
pp. 20–21, with Fig. 2(b) and Fig. 7(d), the evaluation rules (a)–(c) of
Section 3, `adj` of Equation (2), and Equations (13) and (17)–(21).
The change table row "Appendix D.2" makes two revisions. The third formula
becomes `Σ_{w,z} P(z | x) P(y | z, w) P(w)`. The assertion that the backdoor
example makes direct `Q[{Y}]` evaluation fail is removed: in that example the
denominator of Equation (21) is positive at the target `x`, and the front-door
failure concerns another treatment value `x′`.

**Graph.** `figure2B` reads Fig. 2(b) as `W → X → Z → Y` and `W → Y`, with no
bidirected edge. This is the graph whose truncated factorization is
Equation (19) and whose c-components in Equation (20) are singletons. It
matches the caption of Fig. 7(d), an observed mediator and confounder.

**Models.** A `Figure2BModel` has one structural equation per vertex. Each
equation reads its parents in `figure2B` and a private exogenous coordinate.
The coordinates are independent with exact rational point masses. `prob` sums
atom weights over the solutions of a submodel, so `effect` and the `cFactor`
definitions are computed without any observational formula.

**Evaluation.** `fraction`, `addValues`, `mulValues` and `sumValues` implement
rules (a)–(c) on `Option Rat`, where `none` is an undefined value. Every
quotient in a formula is formed by `fraction`, which returns `none` for a zero
denominator. Lean's total-division convention `q / 0 = 0` appears only in
`front_door_only_total_division_is_not_c_factor`, which shows that this value
is not the causal one.

**Scope.** All results are exact calculations on two concrete models. No
theorem here is quantified over the models of Fig. 2(b). The source fixes only
some numbers and inequalities. Each model's docstring separates those from the
parameters chosen here.
-/

namespace OpenCausalScience.Papers.HwangEtAl2024Positivity.FrontDoorSupportExamples

@[expose] public section

/-! ## Partial values (Section 3, rules (a)–(c)) -/

/-- Rule (c). A fraction of probabilities, in particular a conditional
probability, is undefined when its denominator is zero. -/
def fraction (numerator denominator : Rat) : Option Rat :=
  if denominator = 0 then none else some (numerator / denominator)

/-- Rule (a). A sum with an undefined term is undefined. -/
def addValues : Option Rat → Option Rat → Option Rat
  | some a, some b => some (a + b)
  | some _, none => none
  | none, _ => none

/-- Rule (b). A product with an undefined factor is undefined unless the
other factor is zero. -/
def mulValues : Option Rat → Option Rat → Option Rat
  | some a, some b => some (a * b)
  | some a, none => if a = 0 then some 0 else none
  | none, some b => if b = 0 then some 0 else none
  | none, none => none

/-- A finite sum evaluated term by term with rule (a). -/
def sumValues {α : Type} (index : List α) (term : α → Option Rat) : Option Rat :=
  index.foldr (fun a total => addValues (term a) total) (some 0)

/-- `v > 0` for a partial value. A comparison with an undefined value fails. -/
def PositiveValue : Option Rat → Prop
  | some r => 0 < r
  | none => False

/-- `v = 0` for a partial value. A comparison with an undefined value fails. -/
def ZeroValue : Option Rat → Prop
  | some r => r = 0
  | none => False

instance instDecidablePositiveValue : (value : Option Rat) → Decidable (PositiveValue value)
  | some r => inferInstanceAs (Decidable (0 < r))
  | none => inferInstanceAs (Decidable False)

instance instDecidableZeroValue : (value : Option Rat) → Decidable (ZeroValue value)
  | some r => inferInstanceAs (Decidable (r = 0))
  | none => inferInstanceAs (Decidable False)

theorem fraction_eq_some_of_pos {numerator denominator : Rat} (positive : 0 < denominator) :
    fraction numerator denominator = some (numerator / denominator) := by
  simp [fraction, Rat.ne_of_gt positive]

theorem fraction_zero_denominator (numerator : Rat) : fraction numerator 0 = none := by
  simp [fraction]

theorem add_values_none_left (b : Option Rat) : addValues none b = none := rfl

theorem add_values_none_right (a : Option Rat) : addValues a none = none := by
  cases a <;> rfl

theorem mul_values_none_left {b : Rat} (nonzero : b ≠ 0) : mulValues none (some b) = none := by
  simp [mulValues, nonzero]

theorem mul_values_none_right {a : Rat} (nonzero : a ≠ 0) : mulValues (some a) none = none := by
  simp [mulValues, nonzero]

/-- One undefined summand makes the whole sum undefined. -/
theorem sum_values_eq_none {α : Type} {index : List α} {term : α → Option Rat} {a : α}
    (member : a ∈ index) (undefined : term a = none) : sumValues index term = none := by
  induction index with
  | nil => simp at member
  | cons b rest ih =>
    change addValues (term b) (sumValues rest term) = none
    rcases List.mem_cons.mp member with same | later
    · subst same
      rw [undefined]
      exact add_values_none_left _
    · rw [ih later]
      exact add_values_none_right _

/-! ## Fig. 2(b) and finite Markovian models on it -/

/-- Fig. 2(b), also Fig. 7(d), with vertices `W = 0`, `X = 1`, `Z = 2` and
`Y = 3`: arrows `W → X`, `X → Z`, `Z → Y` and `W → Y`. -/
def figure2B : DAG 4 where
  edge u v := (u.val == 0 && v.val == 1) || (u.val == 1 && v.val == 2) ||
    (u.val == 2 && v.val == 3) || (u.val == 0 && v.val == 3)
  rank u := u.val
  edge_increases := by decide

theorem figure2B_edges (u v : Fin 4) :
    figure2B.edge u v = true ↔
      (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 3) ∨ (u = 0 ∧ v = 3) := by
  revert u v
  decide

/-- Values of the observed variables `W`, `X`, `Z` and `Y`. -/
structure Assignment where
  w : Fin 3
  x : Bool
  z : Bool
  y : Bool

/-- One exogenous coordinate for each structural equation. -/
structure Exogenous where
  uW : Fin 3
  uX : Bool
  uZ : Bool
  uY : Bool
deriving DecidableEq

/-- Values of the ternary variable `W` and of its exogenous coordinate. -/
def wValues : List (Fin 3) := [0, 1, 2]

/-- Values of the binary variables and of the binary exogenous coordinates. -/
def boolValues : List Bool := [false, true]

/-- The exogenous assignments, each listed once. -/
def exogenousAtoms : List Exogenous :=
  wValues.flatMap fun a => boolValues.flatMap fun b => boolValues.flatMap fun c =>
    boolValues.map fun d => Exogenous.mk a b c d

theorem w_values_complete (w : Fin 3) : w ∈ wValues := by
  revert w
  decide

theorem bool_values_complete (b : Bool) : b ∈ boolValues := by
  cases b <;> decide

theorem exogenous_atoms_enumerate :
    exogenousAtoms.Nodup ∧ ∀ u : Exogenous, u ∈ exogenousAtoms := by
  refine ⟨by decide +kernel, ?_⟩
  intro ⟨a, b, c, d⟩
  cases b <;> cases c <;> cases d <;> revert a <;> decide +kernel

/-- A finite Markovian SCM on `figure2B`. `fW` has no observed input, `fX`
reads `W`, `fZ` reads `X`, and `fY` reads `Z` and `W`. Each equation also
reads its own exogenous coordinate. The coordinates are independent with
point masses `weightW`, `weightX`, `weightZ` and `weightY`. -/
structure Figure2BModel where
  fW : Fin 3 → Fin 3
  fX : Fin 3 → Bool → Bool
  fZ : Bool → Bool → Bool
  fY : Bool → Fin 3 → Bool → Bool
  weightW : Fin 3 → Rat
  weightX : Bool → Rat
  weightZ : Bool → Rat
  weightY : Bool → Rat

/-- Values fixed by `do(·)`. A variable left as `none` keeps its equation. -/
structure Intervention where
  w : Option (Fin 3)
  x : Option Bool
  z : Option Bool

def noIntervention : Intervention := ⟨none, none, none⟩

def setX (x : Bool) : Intervention := ⟨none, some x, none⟩

def setZ (z : Bool) : Intervention := ⟨none, none, some z⟩

def setWX (w : Fin 3) (x : Bool) : Intervention := ⟨some w, some x, none⟩

def setWXZ (w : Fin 3) (x z : Bool) : Intervention := ⟨some w, some x, some z⟩

/-- The product weight of an atom. The four coordinates are independent. -/
def Figure2BModel.weight (m : Figure2BModel) (u : Exogenous) : Rat :=
  m.weightW u.uW * m.weightX u.uX * m.weightZ u.uZ * m.weightY u.uY

/-- The solution of the submodel for `i` at one atom, in the order `W, X, Z, Y`. -/
def Figure2BModel.solve (m : Figure2BModel) (i : Intervention) (u : Exogenous) : Assignment :=
  let w := i.w.getD (m.fW u.uW)
  let x := i.x.getD (m.fX w u.uX)
  let z := i.z.getD (m.fZ x u.uZ)
  { w := w, x := x, z := z, y := m.fY z w u.uY }

/-- `P_i(event)`: the weight of the atoms whose solution under `do(i)` is in `event`. -/
def Figure2BModel.prob (m : Figure2BModel) (i : Intervention) (event : Assignment → Bool) : Rat :=
  (exogenousAtoms.map fun u => if event (m.solve i u) then m.weight u else 0).sum

/-- Each exogenous coordinate has a nonnegative law with total mass `1`, and so
does their product on `exogenousAtoms`. -/
def Figure2BModel.NormalizedLaw (m : Figure2BModel) : Prop :=
  (∀ a ∈ wValues, 0 ≤ m.weightW a) ∧ (wValues.map m.weightW).sum = 1 ∧
    (∀ b ∈ boolValues, 0 ≤ m.weightX b) ∧ (boolValues.map m.weightX).sum = 1 ∧
    (∀ b ∈ boolValues, 0 ≤ m.weightZ b) ∧ (boolValues.map m.weightZ).sum = 1 ∧
    (∀ b ∈ boolValues, 0 ≤ m.weightY b) ∧ (boolValues.map m.weightY).sum = 1 ∧
    (∀ u ∈ exogenousAtoms, 0 ≤ m.weight u) ∧ (exogenousAtoms.map m.weight).sum = 1

/-- The observational distribution `P(V)`. -/
def Figure2BModel.observed (m : Figure2BModel) (event : Assignment → Bool) : Rat :=
  m.prob noIntervention event

/-! ### Observational probabilities -/

def Figure2BModel.pW (m : Figure2BModel) (w : Fin 3) : Rat :=
  m.observed fun v => v.w == w

def Figure2BModel.pX (m : Figure2BModel) (x : Bool) : Rat :=
  m.observed fun v => v.x == x

def Figure2BModel.pXW (m : Figure2BModel) (x : Bool) (w : Fin 3) : Rat :=
  m.observed fun v => v.x == x && v.w == w

def Figure2BModel.pZX (m : Figure2BModel) (z x : Bool) : Rat :=
  m.observed fun v => v.z == z && v.x == x

def Figure2BModel.pZW (m : Figure2BModel) (z : Bool) (w : Fin 3) : Rat :=
  m.observed fun v => v.z == z && v.w == w

/-- `P(z, x, w)`, the denominator `Q[{Z, X, W}]` of Equation (21). -/
def Figure2BModel.pZXW (m : Figure2BModel) (z x : Bool) (w : Fin 3) : Rat :=
  m.observed fun v => v.z == z && v.x == x && v.w == w

def Figure2BModel.pYX (m : Figure2BModel) (y x : Bool) : Rat :=
  m.observed fun v => v.y == y && v.x == x

def Figure2BModel.pYXW (m : Figure2BModel) (y x : Bool) (w : Fin 3) : Rat :=
  m.observed fun v => v.y == y && v.x == x && v.w == w

def Figure2BModel.pYZX (m : Figure2BModel) (y z x : Bool) : Rat :=
  m.observed fun v => v.y == y && v.z == z && v.x == x

def Figure2BModel.pYZW (m : Figure2BModel) (y z : Bool) (w : Fin 3) : Rat :=
  m.observed fun v => v.y == y && v.z == z && v.w == w

/-- `P(y, z, x, w)`, the numerator `Q[{Y, Z, X, W}]` of Equation (21). -/
def Figure2BModel.pYZXW (m : Figure2BModel) (y z x : Bool) (w : Fin 3) : Rat :=
  m.observed fun v => v.y == y && v.z == z && v.x == x && v.w == w

/-! ### Conditional probabilities as partial values -/

/-- `P(x | w)`. -/
def Figure2BModel.conditionalXW (m : Figure2BModel) (x : Bool) (w : Fin 3) : Option Rat :=
  fraction (m.pXW x w) (m.pW w)

/-- `P(z | x)`. -/
def Figure2BModel.conditionalZX (m : Figure2BModel) (z x : Bool) : Option Rat :=
  fraction (m.pZX z x) (m.pX x)

/-- `P(y | x)`. -/
def Figure2BModel.conditionalYX (m : Figure2BModel) (y x : Bool) : Option Rat :=
  fraction (m.pYX y x) (m.pX x)

/-- `P(y | x, w)`. -/
def Figure2BModel.conditionalYXW (m : Figure2BModel) (y x : Bool) (w : Fin 3) : Option Rat :=
  fraction (m.pYXW y x w) (m.pXW x w)

/-- `P(y | x, z)`. -/
def Figure2BModel.conditionalYZX (m : Figure2BModel) (y z x : Bool) : Option Rat :=
  fraction (m.pYZX y z x) (m.pZX z x)

/-- `P(y | z, w)`. -/
def Figure2BModel.conditionalYZW (m : Figure2BModel) (y z : Bool) (w : Fin 3) : Option Rat :=
  fraction (m.pYZW y z w) (m.pZW z w)

/-! ### Interventional quantities computed in submodels -/

/-- `Pₓ(y)`, computed in the submodel whose equation for `X` is the constant `x`. -/
def Figure2BModel.effect (m : Figure2BModel) (x y : Bool) : Rat :=
  m.prob (setX x) fun v => v.y == y

/-- The c-factor `Q[{Z}](z; x) = Pₓ(z)`. -/
def Figure2BModel.cFactorZ (m : Figure2BModel) (x z : Bool) : Rat :=
  m.prob (setX x) fun v => v.z == z

/-- The c-factor `Q[{Y}](y; z, w) = P_{w,x,z}(y)`. Its value does not depend on `x`. -/
def Figure2BModel.cFactorY (m : Figure2BModel) (x y z : Bool) (w : Fin 3) : Rat :=
  m.prob (setWXZ w x z) fun v => v.y == y

/-- With `W` projected out, the c-factor `Q[{X, Y}](x′, y; z) = P_z(x′, y)`. -/
def Figure2BModel.cFactorXYWithoutW (m : Figure2BModel) (x' y z : Bool) : Rat :=
  m.prob (setZ z) fun v => v.x == x' && v.y == y

/-- With `Z` projected out, the c-factor `Q[{Y}](y; x, w) = P_{w,x}(y)`. -/
def Figure2BModel.cFactorYWithoutZ (m : Figure2BModel) (x y : Bool) (w : Fin 3) : Rat :=
  m.prob (setWX w x) fun v => v.y == y

/-! ### The formulas of Appendix D.2 -/

/-- Equation (17), the back-door formula `Σ_w P(y | x, w) P(w)`. -/
def Figure2BModel.backdoorFormula (m : Figure2BModel) (x y : Bool) : Option Rat :=
  sumValues wValues fun w => mulValues (m.conditionalYXW y x w) (some (m.pW w))

/-- The inner sum `Σ_{x′} P(y | x′, z) P(x′)` of Equation (18). It ranges over
every treatment value, not only the target. -/
def Figure2BModel.frontDoorInner (m : Figure2BModel) (y z : Bool) : Option Rat :=
  sumValues boolValues fun x' => mulValues (m.conditionalYZX y z x') (some (m.pX x'))

/-- Equation (18), the front-door formula `Σ_z P(z | x) Σ_{x′} P(y | x′, z) P(x′)`. -/
def Figure2BModel.frontDoorFormula (m : Figure2BModel) (x y : Bool) : Option Rat :=
  sumValues boolValues fun z => mulValues (m.conditionalZX z x) (m.frontDoorInner y z)

/-- Corrected Equation (19): `Σ_{w,z} P(z | x) P(y | z, w) P(w)`. -/
def Figure2BModel.identifyFormula (m : Figure2BModel) (x y : Bool) : Option Rat :=
  sumValues wValues fun w => sumValues boolValues fun z =>
    mulValues (mulValues (m.conditionalZX z x) (m.conditionalYZW y z w)) (some (m.pW w))

/-- `Σ_z P(z | x) P(y | z, w)` for one value `w`, without the average over `W`. -/
def Figure2BModel.fixedWExpression (m : Figure2BModel) (x y : Bool) (w : Fin 3) : Option Rat :=
  sumValues boolValues fun z => mulValues (m.conditionalZX z x) (m.conditionalYZW y z w)

/-- Equation (21), `Q[{Y}] = Q[{Y, Z, X, W}] / Q[{Z, X, W}]`, with `X` at `x`. -/
def Figure2BModel.equation21 (m : Figure2BModel) (x y z : Bool) (w : Fin 3) : Option Rat :=
  fraction (m.pYZXW y z x w) (m.pZXW z x w)

/-- Equation (20) with `Q[{Y}]` from Equation (21) and the other two factors
`Q[{W}] = P(w)` and `Q[{Z}] = P(z | x)` as in Equation (19). -/
def Figure2BModel.qDecompositionFormula (m : Figure2BModel) (x y : Bool) : Option Rat :=
  sumValues wValues fun w => sumValues boolValues fun z =>
    mulValues (mulValues (m.equation21 x y z w) (some (m.pW w))) (m.conditionalZX z x)

/-- With `W` projected out, `Q[{X, Y}] = (Q[{Y, Z, X}] / Q[{Z, X}]) (Q[{X}] / Q[∅])`,
where `Q[∅] = 1`. -/
def Figure2BModel.qXYWithoutW (m : Figure2BModel) (x' y z : Bool) : Option Rat :=
  mulValues (fraction (m.pYZX y z x') (m.pZX z x')) (fraction (m.pX x') 1)

/-- With `Z` projected out, `Q[{Y}] = Q[{Y, X, W}] / Q[{X, W}]`. -/
def Figure2BModel.qYWithoutZ (m : Figure2BModel) (x y : Bool) (w : Fin 3) : Option Rat :=
  fraction (m.pYXW y x w) (m.pXW x w)

/-! ### Positivity conditions -/

/-- `adj(x; W)` of Equation (2): `∀ w (P(w) = 0 ∨ P(x | w) > 0)`. -/
def Figure2BModel.AdjXW (m : Figure2BModel) (x : Bool) : Prop :=
  ∀ w ∈ wValues, m.pW w = 0 ∨ PositiveValue (m.conditionalXW x w)

/-- `adj(z; X)`: `∀ x′ (P(x′) = 0 ∨ P(z | x′) > 0)`. -/
def Figure2BModel.AdjZX (m : Figure2BModel) (z : Bool) : Prop :=
  ∀ x' ∈ boolValues, m.pX x' = 0 ∨ PositiveValue (m.conditionalZX z x')

/-- The condition of Equation (13) at one value `z`:
`P(z | x) = 0 ∨ ∀ x′ (P(y | x′, z) = 0 ∨ P(x′) = 0) ∨ (P(x) > 0 ∧ adj(z; X))`. -/
def Figure2BModel.FrontDoorCondition (m : Figure2BModel) (x y z : Bool) : Prop :=
  ZeroValue (m.conditionalZX z x) ∨
    (∀ x' ∈ boolValues, ZeroValue (m.conditionalYZX y z x') ∨ m.pX x' = 0) ∨
    (0 < m.pX x ∧ m.AdjZX z)

/-! ## Front-door but not backdoor (Appendix D.2, p. 20) -/

/-- The target treatment value `x`. The source does not name it; this module
uses `true`. -/
abbrev targetX : Bool := true

/-- "Front-door but not backdoor". Source-confirmed: binary `X` and `Z`,
ternary uniform `W`, `P(x | W = 0) = 0`, `P(x | W = w) > 0` for `w ∈ {1, 2}`,
and positive `P(Z | X)`. Chosen here: `x = true`; `X = false` if `W = 0` and
`X = U_X` otherwise, with `P(U_X = true) = 1/2`; `Z = X xor U_Z` with
`P(U_Z = true) = 1/4`; and `Y = U_Y` if `W = 0`, `Y = Z` otherwise, with
`P(U_Y = true) = 1/2`. The source does not specify the outcome equation. -/
def frontDoorOnlyModel : Figure2BModel where
  fW u := u
  fX w u := if w = 0 then false else u
  fZ x u := Bool.xor x u
  fY z w u := if w = 0 then u else z
  weightW _ := 1 / 3
  weightX _ := 1 / 2
  weightZ u := if u then 1 / 4 else 3 / 4
  weightY _ := 1 / 2

theorem front_door_only_normalized : frontDoorOnlyModel.NormalizedLaw := by
  unfold Figure2BModel.NormalizedLaw
  decide +kernel

/-- `W` is uniform on its three values. -/
theorem front_door_only_w_uniform (w : Fin 3) : frontDoorOnlyModel.pW w = 1 / 3 := by
  revert w
  decide +kernel

/-- `P(x | W = 0) = 0` with `P(W = 0) > 0`, and `P(x | W = w) > 0` for `w ∈ {1, 2}`. -/
theorem front_door_only_treatment_support :
    0 < frontDoorOnlyModel.pW 0 ∧ frontDoorOnlyModel.conditionalXW targetX 0 = some 0 ∧
      PositiveValue (frontDoorOnlyModel.conditionalXW targetX 1) ∧
      PositiveValue (frontDoorOnlyModel.conditionalXW targetX 2) := by
  decide +kernel

/-- `P(X, Z) > 0`, so every `P(z | x′)` is defined and positive. -/
theorem front_door_only_joint_support (x' z : Bool) :
    0 < frontDoorOnlyModel.pZX z x' ∧ 0 < frontDoorOnlyModel.pX x' ∧
      PositiveValue (frontDoorOnlyModel.conditionalZX z x') := by
  cases x' <;> cases z <;> decide +kernel

/-- Equation (13) holds through its last disjunct: `P(z | x) > 0 ∧ adj(z; X)`. -/
theorem front_door_only_front_door_condition (y z : Bool) :
    PositiveValue (frontDoorOnlyModel.conditionalZX z targetX) ∧ frontDoorOnlyModel.AdjZX z ∧
      frontDoorOnlyModel.FrontDoorCondition targetX y z := by
  unfold Figure2BModel.FrontDoorCondition Figure2BModel.AdjZX
  cases y <;> cases z <;> decide +kernel

/-- `adj(x; W)` fails at `W = 0`. -/
theorem front_door_only_backdoor_condition_fails : ¬ frontDoorOnlyModel.AdjXW targetX := by
  unfold Figure2BModel.AdjXW
  decide +kernel

/-- The term `P(y | x, W = 0)` of Equation (17) has denominator `P(x, W = 0) = 0`
and is multiplied by `P(W = 0) > 0`, so the back-door formula is undefined. -/
theorem front_door_only_backdoor_formula_undefined (y : Bool) :
    frontDoorOnlyModel.pXW targetX 0 = 0 ∧
      frontDoorOnlyModel.conditionalYXW y targetX 0 = none ∧
      frontDoorOnlyModel.backdoorFormula targetX y = none := by
  cases y <;> decide +kernel

/-- `Pₓ(y)` in the submodel `do(X = x)`. -/
theorem front_door_only_effect :
    frontDoorOnlyModel.effect targetX true = 2 / 3 ∧
      frontDoorOnlyModel.effect targetX false = 1 / 3 := by
  decide +kernel

/-- Equation (18) is defined and equals the interventional value. -/
theorem front_door_only_front_door_formula (y : Bool) :
    frontDoorOnlyModel.frontDoorFormula targetX y = some (frontDoorOnlyModel.effect targetX y) := by
  cases y <;> decide +kernel

/-- Corrected Equation (19) is defined and equals the interventional value. -/
theorem front_door_only_identify_formula (y : Bool) :
    frontDoorOnlyModel.identifyFormula targetX y = some (frontDoorOnlyModel.effect targetX y) := by
  cases y <;> decide +kernel

/-- Both conditional factors of Equation (19) have positive denominators and
equal the c-factors computed in the corresponding submodels. -/
theorem front_door_only_identify_factors (y z : Bool) (w : Fin 3) :
    0 < frontDoorOnlyModel.pX targetX ∧ 0 < frontDoorOnlyModel.pZW z w ∧
      frontDoorOnlyModel.conditionalZX z targetX = some (frontDoorOnlyModel.cFactorZ targetX z) ∧
      frontDoorOnlyModel.conditionalYZW y z w = some (frontDoorOnlyModel.cFactorY targetX y z w) := by
  cases y <;> cases z <;> revert w <;> decide +kernel

/-- The specific failure of Equation (21) at `X = x`, `W = 0`: the numerator and
the denominator `Q[{Z, X, W}](z, x, 0) = P(z, x, W = 0)` are both zero. -/
theorem front_door_only_equation21_zero_over_zero (y z : Bool) :
    frontDoorOnlyModel.pYZXW y z targetX 0 = 0 ∧ frontDoorOnlyModel.pZXW z targetX 0 = 0 ∧
      frontDoorOnlyModel.equation21 targetX y z 0 = none := by
  cases y <;> cases z <;> decide +kernel

/-- For `W ≠ 0` the denominator of Equation (21) at `x` is positive, and the
fraction equals the c-factor. Only the cell `W = 0` fails. -/
theorem front_door_only_equation21_other_cells (y z : Bool) :
    0 < frontDoorOnlyModel.pZXW z targetX 1 ∧ 0 < frontDoorOnlyModel.pZXW z targetX 2 ∧
      frontDoorOnlyModel.equation21 targetX y z 1 =
        some (frontDoorOnlyModel.cFactorY targetX y z 1) ∧
      frontDoorOnlyModel.equation21 targetX y z 2 =
        some (frontDoorOnlyModel.cFactorY targetX y z 2) := by
  cases y <;> cases z <;> decide +kernel

/-- Equation (20), with Equation (21) for `Q[{Y}]`, is undefined. -/
theorem front_door_only_q_decomposition_undefined (y : Bool) :
    frontDoorOnlyModel.qDecompositionFormula targetX y = none := by
  cases y <;> decide +kernel

/-- At the failing cell the c-factor itself is defined. Its value `1/2` is also
`P(y | z, W = 0)`, the factor used by Equation (19), whose denominator is positive. -/
theorem front_door_only_c_factor_at_missing_cell (y z : Bool) :
    frontDoorOnlyModel.cFactorY targetX y z 0 = 1 / 2 ∧ 0 < frontDoorOnlyModel.pZW z 0 ∧
      frontDoorOnlyModel.conditionalYZW y z 0 = some (1 / 2) := by
  cases y <;> cases z <;> decide +kernel

/-- Lean defines `0 / 0 = 0`. At the failing cell this quotient is `0`, while
the c-factor is `1/2`. The total-division value has no causal meaning. -/
theorem front_door_only_total_division_is_not_c_factor (y z : Bool) :
    frontDoorOnlyModel.pYZXW y z targetX 0 / frontDoorOnlyModel.pZXW z targetX 0 = 0 ∧
      frontDoorOnlyModel.cFactorY targetX y z 0 = 1 / 2 := by
  cases y <;> cases z <;> decide +kernel

/-- With `W` projected out, the expression for `Q[{X, Y}]` is defined for every
`x′` and equals the c-factor `P_z(x′, y)`. -/
theorem front_door_only_projected_c_factor (x' y z : Bool) :
    frontDoorOnlyModel.qXYWithoutW x' y z = some (frontDoorOnlyModel.cFactorXYWithoutW x' y z) := by
  cases x' <;> cases y <;> cases z <;> decide +kernel

/-- Without the average over `W`, the expression depends on `w` and never
equals `Pₓ(Y = true)` in this model. -/
theorem front_door_only_average_over_w_needed (w : Fin 3) :
    frontDoorOnlyModel.fixedWExpression targetX true w ≠
      some (frontDoorOnlyModel.effect targetX true) := by
  revert w
  decide +kernel

/-- `W` confounds `X` and `Y` in this model: `P(Y = true | x) = 3/4`, while
`Pₓ(Y = true) = 2/3`. -/
theorem front_door_only_confounded :
    frontDoorOnlyModel.conditionalYX true targetX = some (3 / 4) ∧
      frontDoorOnlyModel.effect targetX true = 2 / 3 := by
  decide +kernel

/-! ## Backdoor but not front-door (Appendix D.2, p. 21) -/

/-- The treatment value `x′ ≠ x` at which the mediator value `z′` is impossible. -/
abbrev otherX : Bool := false

/-- The mediator value `z′` with `P(z′ | x′) = 0`. -/
abbrev missingZ : Bool := true

/-- "Backdoor but not Front-door". Source-confirmed: `P(X, W) > 0`,
`P(Z | x) > 0`, and `P(z′ | x′) = 0` for some `x′ ≠ x`; the front-door
discussion uses `P(x′) > 0`, which here follows from `P(X, W) > 0`.
Chosen here: the domains and the uniform law of `W`, copied from the first
example, which the source says is designed similarly; `x = true`, `x′ = false`
and `z′ = true`; `X = U_X` if `W = 0` and `X = ¬U_X` otherwise, with
`P(U_X = true) = 1/4`; `Z = X ∧ U_Z` with `P(U_Z = true) = 2/3`; and the
outcome equation of `frontDoorOnlyModel`. -/
def backdoorOnlyModel : Figure2BModel where
  fW u := u
  fX w u := if w = 0 then u else !u
  fZ x u := x && u
  fY z w u := if w = 0 then u else z
  weightW _ := 1 / 3
  weightX u := if u then 1 / 4 else 3 / 4
  weightZ u := if u then 2 / 3 else 1 / 3
  weightY _ := 1 / 2

theorem backdoor_only_normalized : backdoorOnlyModel.NormalizedLaw := by
  unfold Figure2BModel.NormalizedLaw
  decide +kernel

/-- `P(X, W) > 0`. -/
theorem backdoor_only_treatment_support (x : Bool) (w : Fin 3) : 0 < backdoorOnlyModel.pXW x w := by
  cases x <;> revert w <;> decide +kernel

/-- `P(Z | x) > 0` at the target `x`. -/
theorem backdoor_only_mediator_support (z : Bool) :
    PositiveValue (backdoorOnlyModel.conditionalZX z targetX) := by
  cases z <;> decide +kernel

/-- `P(z′ | x′) = 0` is defined, since `P(x′) > 0`. -/
theorem backdoor_only_missing_mediator :
    otherX ≠ targetX ∧ 0 < backdoorOnlyModel.pX otherX ∧
      backdoorOnlyModel.conditionalZX missingZ otherX = some 0 := by
  decide +kernel

/-- `adj(x; W)` holds. -/
theorem backdoor_only_backdoor_condition : backdoorOnlyModel.AdjXW targetX := by
  unfold Figure2BModel.AdjXW
  decide +kernel

/-- `Pₓ(y)` in the submodel `do(X = x)`. -/
theorem backdoor_only_effect :
    backdoorOnlyModel.effect targetX true = 11 / 18 ∧
      backdoorOnlyModel.effect targetX false = 7 / 18 := by
  decide +kernel

/-- Equation (17) is defined and equals the interventional value. -/
theorem backdoor_only_backdoor_formula (y : Bool) :
    backdoorOnlyModel.backdoorFormula targetX y = some (backdoorOnlyModel.effect targetX y) := by
  cases y <;> decide +kernel

/-- The front-door failure. The factor `① = P(z′ | x)` is positive. The term
`P(y | x′, z′)` has denominator `P(x′, z′) = 0` and is multiplied by
`P(x′) > 0`, so `② = Σ_{x″} P(y | x″, z′) P(x″)` and Equation (18) are undefined. -/
theorem backdoor_only_front_door_failure (y : Bool) :
    backdoorOnlyModel.conditionalZX missingZ targetX = some (2 / 3) ∧
      backdoorOnlyModel.pZX missingZ otherX = 0 ∧ 0 < backdoorOnlyModel.pX otherX ∧
      backdoorOnlyModel.conditionalYZX y missingZ otherX = none ∧
      backdoorOnlyModel.frontDoorInner y missingZ = none ∧
      backdoorOnlyModel.frontDoorFormula targetX y = none := by
  cases y <;> decide +kernel

/-- Equation (13) fails at `z′`. -/
theorem backdoor_only_front_door_condition_fails (y : Bool) :
    ¬ backdoorOnlyModel.FrontDoorCondition targetX y missingZ := by
  unfold Figure2BModel.FrontDoorCondition Figure2BModel.AdjZX
  cases y <;> decide +kernel

/-- At the target `x`, the denominator of Equation (21) is
`P(z, x, w) = P(z | x) P(x, w) > 0` (stated without division), and the
fraction equals the c-factor `Q[{Y}]`. -/
theorem backdoor_only_equation21_at_target (y z : Bool) (w : Fin 3) :
    0 < backdoorOnlyModel.pZXW z targetX w ∧
      backdoorOnlyModel.pZXW z targetX w * backdoorOnlyModel.pX targetX =
        backdoorOnlyModel.pZX z targetX * backdoorOnlyModel.pXW targetX w ∧
      backdoorOnlyModel.equation21 targetX y z w = some (backdoorOnlyModel.cFactorY targetX y z w) := by
  cases y <;> cases z <;> revert w <;> decide +kernel

/-- At `x′` the denominator `P(z′, x′, w)` of Equation (21) is zero even though
`P(x′, w) > 0`. -/
theorem backdoor_only_equation21_at_other (y : Bool) (w : Fin 3) :
    backdoorOnlyModel.pZXW missingZ otherX w = 0 ∧ 0 < backdoorOnlyModel.pXW otherX w ∧
      backdoorOnlyModel.equation21 otherX y missingZ w = none := by
  cases y <;> revert w <;> decide +kernel

/-- Positivity at the target `x` against failure at `x′`. -/
theorem backdoor_only_target_versus_other :
    (∀ z ∈ boolValues, ∀ w ∈ wValues, 0 < backdoorOnlyModel.pZXW z targetX w) ∧
      (∀ z ∈ boolValues, PositiveValue (backdoorOnlyModel.conditionalZX z targetX)) ∧
      ZeroValue (backdoorOnlyModel.conditionalZX missingZ otherX) ∧
      (∀ w ∈ wValues, backdoorOnlyModel.pZXW missingZ otherX w = 0) := by
  decide +kernel

/-- Corrected Equation (19) is defined and equals the interventional value. -/
theorem backdoor_only_identify_formula (y : Bool) :
    backdoorOnlyModel.identifyFormula targetX y = some (backdoorOnlyModel.effect targetX y) := by
  cases y <;> decide +kernel

/-- Both conditional factors of Equation (19) have positive denominators and
equal the c-factors computed in the corresponding submodels. -/
theorem backdoor_only_identify_factors (y z : Bool) (w : Fin 3) :
    0 < backdoorOnlyModel.pX targetX ∧ 0 < backdoorOnlyModel.pZW z w ∧
      backdoorOnlyModel.conditionalZX z targetX = some (backdoorOnlyModel.cFactorZ targetX z) ∧
      backdoorOnlyModel.conditionalYZW y z w = some (backdoorOnlyModel.cFactorY targetX y z w) := by
  cases y <;> cases z <;> revert w <;> decide +kernel

/-- With `Z` projected out, the denominator `Q[{X, W}] = P(x, w)` is positive,
and the expression for `Q[{Y}]` equals the c-factor `P_{w,x}(y)`. -/
theorem backdoor_only_projected_c_factor (y : Bool) (w : Fin 3) :
    0 < backdoorOnlyModel.pXW targetX w ∧
      backdoorOnlyModel.qYWithoutZ targetX y w = some (backdoorOnlyModel.cFactorYWithoutZ targetX y w) := by
  cases y <;> revert w <;> decide +kernel

/-- `W` confounds `X` and `Y` in this model: `P(Y = true | x) = 9/14`, while
`Pₓ(Y = true) = 11/18`. -/
theorem backdoor_only_confounded :
    backdoorOnlyModel.conditionalYX true targetX = some (9 / 14) ∧
      backdoorOnlyModel.effect targetX true = 11 / 18 := by
  decide +kernel

end

end OpenCausalScience.Papers.HwangEtAl2024Positivity.FrontDoorSupportExamples
