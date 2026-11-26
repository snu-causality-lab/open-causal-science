module
public import OpenCausalScience.Graph.MixedSeparationExecutable
public import OpenCausalScience.Papers.TianPearl2003.AncestralMarginal
public import OpenCausalScience.Papers.BareinboimTian2015.RC

/-! # Figure 3(c–d): identification and selection after intervention

Bareinboim and Tian (AAAI 2015), Figure 3(c–d). Cutting arrowheads
into X makes Y independent of selection in the intervention graph.
Two strictly positive finite models can still share the selected law
and differ on the population effect. Y is unaffected by the treatment
on every unit in both models.

Source: https://ojs.aaai.org/index.php/AAAI/article/download/9679/9538#page=5
-/

namespace OpenCausalScience.Papers.BareinboimTian2015.Figure3

open TianPearl2003.AncestralMarginal RC

@[expose] public section

abbrev x : Fin 3 := 0
abbrev y : Fin 3 := 1
abbrev s : Fin 3 := 2

def edge (natural : Bool) (u : Fin 3) (atU : Bool) (v : Fin 3) (atV : Bool) : Bool :=
  match atU, atV with
  | false, true => u == x && v == s
  | true, false => v == x && u == s
  | true, true => natural && ((u == x && v == y) || (u == y && v == x))
  | false, false => false

def graph (natural : Bool) : MixedGraph 3 where
  edge := edge natural
  symmetric := by cases natural <;> decide +kernel
  loop_free := by cases natural <;> decide +kernel
  no_arrow_of_undirected := by
    intro u v w mark bad
    change false = true at bad
    contradiction

theorem intervention_removes_incoming_x {u v : Fin 3} {a b : Bool} :
    (graph false).edge u a v b =
      ((graph true).edge u a v b && !(u == x && a) && !(v == x && b)) := by
  have all : ∀ u v : Fin 3, ∀ a b,
      (graph false).edge u a v b =
        ((graph true).edge u a v b && !(u == x && a) && !(v == x && b)) := by decide +kernel
  exact all u v a b

theorem intervention_separates_selection :
    (graph false).mSeparated (· == y) (· == s) (· == x) = true := by
  apply ((graph false).m_separated_iff_no_walk _ _ _).mpr
  rintro ⟨first, _, ⟨v, mark, isY, incident⟩, _, _⟩
  obtain rfl : v = y := beq_iff_eq.mp isY
  have isolated : ∀ (v : Fin 3) (a b : Bool), (graph false).edge y a v b = false := by
    decide +kernel
  rw [isolated first.1 mark first.2] at incident
  contradiction

theorem rc_blocks :
    plan (graph true) s y [y] [x, y, s] = .blocked [x, y, s] := by
  rw [plan]
  decide +kernel

/-- Each unit records the common root's two responses and an independent
equiprobable selection draw. Neither S nor Y affects the treatment equation. -/
abbrev Unit := Bool × Bool × Fin 8

def units : List Unit :=
  [false, true].flatMap fun x => [false, true].flatMap fun y =>
    (List.finRange 8).map (fun draw => (x, y, draw))

def populationX (second : Bool) : Rat := if second then 2 / 3 else 1 / 2

def noiseWeight (second : Bool) (unit : Unit) : Rat :=
  let px := if unit.1 then populationX second else 1 - populationX second
  let yAgrees := if unit.1 == unit.2.1 then (3 / 4 : Rat) else 1 / 4
  px * yAgrees / 8

def treatment (intervention : Option Bool) (unit : Unit) : Bool :=
  intervention.getD unit.1

def outcome (unit : Unit) : Bool := unit.2.1

def threshold (second treatmentValue : Bool) : Nat :=
  if second then (if treatmentValue then 3 else 6) else 4

def selection (second : Bool) (intervention : Option Bool) (unit : Unit) : Bool :=
  decide (unit.2.2.val < threshold second (treatment intervention unit))

def jointCell (second : Bool) (tx ty selected : Bool) : Rat :=
  mass units (noiseWeight second) (fun unit =>
    (treatment none unit == tx) && (outcome unit == ty) && (selection second none unit == selected))

def selectedRate (second : Bool) : Rat :=
  mass units (noiseWeight second) (selection second none)

def selectedCell (second : Bool) (tx ty : Bool) : Rat :=
  jointCell second tx ty true / selectedRate second

def interventionRisk (second : Bool) (action : Bool) : Rat :=
  mass units (noiseWeight second) (fun unit => treatment (some action) unit == action && outcome unit)

/-- Both models have positive population joint cells at either value of S.
In particular both are in the positive selected-law domain of RC. -/
theorem positive_observational_cells (second tx ty selected : Bool) :
    0 < jointCell second tx ty selected := by
  cases second <;> cases tx <;> cases ty <;> cases selected <;> decide +kernel

theorem normalized_laws (second : Bool) :
    mass units (noiseWeight second) (fun _ => true) = 1 := by
  cases second <;> decide +kernel

theorem same_selection_rates (second : Bool) : selectedRate second = 1 / 2 := by
  cases second <;> decide +kernel

theorem equal_selected_laws (tx ty : Bool) :
    selectedCell false tx ty = selectedCell true tx ty := by
  cases tx <;> cases ty <;> decide +kernel

theorem different_population_risks (action : Bool) :
    interventionRisk false action = 1 / 2 ∧ interventionRisk true action = 7 / 12 := by
  cases action <;> decide +kernel

end
end OpenCausalScience.Papers.BareinboimTian2015.Figure3
