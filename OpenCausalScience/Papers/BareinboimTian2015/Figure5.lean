module
public import OpenCausalScience.Papers.BareinboimTian2015.KernelIdentities

/-! # Three selected-only RC traces from Figure 5

Bareinboim and Tian (AAAI 2015), Figure 5(a–c), effects of X on Y.
The same target district {Y} exercises stopping, calling Identify,
and removing a clean district before ancestral restriction.

Source: https://ojs.aaai.org/index.php/AAAI/article/download/9679/9538#page=6
-/

namespace OpenCausalScience.Papers.BareinboimTian2015.Figure5

open TianPearl2003.IdentifyRecurrence RC

@[expose] public section

abbrev w1 : Fin 6 := 0
abbrev w2 : Fin 6 := 1
abbrev w3 : Fin 6 := 2
abbrev x : Fin 6 := 3
abbrev y : Fin 6 := 4
abbrev s : Fin 6 := 5

inductive Panel where
  | a | b | c
  deriving DecidableEq

def directed (panel : Panel) (u v : Fin 6) : Bool :=
  let common := (u == w2 && v == x) || (u == x && v == y)
  common || match panel with
  | .a => (u == w1 && v == w2) || (u == w2 && v == s)
  | .b => (u == w1 && v == w2) || (u == w3 && v == s)
  | .c => (u == w1 && v == x) || (u == w2 && v == s)

def bidirected (panel : Panel) (u v : Fin 6) : Bool :=
  let listed := fun a b => match panel with
    | .a => (a == w1 && b == x) || (a == w1 && b == y)
    | .b => (a == w1 && b == x) || (a == w1 && b == y) || (a == w2 && b == w3)
    | .c => (a == w1 && b == w2) || (a == w1 && b == y)
  listed u v || listed v u

def edge (panel : Panel) (u : Fin 6) (atU : Bool) (v : Fin 6) (atV : Bool) : Bool :=
  match atU, atV with
  | false, true => directed panel u v
  | true, false => directed panel v u
  | true, true => bidirected panel u v
  | false, false => false

def graph (panel : Panel) : MixedGraph 6 where
  edge := edge panel
  symmetric := by cases panel <;> decide +kernel
  loop_free := by cases panel <;> decide +kernel
  no_arrow_of_undirected := by
    intro u v w mark bad
    change false = true at bad
    contradiction

def current (panel : Panel) : Vertices 6 :=
  match panel with
  | .a | .c => [w1, w2, x, y, s]
  | .b => [w1, w2, w3, x, y, s]

theorem only_y_is_relevant_after_intervening (panel : Panel) :
    ancestors (graph panel) ((current panel).filter (fun v => v != x && v != s)) [y] = [y] := by
  cases panel <;> decide +kernel

theorem panel_a_blocks :
    plan (graph .a) s y [y] (current .a) = .blocked (current .a) := by
  rw [plan]
  decide +kernel

theorem panel_b_recovers_from_clean_district :
    plan (graph .b) s y [y] (current .b) =
      .identify (current .b) [w1, x, y]
        [.marginalize [w1, x, y] [x, y], .extractFactor [x, y] [y], .marginalize [y] [y]] := by
  have first :
      plan (graph .b) s y [y] (current .b) =
        .identify (current .b) [w1, x, y] (identifyPlan (graph .b) [y] y [w1, x, y]) := by
    rw [plan]
    decide +kernel
  have ordinary :
      identifyPlan (graph .b) [y] y [w1, x, y] =
        .marginalize [w1, x, y] [x, y] :: .extractFactor [x, y] [y] ::
          identifyPlan (graph .b) [y] y [y] := by
    rw [identifyPlan]
    decide +kernel
  rw [first]
  have finish : identifyPlan (graph .b) [y] y [y] = [.marginalize [y] [y]] := by
    rw [identifyPlan]
    decide +kernel
  rw [ordinary, finish]

theorem panel_c_recovers_after_division_and_pruning :
    plan (graph .c) s y [y] (current .c) =
      .peel (current .c) [[x]] [w1, w2, y, s]
        (.restrict [w1, w2, y, s] [w2, y, s]
          (.identify [w2, y, s] [y] [.marginalize [y] [y]])) := by
  have first :
      plan (graph .c) s y [y] (current .c) =
        .peel (current .c) [[x]] [w1, w2, y, s]
          (plan (graph .c) s y [y] [w1, w2, y, s]) := by
    rw [plan]
    decide +kernel
  have second :
      plan (graph .c) s y [y] [w1, w2, y, s] =
        .restrict [w1, w2, y, s] [w2, y, s] (plan (graph .c) s y [y] [w2, y, s]) := by
    rw [plan]
    decide +kernel
  have finish :
      plan (graph .c) s y [y] [w2, y, s] =
        .identify [w2, y, s] [y] (identifyPlan (graph .c) [y] y [y]) := by
    rw [plan]
    decide +kernel
  have ordinary :
      identifyPlan (graph .c) [y] y [y] = [.marginalize [y] [y]] := by
    rw [identifyPlan]
    decide +kernel
  rw [first, second, finish, ordinary]

end
end OpenCausalScience.Papers.BareinboimTian2015.Figure5
