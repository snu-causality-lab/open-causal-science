module
public import OpenCausalScience.Papers.CorreaTianBareinboim2018.Criterion

/-! # An adjustment pair with partial external data

Correa, Tian and Bareinboim (2018), Figure 2 and equation (5).
The internal appendix repeats this graph as Figure 3. The selection
indicator is S and the unbiased margin is measured on Z₂ alone.
Source: https://causalai.net/r29.pdf#page=4
-/

namespace OpenCausalScience.Papers.CorreaTianBareinboim2018.Figure2

open Criterion

@[expose] public section

abbrev x1 : Fin 7 := 0
abbrev x2 : Fin 7 := 1
abbrev z1 : Fin 7 := 2
abbrev z2 : Fin 7 := 3
abbrev z3 : Fin 7 := 4
abbrev y : Fin 7 := 5
abbrev s : Fin 7 := 6

def directed (a b : Fin 7) : Bool :=
  [(x2, z3), (z3, z2), (z2, s), (x2, y), (z1, x1), (x1, y)].contains (a, b)

def confounded (a b : Fin 7) : Bool :=
  [(z2, y), (z1, s), (z1, y)].contains (a, b) ||
  [(z2, y), (z1, s), (z1, y)].contains (b, a)

def markedEdge (u : Fin 7) (atU : Bool) (v : Fin 7) (atV : Bool) : Bool :=
  match atU, atV with
  | false, false => false
  | false, true => directed u v
  | true, false => directed v u
  | true, true => confounded u v

def graph : MixedGraph 7 where
  edge := markedEdge
  symmetric := by decide +kernel
  loop_free := by decide +kernel
  no_arrow_of_undirected := by
    intro u v w mark edge
    change false = true at edge
    contradiction

def query : Query 7 where
  x := fun v => v == x1 || v == x2
  y := (· == y)
  s := s
  x_outside_y := by decide +kernel
  s_outside_x := by decide +kernel
  s_outside_y := by decide +kernel

def allZ (v : Fin 7) : Bool := v == z1 || v == z2 || v == z3
def onlyZ2 (v : Fin 7) : Bool := v == z2

theorem proper_first_edges :
    ∀ a b, properFirst graph query.x query.y a b = ((a == x1 || a == x2) && b == y) := by
  apply of_decide_eq_true
  cbv

theorem forbidden_is_outcome :
    ∀ v, forbidden graph query.x query.y v = (v == y) := by
  apply of_decide_eq_true
  cbv

theorem figure2_pair_valid :
    valid graph query allZ onlyZ2 onlyZ2 = true := by
  cbv

theorem figure2_pair_admissible : Admissible graph query allZ onlyZ2 onlyZ2 :=
  (valid_iff_admissible graph query allZ onlyZ2 onlyZ2).mp figure2_pair_valid

theorem figure2_adding_z1_to_population_is_invalid :
    valid graph query allZ (fun v => v == z1 || v == z2) allZ = false := by
  cbv

def subsetsOfZ (a b c : Bool) (v : Fin 7) : Bool :=
  (a && v == z1) || (b && v == z2) || (c && v == z3)

theorem figure2_selected_only_fails :
    ∀ a b c, valid graph query (subsetsOfZ a b c) (fun _ => false) (fun _ => false) = false := by
  apply of_decide_eq_true
  cbv

theorem figure2_all_adjustment_measured_fails :
    ∀ a b c, valid graph query (subsetsOfZ a b c) (subsetsOfZ a b c) allZ = false := by
  apply of_decide_eq_true
  cbv

end

end OpenCausalScience.Papers.CorreaTianBareinboim2018.Figure2
