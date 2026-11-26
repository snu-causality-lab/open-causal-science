module
public import OpenCausalScience.Papers.CorreaTianBareinboim2018.Criterion

/-! # Proper paths for a joint treatment

The printed Definition 8(b) says "all non-causal paths".
Proposition 3's proof instead restarts when it encounters another
treatment vertex. The finite check below distinguishes the literal
wording from the proper-path criterion implemented by Definition 9.

Source: https://causalai.net/r29.pdf#page=20
-/

namespace OpenCausalScience.Papers.CorreaTianBareinboim2018.JointTreatment

open Criterion

@[expose] public section

abbrev a : Fin 4 := 0
abbrev b : Fin 4 := 1
abbrev y : Fin 4 := 2
abbrev s : Fin 4 := 3

def directed (u v : Fin 4) : Bool :=
  [(a, b), (a, y), (b, s)].contains (u, v)

def marked (u : Fin 4) (atU : Bool) (v : Fin 4) (atV : Bool) : Bool :=
  match atU, atV with
  | false, true => directed u v
  | true, false => directed v u
  | _, _ => false

def graph : MixedGraph 4 where
  edge := marked
  symmetric := by decide +kernel
  loop_free := by decide +kernel
  no_arrow_of_undirected := by
    intro u v w mark edge
    change false = true at edge
    contradiction

def query : Query 4 where
  x := fun u => u == a || u == b
  y := (· == y)
  s := s
  x_outside_y := by decide +kernel
  s_outside_x := by decide +kernel
  s_outside_y := by decide +kernel

/-- B ← A → Y is active given S. It starts at B and crosses a second
treated vertex A. At A both incident marks are tails. -/
theorem nonproper_fork_is_active :
    graph.edge b true a false = true ∧ query.x a = true ∧ query.x b = true ∧
      graph.ActiveWalk query.selection (a, false) [y] (y, true) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact .cons (next := (y, true)) ⟨false, rfl, rfl⟩ (.nil (y, true))

theorem empty_pair_is_valid :
    valid graph query (fun _ => false) (fun _ => false) (fun _ => false) = true := by
  cbv

end

end OpenCausalScience.Papers.CorreaTianBareinboim2018.JointTreatment
