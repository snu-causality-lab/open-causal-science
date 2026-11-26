module
public import OpenCausalScience.Papers.CorreaTianBareinboim2019.HybridDistrict
public import OpenCausalScience.Papers.CorreaTianBareinboim2018.Criterion
public import OpenCausalScience.Papers.BareinboimTian2015.RC

/-! # External-margin examples and the selected-only RC limitation

Correa, Tian and Bareinboim (2019), Figures 2(a), 2(b) and 3(a).
The fourth graph is an independent six-vertex CGA fixture for the
procedure and the target query in Theorem 2.

https://causalai.net/r38.pdf
https://github.com/snu-causality-lab/cga/blob/v0.2.0a1/tests/fixtures/papers/correa_tian_bareinboim_2019_rc.json
-/

namespace OpenCausalScience.Papers.CorreaTianBareinboim2019.GraphCases

open HybridDistrict
open TianPearl2003.IdentifyRecurrence
open BareinboimTian2015.RC (plan)
open CorreaTianBareinboim2018.Criterion (Query valid)

@[expose] public section

def graphEdge {n : Nat} (directed bidirected : List (Fin n × Fin n))
    (u : Fin n) (a : Bool) (v : Fin n) (b : Bool) : Bool :=
  (u != v) && (match a, b with
    | false, true => directed.contains (u, v)
    | true, false => directed.contains (v, u)
    | true, true => bidirected.contains (u, v) || bidirected.contains (v, u)
    | false, false => false)

def diagram {n : Nat} (directed bidirected : List (Fin n × Fin n)) : MixedGraph n where
  edge := graphEdge directed bidirected
  symmetric := by
    intro u a v b
    have distinct : (u != v) = (v != u) := by
      have equal : (u == v) = (v == u) := BEq.comm
      exact congrArg (! ·) equal
    cases a <;> cases b <;> simp [graphEdge, distinct, Bool.or_comm]
  loop_free := by
    intro u a b
    simp [graphEdge]
  no_arrow_of_undirected := by
    intro u v w mark edge
    simp [graphEdge] at edge

def vertices {n : Nat} (xs : List (Fin n)) : Fin n → Bool := xs.contains

namespace Figure2A

abbrev r : Fin 6 := 0
abbrev z : Fin 6 := 1
abbrev w : Fin 6 := 2
abbrev x : Fin 6 := 3
abbrev y : Fin 6 := 4
abbrev s : Fin 6 := 5

def graph := diagram [(r,z), (z,w), (z,x), (z,y), (w,s), (x,y)] [(z,s)]

theorem expanded_population :
    (List.finRange 6).filter (extendedPopulation graph (fun _ => true) (vertices [z]) s) =
      [z, x, y] := by cbv

theorem source_and_target_districts :
    district graph (List.finRange 6) s = [z, s] ∧
      ancestors graph [r, z, w, y] [y] = [r,z,y] ∧
      district graph [r,z,y] r = [r] ∧
      district graph [r,z,y] z = [z] ∧
      district graph [r,z,y] y = [y] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> cbv

theorem selected_prefix_recovers_x_and_y :
    let active := fun (_ : Fin 6) => true
    let before := vertices (ancestors graph (List.finRange 6) [z,s])
    let available := vertices [z, x, y]
    eligible graph active before available [x] = true ∧
      eligible graph active before available [y] = true ∧
      eligible graph active before available [r] = false := by apply of_decide_eq_true; cbv

end Figure2A

namespace Figure2B

abbrev w₁ : Fin 5 := 0
abbrev w₂ : Fin 5 := 1
abbrev x : Fin 5 := 2
abbrev y : Fin 5 := 3
abbrev s : Fin 5 := 4
def directed : List (Fin 5 × Fin 5) := [(w₁,w₂), (w₂,x), (w₂,s), (x,y)]
def bidirected : List (Fin 5 × Fin 5) := [(w₁,x), (w₁,y)]
def graph := diagram directed bidirected

def query : Query 5 where
  x := vertices [x]
  y := vertices [y]
  s := s
  x_outside_y := by decide +kernel
  s_outside_x := by decide +kernel
  s_outside_y := by decide +kernel

theorem external_w₂_expands_to_population :
    (List.finRange 5).filter (extendedPopulation graph (fun _ => true) (vertices [w₂]) s) =
      [w₁, w₂, x, y] := by cbv

theorem no_adjustment_for_either_margin :
    ∀ useFirst useSecond useW₁ useW₂ : Bool,
      let z := fun v => (useFirst && v == w₁) || (useSecond && v == w₂)
      let zt := fun v => (useW₁ && v == w₁) || (useW₂ && v == w₂)
      valid graph query z zt (vertices [w₁]) = false ∧
        valid graph query z zt (vertices [w₂]) = false := by apply of_decide_eq_true; cbv

theorem identify_y_from_population_district :
    identifyPlan graph [y] y (district graph [w₁,w₂,x,y] y) =
      [.marginalize [w₁,x,y] [x,y], .extractFactor [x,y] [y], .marginalize [y] [y]] := by cbv

end Figure2B

namespace Figure3A

abbrev v₄ : Fin 9 := 0
abbrev v₃ : Fin 9 := 1
abbrev v₅ : Fin 9 := 2
abbrev v₆ : Fin 9 := 3
abbrev v₁ : Fin 9 := 4
abbrev v₂ : Fin 9 := 5
abbrev x : Fin 9 := 6
abbrev y : Fin 9 := 7
abbrev s : Fin 9 := 8

def graph := diagram
  [(v₄,v₃),(v₃,x),(v₅,v₆),(v₆,y),(v₁,v₂),(v₂,x),(v₂,s),(x,y)]
  [(v₄,v₅),(v₅,v₆),(v₃,y),(v₃,s),(v₁,x),(v₁,y)]

theorem expanded_joint_and_target :
    (List.finRange 9).filter (extendedPopulation graph (fun _ => true) (vertices [v₂,v₃,v₆]) s) =
      [v₃,v₆,v₁,v₂,x] ∧
      ancestors graph [v₄,v₃,v₅,v₆,v₁,v₂,y] [y] = [v₅,v₆,y] ∧
      district graph [v₅,v₆,y] v₆ = [v₅,v₆] ∧
      district graph [v₅,v₆,y] y = [y] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> cbv

def induced (current : Vertices 9) : MixedGraph 9 where
  edge := fun u a v b => current.contains u && current.contains v && graph.edge u a v b
  symmetric := by
    intro u a v b
    rw [graph.symmetric u a v b, Bool.and_comm (current.contains u) (current.contains v)]
  loop_free := by
    intro u a b
    simp [graph.loop_free u a b]
  no_arrow_of_undirected := by
    intro u v w mark line
    simp [graph.no_arrow_of_undirected (Bool.and_eq_true_iff.mp line).2]

def full : Vertices 9 := List.finRange 9
def external : Vertices 9 := [v₃,v₆,v₁,v₂,x]
def afterV₂ : Vertices 9 := [v₄,v₃,v₅,v₆,v₁,x,y,s]
def afterV₁ : Vertices 9 := [v₄,v₃,v₅,v₆,x,y,s]
def afterX : Vertices 9 := [v₄,v₃,v₅,v₆,y,s]
def afterV₃V₄ : Vertices 9 := [v₅,v₆,y,s]

/-- In the current graph the original population margin loses
descendants of removed vertices, then grows by separation. -/
def availableAt (current : Vertices 9) : Fin 9 → Bool :=
  let removed := full.filter (!current.contains ·)
  let base := vertices (external.filter fun v => !removed.any (ancestors graph full [v]).contains)
  extendedPopulation (induced current) (vertices current) base s

def recoverableAt (current : Vertices 9) (root : Fin 9) : Bool :=
  let selectionDistrict := district graph current s
  let before := vertices (ancestors graph current selectionDistrict)
  eligible (induced current) (vertices current) before (availableAt current)
    (district graph current root)

theorem rce_divisions :
    recoverableAt full v₂ = true ∧
      district graph full v₂ = [v₂] ∧
      recoverableAt afterV₁ x = true ∧
      district graph afterV₁ x = [x] ∧
      recoverableAt afterV₃V₄ y = true ∧
      district graph afterV₃V₄ y = [y] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> cbv

theorem rce_ancestral_restrictions :
    full.erase v₂ = afterV₂ ∧
      ancestors graph afterV₂ [y,s] = afterV₁ ∧
      afterV₁.erase x = afterX ∧
      ancestors graph afterX [y,s] = afterV₃V₄ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> cbv

end Figure3A

namespace RCCounterexample

abbrev w : Fin 6 := 0
abbrev x : Fin 6 := 1
abbrev y : Fin 6 := 2
abbrev a : Fin 6 := 3
abbrev b : Fin 6 := 4
abbrev s : Fin 6 := 5

def graph := diagram [(w,x),(x,y),(a,s),(b,s)] [(w,y),(w,a),(x,b)]
def withoutIncomingX := diagram [(x,y),(a,s),(b,s)] [(w,y),(w,a)]
def backdoor := diagram [(w,x),(a,s),(b,s)] [(w,y),(w,a),(x,b)]

def query : Query 6 where
  x := vertices [x]
  y := vertices [y]
  s := s
  x_outside_y := by decide +kernel
  s_outside_x := by decide +kernel
  s_outside_y := by decide +kernel

theorem ancestors_and_districts :
    ancestors graph [w,y,a,b] [y] = [y] ∧
      ancestors graph (List.finRange 6) [y,s] = List.finRange 6 ∧
      ancestors graph (List.finRange 6) [s] = [a,b,s] ∧
      district graph (List.finRange 6) y = [w,y,a] ∧
      district graph (List.finRange 6) x = [x,b] ∧
      district graph (List.finRange 6) s = [s] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> cbv

theorem printed_rc_stops :
    plan graph s y [y] (List.finRange 6) = .blocked (List.finRange 6) := by cbv

theorem selected_only_adjustment_succeeds :
    valid graph query (vertices [w,a]) (vertices []) (vertices []) = true := by cbv

theorem do_calculus_separations :
    withoutIncomingX.mSeparated (vertices [y]) (vertices [s]) (vertices [x]) = true ∧
      backdoor.mSeparated (vertices [x]) (vertices [y]) (vertices [w,a,s]) = true ∧
      backdoor.mSeparated (vertices [y]) (vertices [s]) (vertices []) = true ∧
      backdoor.mSeparated (vertices [x]) (vertices [y]) (vertices [w,s]) = false := by
  apply of_decide_eq_true
  cbv

end RCCounterexample

end
end OpenCausalScience.Papers.CorreaTianBareinboim2019.GraphCases
