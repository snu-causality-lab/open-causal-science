module
public import OpenCausalScience.Papers.Richardson2009.HeadTail

/-!
# Head–tail calculations for Richardson (2009), Figures 1 and 2
-/

namespace OpenCausalScience.Papers.Richardson2009.Figures

open OpenCausalScience.MixedGraph

@[expose] public section

abbrev x₁ : Fin 4 := 0
abbrev x₂ : Fin 4 := 1
abbrev x₃ : Fin 4 := 2
abbrev x₄ : Fin 4 := 3

def edge (arrows arcs : List (Fin 4 × Fin 4))
    (u : Fin 4) (atU : Bool) (v : Fin 4) (atV : Bool) : Bool :=
  u != v && match atU, atV with
    | false, false => false
    | false, true => arrows.contains (u, v)
    | true, false => arrows.contains (v, u)
    | true, true => arcs.contains (u, v) || arcs.contains (v, u)

def graphFrom (arrows arcs : List (Fin 4 × Fin 4)) : MixedGraph 4 where
  edge := edge arrows arcs
  symmetric u h v k := by
    have unequal : (u != v) = (v != u) := congrArg (! ·) (BEq.comm (a := u) (b := v))
    cases h <;> cases k <;> simp [edge, unequal, Bool.or_comm]
  loop_free u h k := by simp [edge]
  no_arrow_of_undirected := by simp [edge]

def figure1 : MixedGraph 4 := graphFrom [(x₁, x₃), (x₂, x₄)] [(x₃, x₄)]
def figure2 : MixedGraph 4 := graphFrom [(x₁, x₃), (x₂, x₄)] [(x₁, x₄), (x₂, x₃)]

def full : List (Fin 4) := [x₁, x₂, x₃, x₄]

/-- The nine ancestral margins of each figure, since both figures have
the same two directed edges. -/
def margins : List (List (Fin 4)) :=
  [[], [x₁], [x₂], [x₁, x₂], [x₁, x₃], [x₂, x₄], [x₁, x₂, x₃], [x₁, x₂, x₄], full]

def ancestralMargins (G : MixedGraph 4) : List (List (Fin 4)) :=
  ((masks 4).map fun m => (List.finRange 4).filter (fun v => m.getLsbD v)).filter fun W =>
    (G.ancestorsOf W.contains).all W.contains
where masks (n : Nat) : List (BitVec n) := (List.finRange (2 ^ n)).map BitVec.ofFin

theorem margins_complete :
    (ancestralMargins figure1).Perm margins ∧ (ancestralMargins figure2).Perm margins := by
  decide +kernel

/-- Figure 1 has ordinary singleton factors and a joint factor for
the head containing both outcomes. -/
theorem figure1_head_and_tail :
    figure1.headPartition full = [[x₁], [x₂], [x₃, x₄]] ∧
    figure1.headTail [x₃, x₄] = [x₁, x₂] ∧
    figure1.headTail [x₃] = [x₁] ∧ figure1.headTail [x₄] = [x₂] := by
  decide +kernel

/-- Figure 2 conditions each head on a vertex of the other head. -/
theorem figure2_cyclic_conditioning :
    figure2.headPartition full = [[x₁, x₄], [x₂, x₃]] ∧
    figure2.headTail [x₁, x₄] = [x₂] ∧ figure2.headTail [x₂, x₃] = [x₁] := by
  decide +kernel

/-- Correlated binary noise, independent of two uniform binary roots. -/
def figure1Mass (x : BitVec 4) : Rat :=
  let u₃ := xor (x.getLsbD x₁) (x.getLsbD x₃)
  let u₄ := xor (x.getLsbD x₂) (x.getLsbD x₄)
  (1/4) * (if u₃ != u₄ then (1/8) else if u₃ then (1/4) else (1/2))

def cells : List (BitVec 4) := (List.finRange 16).map BitVec.ofFin

def marginMass (W : List (Fin 4)) (x : BitVec 4) : Rat :=
  ((cells.filter fun y => W.all fun v => x.getLsbD v == y.getLsbD v).map figure1Mass).sum

def factors (G : MixedGraph 4) (W : List (Fin 4)) (x : BitVec 4) : Rat :=
  ((G.headPartition W).map fun H =>
    let T := G.headTail H
    marginMass (H ++ T) x / marginMass T x).prod

theorem figure1_positive_normalized :
    cells.all (fun x => decide (0 < figure1Mass x)) = true ∧
    (cells.map figure1Mass).sum = 1 := by decide +kernel

set_option maxRecDepth 2048 in
/-- Exact head–tail factorization for a positive binary law in every
ancestral margin of Figure 1. -/
theorem figure1_all_ancestral_factors :
    margins.all (fun W => cells.all fun x => factors figure1 W x == marginMass W x) = true :=
  by decide +kernel

end
end OpenCausalScience.Papers.Richardson2009.Figures
