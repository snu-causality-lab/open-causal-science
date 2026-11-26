module
public import OpenCausalScience.Papers.CorreaLeeBareinboim2021.SourceKernels

/-! # Source availability on Figure 5(a)

The two-vertex source after intervening on X supports the factor on Z.
Observation alone reaches the ancestor fixed point on the bow X → Z,
X ↔ Z. The observational source is sufficient for the singleton Y
factor. Correa, Lee and Bareinboim (2021), Figure 5(a) and equation (17).

Source: https://proceedings.neurips.cc/paper/2021/file/36bedb6eb7152f39b16328448942822b-Paper.pdf#page=7
-/

namespace OpenCausalScience.Papers.CorreaLeeBareinboim2021.Figure5

open TianPearl2003.IdentifyRecurrence
open SourceKernels

@[expose] public section

abbrev x : Fin 3 := 0
abbrev z : Fin 3 := 1
abbrev y : Fin 3 := 2

def edge (u : Fin 3) (atU : Bool) (v : Fin 3) (atV : Bool) : Bool :=
  if u < v then
    if u == x && v == z then atV else !atU && atV
  else if v < u then
    if v == x && u == z then atU else atU && !atV
  else false

def graph : MixedGraph 3 where
  edge
  symmetric := by decide +kernel
  loop_free := by decide +kernel
  no_arrow_of_undirected := by
    have noLines : ∀ u v, edge u false v false = false := by decide +kernel
    intro u v w mark incident
    rw [noLines] at incident
    contradiction

def observed : Vertices 3 := [x, z, y]
def experimentX : Vertices 3 := [z, y]

theorem observed_z_fixed_point :
    identifyPlan graph [z] z (district graph observed z) = [.ancestorFixedPoint [x, z]] := by
  rw [identifyPlan]
  decide +kernel

theorem experiment_x_recovers_z :
    findSource graph [z] z [observed, experimentX] = some experimentX := by
  unfold findSource admits
  change List.find? (fun source => [z].all source.contains &&
    completes (identifyPlan graph [z] z (district graph source z))) [observed, experimentX] = _
  have plan : identifyPlan graph [z] z (district graph experimentX z) =
      [.marginalize [z] [z]] := by
    rw [identifyPlan]
    decide +kernel
  simp only [List.find?_cons, observed_z_fixed_point, plan]
  decide +kernel

theorem observation_alone_rejects_z :
    findSource graph [z] z [observed] = none := by
  unfold findSource admits
  simp only [List.find?_cons, observed_z_fixed_point]
  decide +kernel

theorem observation_recovers_y :
    findSource graph [y] y [observed] = some observed := by
  have plan : identifyPlan graph [y] y (district graph observed y) =
      [.marginalize [y] [y]] := by
    rw [identifyPlan]
    decide +kernel
  unfold findSource admits
  simp only [List.find?_cons, plan]
  decide +kernel

end
end OpenCausalScience.Papers.CorreaLeeBareinboim2021.Figure5
