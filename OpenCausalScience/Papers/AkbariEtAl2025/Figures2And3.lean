module
public import OpenCausalScience.Papers.AkbariEtAl2025.HedgeHull

/-! # The running example in Figures 2 and 3

Figure 2(b) shows the ancestors of S after removing x. Figure 3
instead considers the kernel Q[S] and seeks an experiment that
eliminates its hedges. Both calculations use Figure 2(a)'s graph.

Source: https://jmlr.org/papers/volume26/22-1516/22-1516.pdf#page=5
-/

namespace OpenCausalScience.Papers.AkbariEtAl2025.Figures2And3

open TianPearl2003.IdentifyRecurrence HedgeHull

@[expose] public section

abbrev v1 : Fin 6 := 0
abbrev v2 : Fin 6 := 1
abbrev s1 : Fin 6 := 2
abbrev s2 : Fin 6 := 3
abbrev v3 : Fin 6 := 4
abbrev x : Fin 6 := 5

def observed : Vertices 6 := [v1, v2, s1, s2, v3, x]
def target : Vertices 6 := [s1, s2]
def largeHedge : Vertices 6 := [v1, v2, s1, s2]
def smallHedge : Vertices 6 := [v2, s1, s2]

def directed : List (Fin 6 × Fin 6) := [(v1, v2), (v2, s1), (s1, s2), (s2, x), (v3, x)]
def bidirected : List (Fin 6 × Fin 6) :=
  [(v2, s2), (s1, s2), (v1, s2), (v1, x), (s1, x), (v3, x)]

def markedEdge (u : Fin 6) (atU : Bool) (v : Fin 6) (atV : Bool) : Bool :=
  match atU, atV with
  | false, true => directed.contains (u, v)
  | true, false => directed.contains (v, u)
  | true, true => bidirected.contains (u, v) || bidirected.contains (v, u)
  | false, false => false

def graph : MixedGraph 6 where
  edge := markedEdge
  symmetric := by decide +kernel
  loop_free := by decide +kernel
  no_arrow_of_undirected := by
    intro u v _ _ undirected
    change false = true at undirected
    contradiction

theorem directed_edges_increase :
    ∀ u v, graph.edge u false v true = true → u.val < v.val := by decide +kernel

theorem figure2_ancestors :
    ancestors graph (remove observed [x]) target = largeHedge := by decide +kernel

theorem target_stable : Stable graph target s1 target := by
  constructor <;> decide +kernel

theorem figure3_hedges :
    IsHedge graph observed target s1 largeHedge ∧ IsHedge graph observed target s1 smallHedge := by
  constructor
  · refine ⟨by decide +kernel, ?_, v1, by decide +kernel, by decide +kernel⟩
    constructor <;> decide +kernel
  · refine ⟨by decide +kernel, ?_, v2, by decide +kernel, by decide +kernel⟩
    constructor <;> decide +kernel

theorem figure3_hulls :
    hedgeHull graph observed target s1 = largeHedge ∧
    hedgeHull graph (remove observed [v1]) target s1 = smallHedge ∧
    hedgeHull graph (remove observed [v2]) target s1 = target := by decide +kernel

theorem figure3_v2_removes_all_hedges : NoHedge graph (remove observed [v2]) target s1 := by
  apply (no_hedge_iff_hull_subset_target (by decide +kernel) target_stable).mpr
  rw [figure3_hulls.2.2]
  intro v hv
  exact hv

theorem figure3_hitting_iff_v2 {A : Vertices 6} :
    HitsEveryHedge graph observed target s1 A ↔ v2 ∈ A := by
  constructor
  · intro hits
    obtain ⟨v, member, outside, inA⟩ := hits smallHedge figure3_hedges.2
    have unique : ∀ w, w ∈ smallHedge → w ∉ target → w = v2 := by decide +kernel
    exact unique v member outside ▸ inA
  · intro v2InA vertices hedge
    have avoids : ∀ v ∈ ([v2] : Vertices 6), v ∉ target := by decide +kernel
    have hits := (no_hedge_after_removal_iff_hits_every_hedge avoids).mp figure3_v2_removes_all_hedges
    obtain ⟨v, member, outside, intervention⟩ := hits vertices hedge
    have same : v = v2 := List.mem_singleton.mp intervention
    exact ⟨v, member, outside, same.symm ▸ v2InA⟩

/-- Every feasible intervention contains v2. In particular, any nonnegative
additive vertex cost on sets is minimized at the singleton {v2}. -/
theorem figure3_singleton_optimum {Cost : Type} [LE Cost] (cost : Vertices 6 → Cost)
    (monotone : ∀ {A B}, A ⊆ B → cost A ≤ cost B) :
    Minimizes cost (fun A => Admissible observed target A ∧
      NoHedge graph (remove observed A) target s1) [v2] := by
  apply (minimum_removal_iff_minimum_hitting_set graph observed target s1 cost [v2]).mpr
  refine ⟨⟨⟨by decide +kernel, by decide +kernel⟩, figure3_hitting_iff_v2.mpr (by decide +kernel)⟩, ?_⟩
  intro alternative feasible
  apply monotone
  intro v hv
  exact (List.mem_singleton.mp hv).symm ▸ figure3_hitting_iff_v2.mp feasible.2

/-- With no proper hedge, its union is empty and the algorithm still retains s1. -/
theorem figure3_empty_union_case :
    s1 ∈ hedgeHull graph (remove observed [v2]) target s1 ∧
    ¬ ∃ vertices, IsHedge graph (remove observed [v2]) target s1 vertices ∧ s1 ∈ vertices := by
  refine ⟨?_, ?_⟩
  · rw [figure3_hulls.2.2]
    decide +kernel
  · rintro ⟨vertices, hedge, _⟩
    exact figure3_v2_removes_all_hedges vertices hedge

end

end OpenCausalScience.Papers.AkbariEtAl2025.Figures2And3
