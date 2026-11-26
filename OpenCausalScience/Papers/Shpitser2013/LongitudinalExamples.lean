module
public import OpenCausalScience.Papers.Shpitser2013.RecantingDistrict

/-! # The longitudinal examples in Figures 4 and 5

Figure 4's green paths have no recanting district. The bidirected edge
added in Figure 5(a) creates a district with two different first
successors from A₁. The blue directed edge added in Figure 5(b) gives
one successor of A₀ both a selected and an excluded continuation.
Source: https://arxiv.org/pdf/1205.0241#page=41
-/

namespace OpenCausalScience.Papers.Shpitser2013.LongitudinalExamples

open TianPearl2003.IdentifyRecurrence (Vertices district)
open TianPearl2003.IdentifyReachability (mem_district_iff)
open RecantingDistrict

@[expose] public section

abbrev a₀ : Fin 7 := 0
abbrev l₁ : Fin 7 := 1
abbrev m₁ : Fin 7 := 2
abbrev a₁ : Fin 7 := 3
abbrev l₂ : Fin 7 := 4
abbrev m₂ : Fin 7 := 5
abbrev y : Fin 7 := 6

inductive Panel
  | figure4
  | figure5a
  | figure5b
  deriving DecidableEq

def green : List (Fin 7 × Fin 7) := [(a₀, m₁), (m₁, m₂), (m₁, y), (a₁, m₂), (m₂, y)]

def blue : List (Fin 7 × Fin 7) :=
  [(a₀, l₁), (a₀, y), (l₁, m₁), (l₁, l₂), (l₁, y), (m₁, a₁),
    (a₁, l₂), (a₁, y), (l₂, m₂), (l₂, y)]

def directed (panel : Panel) (u v : Fin 7) : Bool :=
  green.contains (u, v) || blue.contains (u, v) ||
    (decide (panel = .figure5b) && (u, v) == (m₁, l₂))

def spouses (panel : Panel) (u v : Fin 7) : Bool :=
  let edges := [(l₁, l₂), (l₁, y), (l₂, y)] ++ (if panel = .figure5a then [(l₂, m₂)] else [])
  edges.contains (u, v) || edges.contains (v, u)

def markedEdge (panel : Panel) (u : Fin 7) (atU : Bool) (v : Fin 7) (atV : Bool) : Bool :=
  match atU, atV with
  | false, true => directed panel u v
  | true, false => directed panel v u
  | true, true => spouses panel u v
  | false, false => false

def graph (panel : Panel) : MixedGraph 7 where
  edge := markedEdge panel
  symmetric := by
    intro u atU v atV
    cases atU <;> cases atV <;> simp [markedEdge, spouses, Bool.or_comm]
  loop_free := by cases panel <;> decide +kernel
  no_arrow_of_undirected := by simp [markedEdge]

theorem topological (panel : Panel) : ∀ u v, (graph panel).edge u false v true = true → u < v := by
  cases panel <;> decide +kernel

def greenTail (v : Fin 7) : Vertices 7 → Bool
  | [] => true
  | w :: rest => green.contains (v, w) && greenTail w rest

def selected : PathSelection 7 := fun a first tail => green.contains (a, first) && greenTail first tail

def treatments : Vertices 7 := [a₀, a₁]
def outcomes : Vertices 7 := [y]

theorem ancestral_region (panel : Panel) :
    ancestralRegion (graph panel) treatments outcomes = [l₁, m₁, l₂, m₂, y] := by
  cases panel <;> decide +kernel

theorem figure4_no_recanting_district : ¬ Recants (graph .figure4) treatments outcomes selected := by
  have rejected : recants (graph .figure4) treatments outcomes selected = false := by decide +kernel
  intro recanting
  have accepted := (recants_eq_true_iff _ _ _ _).mpr recanting
  rw [rejected] at accepted
  exact Bool.noConfusion accepted

theorem figure5a_recanting_district :
    district (graph .figure5a) (ancestralRegion (graph .figure5a) treatments outcomes) m₂ =
      [l₁, l₂, m₂, y] ∧ Recants (graph .figure5a) treatments outcomes selected := by
  refine ⟨by decide +kernel, a₁, m₂, by decide +kernel, ?_, l₂, ?_, ?_⟩
  · exact ⟨[y], ⟨by decide +kernel, by decide +kernel,
      .step (by decide +kernel) (by decide +kernel) (.stop (by decide +kernel) (by decide +kernel))⟩,
      by decide +kernel⟩
  · apply (mem_district_iff _ _ _ _).mp
    decide +kernel
  · exact ⟨[y], ⟨by decide +kernel, by decide +kernel,
      .step (by decide +kernel) (by decide +kernel) (.stop (by decide +kernel) (by decide +kernel))⟩,
      by decide +kernel⟩

theorem figure5b_recanting_district :
    district (graph .figure5b) (ancestralRegion (graph .figure5b) treatments outcomes) m₁ = [m₁] ∧
      Recants (graph .figure5b) treatments outcomes selected := by
  refine ⟨by decide +kernel, a₀, m₁, by decide +kernel, ?_, m₁, ?_, ?_⟩
  · exact ⟨[y], ⟨by decide +kernel, by decide +kernel,
      .step (by decide +kernel) (by decide +kernel) (.stop (by decide +kernel) (by decide +kernel))⟩,
      by decide +kernel⟩
  · apply (mem_district_iff _ _ _ _).mp
    decide +kernel
  · exact ⟨[l₂, y], ⟨by decide +kernel, by decide +kernel,
      .step (by decide +kernel) (by decide +kernel)
        (.step (by decide +kernel) (by decide +kernel) (.stop (by decide +kernel) (by decide +kernel)))⟩,
      by decide +kernel⟩

end
end OpenCausalScience.Papers.Shpitser2013.LongitudinalExamples
