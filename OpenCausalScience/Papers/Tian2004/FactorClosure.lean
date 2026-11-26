module
public import OpenCausalScience.Papers.Tian2004.Reduction
public import OpenCausalScience.Papers.KimEtAl2026.BayesBallCorrectness

/-! Tian (2004), Figure 3, Phase 3 merges factors through their common
summed variables. The least fixed point gives the factors that must
stay on the same side as some failed component during normalization. -/

namespace OpenCausalScience.Papers.Tian2004.FactorClosure

open MixedGraph (Reach)
open FactorGraph
open Reduction
open OpenCausalScience.Papers.KimEtAl2026.BayesBallCorrectness (explore explore_covers
  explore_closed explore_sound)

@[expose] public section

variable {n : Nat}

/-- Represent any factor by any member of its district. Two factors
communicate if they use the same summed variable. -/
def FactorStep (G : MixedGraph n) (live Y Z : Vertices n) (d e : Fin n) : Prop :=
  live d ∧ live e ∧
    (district G live d e ∨ ∃ f, live f ∧ Free Y Z f ∧ scope G live d f ∧ scope G live e f)

private theorem step_from_scope {G : MixedGraph n} {live Y Z : Vertices n}
    {d f : Fin n} (fLive : live f) (free : Free Y Z f) (argument : scope G live d f) :
    Reach (Bridge G live Y Z) d f := by
  rcases argument with within | ⟨v, inDistrict, edge⟩
  · exact paths_in_district_are_bridges within.2
  · exact .extend (paths_in_district_are_bridges inDistrict.2)
      ⟨inDistrict.1, fLive, Or.inr (Or.inr ⟨free, edge⟩)⟩

private theorem bridge_of_factor_step {G : MixedGraph n} {live Y Z : Vertices n} {u v : Fin n}
    (step : FactorStep G live Y Z u v) : Reach (Bridge G live Y Z) u v := by
  rcases step.2.2 with same | ⟨f, fLive, free, hu, hv⟩
  · exact paths_in_district_are_bridges same.2
  · exact reach_trans (step_from_scope fLive free hu)
      (reach_symm bridge_symm (step_from_scope fLive free hv))

private theorem factor_step_of_bridge {G : MixedGraph n} {live Y Z : Vertices n} {u v : Fin n}
    (step : Bridge G live Y Z u v) : FactorStep G live Y Z u v := by
  refine ⟨step.1, step.2.1, ?_⟩
  rcases step.2.2 with bidirected | ⟨free, dir⟩ | ⟨free, dir⟩
  · exact Or.inl ⟨step.2.1, .extend (.refl u) ⟨step.1, step.2.1, bidirected⟩⟩
  · exact Or.inr ⟨u, step.1, free, Or.inl ⟨step.1, .refl _⟩,
      Or.inr ⟨v, ⟨step.2.1, .refl _⟩, dir⟩⟩
  · exact Or.inr ⟨v, step.2.1, free, Or.inr ⟨u, ⟨step.1, .refl _⟩, dir⟩,
      Or.inl ⟨step.2.1, .refl _⟩⟩

theorem reach_factor_iff_bridge {G : MixedGraph n} {live Y Z : Vertices n} {u v : Fin n} :
    Reach (FactorStep G live Y Z) u v ↔ Reach (Bridge G live Y Z) u v := by
  constructor
  · intro route
    induction route with
    | refl => exact .refl _
    | extend _ edge ih => exact reach_trans ih (bridge_of_factor_step edge)
  · exact reach_map factor_step_of_bridge

/-- Express output linkage in terms of closed factor scopes. -/
theorem linked_iff_outcome_in_reached_scope {G : MixedGraph n} {live Y Z : Vertices n}
    {u : Fin n} : Linked G live Y Z u ↔
      ∃ v, live v ∧ Reach (FactorStep G live Y Z) u v ∧ ∃ y, Y y ∧ scope G live v y := by
  constructor
  · rintro ⟨v, path, hv, hit⟩
    refine ⟨v, hv, reach_factor_iff_bridge.mpr path, ?_⟩
    rcases hit with here | ⟨y, hy, arrow⟩
    · exact ⟨v, here, Or.inl ⟨hv, .refl _⟩⟩
    · exact ⟨y, hy, Or.inr ⟨v, ⟨hv, .refl _⟩, arrow⟩⟩
  · rintro ⟨v, _, path, y, hy, hit⟩
    have before := reach_factor_iff_bridge.mp path
    rcases hit with member | ⟨w, member, arrow⟩
    · exact ⟨y, reach_trans before (paths_in_district_are_bridges member.2),
        member.1, Or.inl hy⟩
    · exact ⟨w, reach_trans before (paths_in_district_are_bridges member.2),
        member.1, Or.inr ⟨y, hy, arrow⟩⟩

/-- Failed factors and all the factors that Phase 3 pulls in. -/
def MarkedFactors (G : MixedGraph n) (live Y Z failed : Vertices n) (v : Fin n) : Prop :=
  ∃ d, failed d ∧ live d ∧ Reach (FactorStep G live Y Z) d v

def MarkedSummed (G : MixedGraph n) (live Y Z : Vertices n)
    (marked : Vertices n) (f : Fin n) : Prop :=
  live f ∧ Free Y Z f ∧ ∃ d, marked d ∧ scope G live d f

/-- A stationary marking includes every failed factor and is closed
under sharing a summed argument and changing district representative. -/
structure ClosedMarking (G : MixedGraph n) (live Y Z failed marked : Vertices n) : Prop where
  seeds : ∀ d, failed d → live d → marked d
  closed : ∀ {d e}, marked d → FactorStep G live Y Z d e → marked e

theorem marked_is_least_closed (G : MixedGraph n) (live Y Z failed : Vertices n) :
    ClosedMarking G live Y Z failed (MarkedFactors G live Y Z failed) ∧
      ∀ marked, ClosedMarking G live Y Z failed marked →
        ∀ d, MarkedFactors G live Y Z failed d → marked d := by
  constructor
  · exact ⟨fun d bad here => ⟨d, bad, here, .refl d⟩,
      fun ⟨d, bad, here, path⟩ next => ⟨d, bad, here, .extend path next⟩⟩
  · rintro marked closed v ⟨d, bad, here, route⟩
    induction route with
    | refl => exact closed.seeds _ bad here
    | extend _ step ih => exact closed.closed ih step

theorem marked_factor_of_marked_summed {G : MixedGraph n} {live Y Z failed : Vertices n}
    {d f : Fin n}
    (summed : MarkedSummed G live Y Z (MarkedFactors G live Y Z failed) f)
    (liveFactor : live d) (usesSummed : scope G live d f) :
    MarkedFactors G live Y Z failed d := by
  obtain ⟨fLive, free, predecessor, marked, uses⟩ := summed
  obtain ⟨seed, bad, here, route⟩ := marked
  have predLive : live predecessor := by
    cases route with
    | refl => exact here
    | extend _ edge => exact edge.2.1
  exact ⟨seed, bad, here, .extend route
    ⟨predLive, liveFactor, Or.inr ⟨f, fLive, free, uses, usesSummed⟩⟩⟩

/-- Phase 4 checks precisely whether the joint factor of an
outcome-linked block contains any failed district. -/
theorem phase_four_iff_tian_fails (G : MixedGraph n) (q : Query n)
    (intrinsic : Vertices n → Prop) :
    (∃ v y, q.live G v ∧
       MarkedFactors G (q.live G) q.outcome q.evidence (fun d => ¬ intrinsic (q.district G d)) v ∧
       q.outcome y ∧ scope G (q.live G) v y) ↔ TianFails G q intrinsic := by
  constructor
  · rintro ⟨v, y, here, ⟨d, bad, _, path⟩, hy, scopeY⟩
    exact ⟨d, linked_iff_outcome_in_reached_scope.mpr ⟨v, here, path, y, hy, scopeY⟩, bad⟩
  · rintro ⟨d, linked, bad⟩
    obtain ⟨v, hv, path, y, hy, scopeY⟩ := linked_iff_outcome_in_reached_scope.mp linked
    exact ⟨v, y, hv, ⟨d, bad, linked_is_live linked, path⟩, hy, scopeY⟩

/-- Iterate the equivalent marking with a finite worklist. The Boolean
inputs describe factor representatives, failed seeds and shared-scope tests. -/
def phaseThree (live failed : Fin n → Bool) (step : Fin n → Fin n → Bool) : List (Fin n) :=
  let vertices := (List.finRange n).filter live
  explore (fun d => vertices.filter (step d)) vertices (vertices.filter failed)

theorem phase_three_iff_marked (G : MixedGraph n) (live Y Z failed : Vertices n)
    (liveTest failTest : Fin n → Bool) (stepTest : Fin n → Fin n → Bool)
    (liveSpec : ∀ d, liveTest d = true ↔ live d)
    (failSpec : ∀ d, failTest d = true ↔ failed d)
    (stepSpec : ∀ d e, stepTest d e = true ↔ FactorStep G live Y Z d e)
    (d : Fin n) :
    d ∈ phaseThree liveTest failTest stepTest ↔ MarkedFactors G live Y Z failed d := by
  let vertices := (List.finRange n).filter liveTest
  let next (d : Fin n) := vertices.filter (stepTest d)
  have live_iff (d : Fin n) : d ∈ vertices ↔ live d := by
    simp [vertices, List.mem_finRange, liveSpec d]
  change d ∈ explore next vertices (vertices.filter failTest) ↔ _
  constructor
  · intro found
    have marks := (marked_is_least_closed G live Y Z failed).1
    exact explore_sound (P := MarkedFactors G live Y Z failed)
      (fun _ e old step => marks.closed old ((stepSpec _ e).mp (List.mem_filter.mp step).2))
      (fun a mem => marks.seeds a ((failSpec a).mp (List.mem_filter.mp mem).2)
        ((live_iff a).mp (List.mem_filter.mp mem).1)) found
  · rintro ⟨seed, bad, here, route⟩
    induction route with
    | refl =>
      exact explore_covers ((live_iff seed).mpr here)
        (List.mem_filter.mpr ⟨(live_iff seed).mpr here, (failSpec seed).mpr bad⟩)
    | extend _ step ih =>
      have survives := (live_iff _).mpr step.2.1
      exact explore_closed (next := next) ih
        (List.mem_filter.mpr ⟨survives, (stepSpec _ _).mpr step⟩) survives

end
end OpenCausalScience.Papers.Tian2004.FactorClosure
