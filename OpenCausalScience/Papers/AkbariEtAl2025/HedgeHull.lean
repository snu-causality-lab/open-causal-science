module
public import OpenCausalScience.Papers.Shpitser2023.FixedPointObstruction

/-! # Hedges under a single intervention

Akbari, Etesami and Kiyavash (2025), Definition 2, Lemma 3 and
Algorithm 1 in Lemma 6. The setting is the induced graph on the variables
not intervened upon. Definition 2 requires the target to be a strict
subset of a hedge. Algorithm 1 returns the target together with the union
of all hedges, and hence returns the target when no hedge exists.

Source: https://jmlr.org/papers/volume26/22-1516/22-1516.pdf
-/

namespace OpenCausalScience.Papers.AkbariEtAl2025.HedgeHull

open TianPearl2003.IdentifyRecurrence TianPearl2003.IdentifyReachability
open Shpitser2023.FixedPointObstruction (Reached.extend_current)

@[expose] public section

variable {n : Nat}

/-- All vertices are in the root's district and are ancestors of the target
within the induced graph. For the single-district query, the root is chosen
from the target. -/
structure Stable (graph : MixedGraph n) (target : Vertices n) (root : Fin n)
    (vertices : Vertices n) : Prop where
  includes : target ⊆ vertices
  connected : vertices ⊆ district graph vertices root
  ancestral : vertices ⊆ ancestors graph vertices target

structure IsHedge (graph : MixedGraph n) (current target : Vertices n) (root : Fin n)
    (vertices : Vertices n) : Prop where
  within : vertices ⊆ current
  stable : Stable graph target root vertices
  proper : ∃ v ∈ vertices, v ∉ target

def remove (current intervention : Vertices n) : Vertices n :=
  current.filter fun v => !intervention.contains v

theorem mem_remove {current intervention : Vertices n} {v : Fin n} :
    v ∈ remove current intervention ↔ v ∈ current ∧ v ∉ intervention := by
  simp [remove]

def NoHedge (graph : MixedGraph n) (current target : Vertices n) (root : Fin n) : Prop :=
  ∀ vertices, ¬ IsHedge graph current target root vertices

def HitsEveryHedge (graph : MixedGraph n) (current target : Vertices n) (root : Fin n)
    (intervention : Vertices n) : Prop :=
  ∀ vertices, IsHedge graph current target root vertices →
    ∃ v ∈ vertices, v ∉ target ∧ v ∈ intervention

/-- Lemma 3's graph equivalence. The probability-level hedge criterion is
a separate premise when this equivalence is used for identifiability. -/
theorem no_hedge_after_removal_iff_hits_every_hedge {graph : MixedGraph n}
    {current target intervention : Vertices n} {root : Fin n}
    (avoids : ∀ v ∈ intervention, v ∉ target) :
    NoHedge graph (remove current intervention) target root ↔
      HitsEveryHedge graph current target root intervention := by
  classical
  constructor
  · intro noHedge vertices hedge
    apply Classical.byContradiction
    intro missed
    apply noHedge vertices
    refine ⟨?_, hedge.stable, hedge.proper⟩
    intro v hv
    exact mem_remove.mpr ⟨hedge.within hv, fun included =>
      missed ⟨v, hv, avoids v included, included⟩⟩
  · intro hits vertices survives
    have within : vertices ⊆ current := by
      intro v hv
      exact (mem_remove.mp (survives.within hv)).1
    obtain ⟨v, hv, _, included⟩ := hits vertices
      ⟨within, survives.stable, survives.proper⟩
    exact (mem_remove.mp (survives.within hv)).2 included

def Admissible (current target intervention : Vertices n) : Prop :=
  intervention ⊆ current ∧ ∀ v ∈ intervention, v ∉ target

def Minimizes {Cost : Type} [LE Cost] (cost : Vertices n → Cost)
    (feasible : Vertices n → Prop) (choice : Vertices n) : Prop :=
  feasible choice ∧ ∀ alternative, feasible alternative → cost choice ≤ cost alternative

/-- The feasible collections coincide, so the optimum sets coincide for the
same cost function. In the paper both costs sum nonnegative vertex costs. -/
theorem minimum_removal_iff_minimum_hitting_set {Cost : Type} [LE Cost]
    (graph : MixedGraph n) (current target : Vertices n) (root : Fin n)
    (cost : Vertices n → Cost) (choice : Vertices n) :
    Minimizes cost (fun A => Admissible current target A ∧
      NoHedge graph (remove current A) target root) choice ↔
    Minimizes cost (fun A => Admissible current target A ∧
      HitsEveryHedge graph current target root A) choice := by
  have equiv (A : Vertices n) :
      (Admissible current target A ∧ NoHedge graph (remove current A) target root) ↔
      (Admissible current target A ∧ HitsEveryHedge graph current target root A) :=
    ⟨fun h => ⟨h.1, (no_hedge_after_removal_iff_hits_every_hedge h.1.2).mp h.2⟩,
      fun h => ⟨h.1, (no_hedge_after_removal_iff_hits_every_hedge h.1.2).mpr h.2⟩⟩
  exact ⟨fun h => ⟨(equiv choice).mp h.1, fun A ha => h.2 A ((equiv A).mpr ha)⟩,
    fun h => ⟨(equiv choice).mpr h.1, fun A ha => h.2 A ((equiv A).mp ha)⟩⟩

/-- First retain the district of the target, then compute ancestry in that
district, as in lines 4–5 of Algorithm 1. -/
def prune (graph : MixedGraph n) (target : Vertices n) (root : Fin n)
    (current : Vertices n) : Vertices n :=
  ancestors graph (district graph current root) target

private theorem prune_sublist (graph : MixedGraph n) (target : Vertices n) (root : Fin n)
    (current : Vertices n) : (prune graph target root current).Sublist current := by
  unfold prune
  have reach : (ancestors graph (district graph current root) target).Sublist
      (district graph current root) := List.filter_sublist
  exact reach.trans List.filter_sublist

private theorem prune_preserves {graph : MixedGraph n} {current target vertices : Vertices n}
    {root : Fin n} (within : vertices ⊆ current) (stable : Stable graph target root vertices) :
    vertices ⊆ prune graph target root current := by
  have inDistrict : vertices ⊆ district graph current root := by
    intro v hv
    exact (mem_district_iff graph current root v).mpr
      (Reached.extend_current within ((mem_district_iff graph vertices root v).mp
        (stable.connected hv)))
  intro v hv
  exact (mem_ancestors_iff graph (district graph current root) target v).mpr
    (Reached.extend_current inDistrict ((mem_ancestors_iff graph vertices target v).mp
      (stable.ancestral hv)))

def hullRounds (graph : MixedGraph n) (target : Vertices n) (root : Fin n) :
    Nat → Vertices n → Vertices n
  | 0, current => current
  | rounds + 1, current =>
    let next := prune graph target root current
    if next = current then current else hullRounds graph target root rounds next

/-- Algorithm 1 with a bound of one pruning step per input list entry.
After the bound the graph has reached a fixed point. -/
def hedgeHull (graph : MixedGraph n) (current target : Vertices n) (root : Fin n) : Vertices n :=
  hullRounds graph target root current.length current

theorem hedge_hull_subset (graph : MixedGraph n) (current target : Vertices n) (root : Fin n) :
    hedgeHull graph current target root ⊆ current := by
  have within (rounds : Nat) (vertices : Vertices n) :
      hullRounds graph target root rounds vertices ⊆ vertices := by
    induction rounds generalizing vertices with
    | zero =>
      intro v hv
      exact hv
    | succ rounds ih =>
      by_cases same : prune graph target root vertices = vertices
      · simp [hullRounds, same]
      · intro v hv
        have inPruned := ih (prune graph target root vertices)
          (by simpa only [hullRounds, ite_eq_right same] using hv)
        exact (prune_sublist graph target root vertices).subset inPruned
  exact within current.length current

theorem stable_subset_hedge_hull {graph : MixedGraph n} {current target vertices : Vertices n}
    {root : Fin n} (within : vertices ⊆ current) (stable : Stable graph target root vertices) :
    vertices ⊆ hedgeHull graph current target root := by
  have persists (rounds : Nat) (active : Vertices n) (inside : vertices ⊆ active) :
      vertices ⊆ hullRounds graph target root rounds active := by
    induction rounds generalizing active with
    | zero => exact inside
    | succ rounds ih =>
      by_cases same : prune graph target root active = active
      · simpa only [hullRounds, ite_eq_left same] using inside
      · simpa only [hullRounds, ite_eq_right same] using
          ih _ (prune_preserves inside stable)
  exact persists current.length current within

theorem hedge_hull_fixed (graph : MixedGraph n) (current target : Vertices n) (root : Fin n) :
    prune graph target root (hedgeHull graph current target root) =
      hedgeHull graph current target root := by
  have fixed (rounds : Nat) (active : Vertices n) (enough : active.length ≤ rounds) :
      prune graph target root (hullRounds graph target root rounds active) =
        hullRounds graph target root rounds active := by
    induction rounds generalizing active with
    | zero =>
      have sub := prune_sublist graph target root active
      have le := sub.length_le
      exact sub.eq_of_length (by omega)
    | succ rounds ih =>
      by_cases same : prune graph target root active = active
      · simp [hullRounds, same]
      · have sub := prune_sublist graph target root active
        have le := sub.length_le
        have differentLengths : (prune graph target root active).length ≠ active.length :=
          fun equal => same (sub.eq_of_length equal)
        simpa only [hullRounds, ite_eq_right same] using
          ih (prune graph target root active) (by omega)
  exact fixed current.length current (Nat.le_refl _)

theorem hedge_hull_stable {graph : MixedGraph n} {current target : Vertices n} {root : Fin n}
    (targetWithin : target ⊆ current) (targetStable : Stable graph target root target) :
    Stable graph target root (hedgeHull graph current target root) := by
  let hull := hedgeHull graph current target root
  have fixed : prune graph target root hull = hull := hedge_hull_fixed graph current target root
  have districtSub : (district graph hull root).Sublist hull := List.filter_sublist
  have ancestorSub : (prune graph target root hull).Sublist (district graph hull root) :=
    List.filter_sublist
  have hullLe := ancestorSub.length_le
  rw [fixed] at hullLe
  have districtEq : district graph hull root = hull :=
    districtSub.eq_of_length (Nat.le_antisymm districtSub.length_le hullLe)
  have ancestorEq : ancestors graph hull target = hull := by
    simpa only [prune, districtEq] using fixed
  refine ⟨stable_subset_hedge_hull targetWithin targetStable, ?_, ?_⟩
  · intro v hv
    exact districtEq.symm ▸ hv
  · intro v hv
    exact ancestorEq.symm ▸ hv

/-- Lemma 6's output is the target together with the union of proper hedges.
The target is included even when the union is empty. -/
theorem mem_hedge_hull_iff {graph : MixedGraph n} {current target : Vertices n} {root v : Fin n}
    (targetWithin : target ⊆ current) (targetStable : Stable graph target root target) :
    v ∈ hedgeHull graph current target root ↔
      v ∈ target ∨ ∃ vertices, IsHedge graph current target root vertices ∧ v ∈ vertices := by
  have stable := hedge_hull_stable targetWithin targetStable
  constructor
  · intro inHull
    by_cases inTarget : v ∈ target
    · exact .inl inTarget
    · exact .inr ⟨_, ⟨hedge_hull_subset graph current target root, stable, v, inHull, inTarget⟩,
        inHull⟩
  · rintro (inTarget | ⟨_, hedge, member⟩)
    · exact stable.includes inTarget
    · exact stable_subset_hedge_hull hedge.within hedge.stable member

theorem no_hedge_iff_hull_subset_target {graph : MixedGraph n} {current target : Vertices n}
    {root : Fin n} (targetWithin : target ⊆ current) (targetStable : Stable graph target root target) :
    NoHedge graph current target root ↔ hedgeHull graph current target root ⊆ target := by
  constructor
  · intro noHedge v hv
    rcases (mem_hedge_hull_iff targetWithin targetStable).mp hv with
      inTarget | ⟨vertices, hedge, _⟩
    · exact inTarget
    · exact False.elim (noHedge vertices hedge)
  · intro hullWithin vertices hedge
    obtain ⟨v, member, outside⟩ := hedge.proper
    exact outside (hullWithin (stable_subset_hedge_hull hedge.within hedge.stable member))

end

end OpenCausalScience.Papers.AkbariEtAl2025.HedgeHull
