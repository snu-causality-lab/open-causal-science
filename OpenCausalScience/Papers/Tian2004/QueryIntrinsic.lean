module
public import OpenCausalScience.Papers.Tian2004.IntrinsicIdentify
public import OpenCausalScience.Papers.Tian2004.Reduction

/-! # Query districts as inputs to Identify

The conditional factor graph describes its districts by predicates.
The component Identify procedure takes the same sets as lists in a
fixed order. This bridge interprets the factor graph's district
property as intrinsic graphical reachability.
-/

namespace OpenCausalScience.Papers.Tian2004.QueryIntrinsic

open TianPearl2003.IdentifyRecurrence TianPearl2003.IdentifyReachability
open Shpitser2023.FixedPointObstruction
open IntrinsicIdentify Reduction
open MixedGraph (Reach)

@[expose] public section

variable {n : Nat}

/-- List the vertices of a predicate in the order of `Fin n`. -/
noncomputable def verticesList (vertices : Fin n → Prop) : List (Fin n) := by
  classical
  exact (List.finRange n).filter (fun v => decide (vertices v))

theorem mem_verticesList {vertices : Fin n → Prop} {v : Fin n} :
    v ∈ verticesList vertices ↔ vertices v := by
  classical
  simp [verticesList]

theorem mem_list_district_iff {G : MixedGraph n} {live : Fin n → Prop} {root v : Fin n} :
    v ∈ district G (verticesList live) root ↔ FactorGraph.district G live root v := by
  rw [mem_district_iff]
  constructor
  · intro path
    induction path with
    | @seed a present selected =>
      obtain rfl := beq_iff_eq.mp selected
      exact ⟨mem_verticesList.mp present, .refl a⟩
    | step _ present edge ih =>
      have hv := mem_verticesList.mp present
      exact ⟨hv, .extend ih.2 ⟨ih.1, hv, edge⟩⟩
  · rintro ⟨present, path⟩
    induction path with
    | refl => exact .seed (mem_verticesList.mpr present) (beq_iff_eq.mpr rfl)
    | extend _ edge ih =>
      exact .step (ih edge.1) (mem_verticesList.mpr edge.2.1) edge.2.2

private theorem verticesList_eq_filter {vertices : Fin n → Prop} {keep : Fin n → Bool}
    (agrees : ∀ v, vertices v ↔ keep v = true) :
    verticesList vertices = (List.finRange n).filter keep := by
  classical
  unfold verticesList
  apply List.filter_congr
  intro v _
  exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using agrees v)

theorem verticesList_district (G : MixedGraph n) (live : Fin n → Prop) (root : Fin n) :
    verticesList (FactorGraph.district G live root) = district G (verticesList live) root := by
  classical
  let keep := (district G (verticesList live) root).contains
  have canonical : district G (verticesList live) root = (List.finRange n).filter keep := by
    have bound : ∀ v, v ∈ district G (verticesList live) root → v ∈ verticesList live :=
      fun v h => ((mem_district_iff G (verticesList live) root v).mp h).in_current
    calc
      district G (verticesList live) root = (verticesList live).filter keep := by
        unfold district
        dsimp only
        symm
        apply List.filter_congr
        intro v h
        simp [keep, district, List.mem_filter, h]
      _ = (List.finRange n).filter keep := by
        unfold verticesList
        rw [List.filter_filter]
        apply List.filter_congr
        intro v _
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨And.left, fun h => ⟨h, mem_verticesList.mp
          (bound v (List.contains_iff_mem.mp h))⟩⟩
  rw [canonical]
  apply verticesList_eq_filter
  intro v
  exact (mem_list_district_iff (G := G) (live := live) (root := root) (v := v)).symm.trans
    List.contains_iff_mem.symm

theorem query_district_as_list (G : MixedGraph n) (q : Query n) (root : Fin n) :
    verticesList (q.district G root) = district G (verticesList (q.live G)) root :=
  verticesList_district G (q.live G) root

/-- Intrinsic sets are the nonempty bidirected-connected sets reachable
from the original random graph by fixing their complements. -/
def Intrinsic (G : MixedGraph n) (vertices : Fin n → Prop) : Prop :=
  (∃ v, vertices v) ∧ DistrictConnected G (verticesList vertices) ∧
    SetReachable G (List.finRange n) (verticesList vertices)

theorem query_component_identify_iff_intrinsic {G : MixedGraph n} {q : Query n} {root : Fin n}
    (rank : Fin n → Nat)
    (ranked : ∀ a b, G.edge a false b true = true → rank a < rank b)
    (liveRoot : q.live G root) :
    PlanSucceeds (identifyPlan G (verticesList (q.district G root)) root
      (district G (List.finRange n) root)) ↔ Intrinsic G (q.district G root) := by
  have rootMem : q.district G root root := ⟨liveRoot, .refl root⟩
  have connected : DistrictConnected G (verticesList (q.district G root)) := by
    rw [query_district_as_list]
    exact district_connected G (verticesList (q.live G)) root
  have components := component_identify_succeeds_iff_intrinsic (graph := G) rank ranked
    (source := List.finRange n) (fun {v} _ => List.mem_finRange v)
    (mem_verticesList.mpr rootMem) connected
  exact components.trans ⟨fun reach => ⟨⟨root, rootMem⟩, connected, reach⟩, fun intrinsic => intrinsic.2.2⟩

end

end OpenCausalScience.Papers.Tian2004.QueryIntrinsic
