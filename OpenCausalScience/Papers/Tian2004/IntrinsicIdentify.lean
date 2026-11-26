module
public import OpenCausalScience.Papers.TianPearl2003.IdentifyFixing
public import OpenCausalScience.Papers.RichardsonEtAl2023.Fixing

/-! # Identify and intrinsic fixing

The component kernel step in Tian (2004), Figure 3 calls Identify from
Figure 1 with the original district containing the target. Its graph
plan succeeds exactly when fixing the complement of the target is
possible. Ancestor reduction and district extraction both admit fixing
orders. A proper ancestor fixed point prevents every such order.

Sources:
https://arxiv.org/pdf/1207.4161#page=7
https://doi.org/10.1214/22-AOS2253
https://arxiv.org/abs/2307.03750
-/

namespace OpenCausalScience.Papers.Tian2004.IntrinsicIdentify

open TianPearl2003.IdentifyRecurrence TianPearl2003.IdentifyReachability
open TianPearl2003.IdentifyFixing Shpitser2023.FixedPointObstruction
open RichardsonEtAl2023.Fixing

@[expose] public section

variable {n : Nat}

/-- The plan reaches the target without visiting the original failure branch. -/
def PlanSucceeds : List (Instruction n) → Prop
  | [] => True
  | .marginalize _ _ :: rest => PlanSucceeds rest
  | .extractFactor _ _ :: rest => PlanSucceeds rest
  | .ancestorFixedPoint _ :: _ => False

/-- Reachability of a set does not depend on how its vertices are listed. -/
def SetReachable (graph : MixedGraph n) (current target : Vertices n) : Prop :=
  ∃ final, FixingOrder graph target current final ∧
    ∀ v, v ∈ final ↔ v ∈ target

private theorem appendReached {edge : Fin n → Fin n → Bool} {current : Vertices n}
    {seeds : Fin n → Bool} {join last : Fin n}
    (first : Reached edge current seeds join)
    (second : Reached edge current (· == join) last) :
    Reached edge current seeds last := by
  induction second with
  | seed _ selected => exact (beq_iff_eq.mp selected).symm ▸ first
  | step _ present next ih => exact .step ih present next

private def spouse (graph : MixedGraph n) (a b : Fin n) : Bool :=
  graph.edge a true b true

private theorem reverseSpouse {graph : MixedGraph n} {current : Vertices n}
    {first last : Fin n}
    (path : Reached (spouse graph) current (· == first) last) :
    Reached (spouse graph) current (· == last) first := by
  induction path with
  | @seed v present selected =>
    obtain rfl := beq_iff_eq.mp selected
    exact .seed present (beq_iff_eq.mpr rfl)
  | @step u v before currentV next ih =>
    have reverse : spouse graph v u = true := by
      simpa only [spouse, graph.symmetric v true u true] using next
    exact appendReached (.step (.seed currentV (beq_iff_eq.mpr rfl))
      before.in_current reverse) ih

private theorem pathInsideDistrict {graph : MixedGraph n} {current : Vertices n}
    {root last : Fin n} (path : Reached (spouse graph) current (· == root) last) :
    Reached (spouse graph) (district graph current root) (· == root) last := by
  induction path with
  | seed present selected =>
    exact .seed ((mem_district_iff graph current root _).mpr (.seed present selected)) selected
  | step before present edge ih =>
    exact .step ih ((mem_district_iff graph current root _).mpr (.step before present edge)) edge

private theorem memDistrictSelf (graph : MixedGraph n) {current : Vertices n}
    {root : Fin n} (present : root ∈ current) : root ∈ district graph current root :=
  (mem_district_iff graph current root root).mpr (.seed present (beq_iff_eq.mpr rfl))

theorem district_connected (graph : MixedGraph n) (current : Vertices n) (root : Fin n) :
    DistrictConnected graph (district graph current root) := by
  intro u hu v hv
  have toU := pathInsideDistrict ((mem_district_iff graph current root u).mp hu)
  have toV := pathInsideDistrict ((mem_district_iff graph current root v).mp hv)
  exact (mem_district_iff graph _ u v).mpr (appendReached (reverseSpouse toU) toV)

private theorem targetInDistrict {graph : MixedGraph n} {current target : Vertices n}
    {root : Fin n} (inside : target ⊆ current) (rootIn : root ∈ target)
    (connected : DistrictConnected graph target) :
    target ⊆ district graph current root := by
  intro v member
  exact (mem_district_iff graph current root v).mpr
    (Reached.extend_current inside
      ((mem_district_iff graph target root v).mp (connected root rootIn v member)))

private theorem rankIncreases {graph : MixedGraph n} {current : Vertices n}
    {rank : Fin n → Nat}
    (ranked : ∀ a b, graph.edge a false b true = true → rank a < rank b)
    {v w : Fin n} (path : descendant graph current v w) : v = w ∨ rank v < rank w := by
  induction path with
  | seed _ selected => exact .inl (beq_iff_eq.mp selected).symm
  | step _ _ arrow ih =>
    rcases ih with rfl | earlier
    · exact .inr (ranked _ _ arrow)
    · exact .inr (Nat.lt_trans earlier (ranked _ _ arrow))

private theorem highestRank (rank : Fin n → Nat) (vertices : Vertices n)
    (notEmpty : vertices ≠ []) : ∃ v ∈ vertices, ∀ w ∈ vertices, rank w ≤ rank v := by
  induction vertices with
  | nil => contradiction
  | cons head rest ih =>
    by_cases empty : rest = []
    · subst rest
      exact ⟨head, by simp, by simp⟩
    obtain ⟨v, present, bound⟩ := ih empty
    by_cases below : rank head ≤ rank v
    · exact ⟨v, List.mem_cons_of_mem head present, fun w member =>
        (List.mem_cons.mp member).elim (fun same => same ▸ below) (bound w)⟩
    · exact ⟨head, by simp, fun w member => (List.mem_cons.mp member).elim
        (fun same => same ▸ Nat.le_refl _) (fun p => Nat.le_trans (bound w p) (by omega))⟩

private theorem spouseClosed {graph : MixedGraph n} {current : Vertices n}
    (keep : Fin n → Bool)
    (closed : ∀ a ∈ current, ∀ b ∈ current, spouse graph a b = true →
      keep a = true → keep b = true)
    {root last : Fin n} (omitted : keep root = false)
    (path : Reached (spouse graph) current (· == root) last) :
    keep last = false := by
  induction path with
  | seed _ selected => simpa only [beq_iff_eq.mp selected] using omitted
  | @step a b before present next ih =>
    cases result : keep b with
    | false => rfl
    | true =>
      have reverse : spouse graph b a = true := by
        simpa only [spouse, graph.symmetric b true a true] using next
      exact False.elim (Bool.noConfusion (ih.symm.trans
        (closed b present a before.in_current reverse result)))

private theorem fixingToSpouseClosed {graph : MixedGraph n} {current : Vertices n}
    (keep : Fin n → Bool) (rank : Fin n → Nat)
    (ranked : ∀ a b, graph.edge a false b true = true → rank a < rank b)
    (closed : ∀ a ∈ current, ∀ b ∈ current,
      spouse graph a b = true → keep a = true → keep b = true) :
    FixingOrder graph (current.filter keep) current (current.filter keep) := by
  generalize targetEq : current.filter keep = target
  induction size : current.length using Nat.strongRecOn generalizing current with
  | ind size ih =>
    by_cases empty : current.filter (fun v => !keep v) = []
    · have all : current.filter keep = current := by
        apply List.filter_eq_self.mpr
        intro v present
        cases kept : keep v
        · have member : v ∈ current.filter (fun v => !keep v) := by
            simp [present, kept]
          simp [empty] at member
        · rfl
      rw [← targetEq, all]
      exact .empty current
    obtain ⟨v, member, highest⟩ := highestRank rank _ empty
    have present := (List.mem_filter.mp member).1
    have omitted : keep v = false := by simpa using (List.mem_filter.mp member).2
    have avoidsTarget : v ∉ target := by rw [← targetEq]; simp [omitted]
    have fixable : Fixable graph current v := by
      refine ⟨present, ?_⟩
      intro w distinct directed together
      have outside := spouseClosed keep closed omitted ((mem_district_iff graph current v w).mp together)
      have bounded := highest w (List.mem_filter.mpr ⟨directed.in_current, by simp [outside]⟩)
      have increasing := (rankIncreases ranked directed).resolve_left (Ne.symm distinct)
      omega
    apply FixingOrder.step fixable avoidsTarget
    have reduces : (current.filter (· != v)).length < current.length := by
      have le := List.length_filter_le (p := (· != v)) current
      apply Nat.lt_of_le_of_ne le
      intro sameLength
      have all := (List.length_filter_eq_length_iff.mp sameLength) v present
      simp at all
    refine ih _ (size ▸ reduces)
      (fun a ha b hb => closed a (List.mem_filter.mp ha).1 b (List.mem_filter.mp hb).1) ?_ rfl
    rw [← targetEq, List.filter_filter]
    apply List.filter_congr
    intro w _
    by_cases same : w = v
    · simp [same, omitted]
    · simp [bne_iff_ne.mpr same]

/-- Fix vertices outside the retained district in decreasing topological order. -/
theorem fixing_order_to_district {graph : MixedGraph n} {current : Vertices n}
    (root : Fin n) (rank : Fin n → Nat)
    (ranked : ∀ a b, graph.edge a false b true = true → rank a < rank b) :
    FixingOrder graph (district graph current root) current (district graph current root) := by
  have order := fixingToSpouseClosed (graph := graph) (current := current)
    (district graph current root).contains rank ranked (by
      intro a _ b hb edge kept
      exact List.contains_iff_mem.mpr ((mem_district_iff graph current root b).mpr
        (.step ((mem_district_iff graph current root a).mp (List.contains_iff_mem.mp kept)) hb edge)))
  have exactList : current.filter (district graph current root).contains = district graph current root := by
    unfold district
    dsimp only
    apply List.filter_congr
    intro v present
    simp [List.mem_filter, present]
  simpa only [exactList] using order

private theorem retarget {graph : MixedGraph n} {old new current final : Vertices n}
    (order : FixingOrder graph old current final) (inside : new ⊆ old) :
    FixingOrder graph new current final := by
  induction order with
  | empty current => exact .empty current
  | step fixable outside _ ih =>
    exact .step fixable (fun member => outside (inside member)) ih

private theorem appendFixings {graph : MixedGraph n} {target first mid final : Vertices n}
    (prefixOrder : FixingOrder graph target first mid)
    (suffixOrder : FixingOrder graph target mid final) :
    FixingOrder graph target first final := by
  induction prefixOrder with
  | empty => exact suffixOrder
  | step fixable outside _ ih => exact .step fixable outside (ih suffixOrder)

private theorem completeAfterPrefix {graph : MixedGraph n} {retainedTarget current middle target : Vertices n}
    (prefixOrder : FixingOrder graph retainedTarget current middle)
    (keeps : target ⊆ retainedTarget)
    (order : FixingOrder graph target current target) :
    FixingOrder graph target middle target := by
  induction prefixOrder with
  | empty => exact order
  | step fixable outside _ ih =>
    exact ih (reachable_after_fixable_choice order fixable (fun h => outside (keeps h)))

private theorem reachable_iff_after_fixing {graph : MixedGraph n}
    {target current middle : Vertices n} (prefixOrder : FixingOrder graph middle current middle)
    (keeps : target ⊆ middle) : SetReachable graph current target ↔ SetReachable graph middle target := by
  constructor
  · rintro ⟨final, order, members⟩
    have finalInside : final ⊆ middle := fun {v} h => keeps ((members v).mp h)
    have exactOrder : FixingOrder graph final current final :=
      retarget order (fun {v} h => (members v).mp h)
    refine ⟨final, retarget (completeAfterPrefix prefixOrder finalInside exactOrder) ?_, members⟩
    exact fun {v} h => (members v).mpr h
  · rintro ⟨final, order, members⟩
    exact ⟨final, appendFixings (retarget prefixOrder keeps) order, members⟩

private theorem sameVertices_iff_members {left right : Vertices n} :
    sameVertices left right = true ↔ ∀ v, v ∈ left ↔ v ∈ right := by
  constructor
  · intro same v
    obtain ⟨toRight, toLeft⟩ := Bool.and_eq_true_iff.mp same
    exact ⟨fun h => List.contains_iff_mem.mp (List.all_eq_true.mp toRight v h),
      fun h => List.contains_iff_mem.mp (List.all_eq_true.mp toLeft v h)⟩
  · intro members
    exact Bool.and_eq_true_iff.mpr
      ⟨List.all_eq_true.mpr (fun v h => List.contains_iff_mem.mpr ((members v).mp h)),
       List.all_eq_true.mpr (fun v h => List.contains_iff_mem.mpr ((members v).mpr h))⟩

private theorem targetInAncestors {graph : MixedGraph n} {current target : Vertices n}
    (inside : target ⊆ current) : target ⊆ ancestors graph current target := by
  intro v member
  exact (mem_ancestors_iff graph current target v).mpr
    (.seed (inside member) (List.contains_iff_mem.mpr member))

private theorem properFixedPoint {graph : MixedGraph n} {current target : Vertices n}
    (inside : target ⊆ current) (connected : DistrictConnected graph current)
    (fixed : ancestors graph current target = current)
    (different : sameVertices current target ≠ true) : ¬ SetReachable graph current target := by
  rintro ⟨final, order, members⟩
  have retained : current ⊆ final :=
    fixed_point_survives_fixing inside connected (fun v h => fixed.symm ▸ h) order (fun _ h => h)
  apply different
  exact sameVertices_iff_members.mpr
    (fun v => ⟨fun h => (members v).mp (retained h), fun h => inside h⟩)

/-- Identify on its original input district succeeds exactly for reachable targets. -/
theorem plan_succeeds_iff_reachable_from_district {graph : MixedGraph n}
    {current target : Vertices n} {root : Fin n}
    (rank : Fin n → Nat)
    (ranked : ∀ a b, graph.edge a false b true = true → rank a < rank b)
    (inside : target ⊆ current) (rootIn : root ∈ target)
    (targetConnected : DistrictConnected graph target)
    (currentConnected : DistrictConnected graph current) :
    PlanSucceeds (identifyPlan graph target root current) ↔ SetReachable graph current target := by
  induction size : current.length using Nat.strongRecOn generalizing current with
  | ind count ih =>
    let retained := ancestors graph current target
    let component := district graph retained root
    have ancestorFixings : FixingOrder graph retained current retained :=
      fixing_order_to_ancestors rank ranked
    have targetRetained : target ⊆ retained := targetInAncestors inside
    rw [identifyPlan]
    change PlanSucceeds
      (if sameVertices retained target then [.marginalize current retained]
       else if retained.length < current.length then
         .marginalize current retained :: .extractFactor retained component ::
           identifyPlan graph target root component
       else [.ancestorFixedPoint current]) ↔ SetReachable graph current target
    by_cases matching : sameVertices retained target = true
    · rw [ite_eq_left matching]
      exact ⟨fun _ => ⟨retained, retarget ancestorFixings targetRetained,
        sameVertices_iff_members.mp matching⟩, fun _ => trivial⟩
    rw [ite_eq_right matching]
    by_cases smaller : retained.length < current.length
    · rw [ite_eq_left smaller]
      change PlanSucceeds (identifyPlan graph target root component) ↔
        SetReachable graph current target
      have componentFixings : FixingOrder graph component retained component :=
        fixing_order_to_district root rank ranked
      have targetInsideComponent : target ⊆ component :=
        targetInDistrict targetRetained rootIn targetConnected
      have decreases : component.length < count :=
        size ▸ recursive_set_smaller graph current target root smaller
      have reduced := ih component.length decreases targetInsideComponent
        (district_connected graph retained root) rfl
      exact reduced.trans ((reachable_iff_after_fixing ancestorFixings targetRetained).trans
        (reachable_iff_after_fixing componentFixings targetInsideComponent)).symm
    · rw [ite_eq_right smaller]
      change False ↔ SetReachable graph current target
      have fixed : retained = current := ancestors_eq_current_of_no_decrease graph current target smaller
      have different : sameVertices current target ≠ true := fixed ▸ matching
      exact ⟨False.elim, properFixedPoint inside currentConnected fixed different⟩

/-- Starting with the original district instead of the full random graph
preserves reachability of a connected target. -/
theorem component_identify_succeeds_iff_intrinsic {graph : MixedGraph n}
    {source target : Vertices n} {root : Fin n}
    (rank : Fin n → Nat)
    (ranked : ∀ a b, graph.edge a false b true = true → rank a < rank b)
    (inside : target ⊆ source) (rootIn : root ∈ target)
    (connected : DistrictConnected graph target) :
    PlanSucceeds (identifyPlan graph target root (district graph source root)) ↔
      SetReachable graph source target := by
  have districtTarget := targetInDistrict inside rootIn connected
  exact (plan_succeeds_iff_reachable_from_district rank ranked districtTarget rootIn connected
    (district_connected graph source root)).trans
    (reachable_iff_after_fixing (fixing_order_to_district root rank ranked) districtTarget).symm

/-- A district from any induced subgraph is an admissible target for
Tian's original-district component call. -/
theorem restricted_district_identify_succeeds_iff_intrinsic {graph : MixedGraph n}
    {source restriction : Vertices n} {root : Fin n}
    (rank : Fin n → Nat)
    (ranked : ∀ a b, graph.edge a false b true = true → rank a < rank b)
    (inside : restriction ⊆ source) (rootIn : root ∈ restriction) :
    let target := district graph restriction root
    PlanSucceeds (identifyPlan graph target root (district graph source root)) ↔
      SetReachable graph source target := by
  dsimp only
  exact component_identify_succeeds_iff_intrinsic rank ranked
    (fun {v} h => inside ((mem_district_iff graph restriction root v).mp h).in_current)
    (memDistrictSelf graph rootIn) (district_connected graph restriction root)

end

end OpenCausalScience.Papers.Tian2004.IntrinsicIdentify
