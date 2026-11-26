module
public import OpenCausalScience.Papers.Shpitser2023.FixedPointObstruction

/-! # Ancestor reduction by graphical fixing

The ancestor-marginalization step of Tian and Pearl's Identify has a
graphical counterpart. On a directed acyclic mixed graph, one can fix
the omitted vertices in reverse topological order while retaining every
ancestor of the target.

Source: https://ftp.cs.ucla.edu/pub/stat_ser/R290-L.pdf#page=26
-/

namespace OpenCausalScience.Papers.TianPearl2003.IdentifyFixing

open IdentifyRecurrence IdentifyReachability
open OpenCausalScience.Papers.Shpitser2023.FixedPointObstruction

@[expose] public section

variable {n : Nat}

private theorem rank_increases_on_descendants {graph : MixedGraph n}
    {current : Vertices n} {rank : Fin n → Nat}
    (ranked : ∀ a b, graph.edge a false b true = true → rank a < rank b)
    {v w : Fin n} (path : descendant graph current v w) :
    v = w ∨ rank v < rank w := by
  induction path with
  | seed _ selected => exact .inl (beq_iff_eq.mp selected).symm
  | step _ _ arrow ih =>
    rcases ih with rfl | earlier
    · exact .inr (ranked _ _ arrow)
    · exact .inr (Nat.lt_trans earlier (ranked _ _ arrow))

private theorem highest_rank (rank : Fin n → Nat) (vertices : Vertices n)
    (nonempty : vertices ≠ []) :
    ∃ v ∈ vertices, ∀ w ∈ vertices, rank w ≤ rank v := by
  induction vertices with
  | nil => contradiction
  | cons x xs ih =>
    by_cases empty : xs = []
    · subst xs
      exact ⟨x, by simp, by simp⟩
    obtain ⟨v, present, bound⟩ := ih empty
    by_cases below : rank x ≤ rank v
    · exact ⟨v, List.mem_cons_of_mem x present, fun w h =>
        (List.mem_cons.mp h).elim (fun h => h ▸ below) (bound w)⟩
    · exact ⟨x, by simp, fun w h => (List.mem_cons.mp h).elim
        (fun h => h ▸ Nat.le_refl _) (fun p => Nat.le_trans (bound w p) (by omega))⟩

theorem fixing_order_to_parent_closed {graph : MixedGraph n} {current : Vertices n}
    (keep : Fin n → Bool) (rank : Fin n → Nat)
    (ranked : ∀ a b, graph.edge a false b true = true → rank a < rank b)
    (closed : ∀ a ∈ current, ∀ b ∈ current,
      graph.edge a false b true = true → keep b = true → keep a = true) :
    FixingOrder graph (current.filter keep) current (current.filter keep) := by
  generalize targetEq : current.filter keep = target
  induction size : current.length using Nat.strongRecOn generalizing current with
  | ind size ih =>
    by_cases empty : current.filter (fun x => !keep x) = []
    · have targetAll : current.filter keep = current := by
        apply List.filter_eq_self.mpr
        intro v present
        cases omitted : keep v
        ·
          have member : v ∈ current.filter (fun x => !keep x) :=
            List.mem_filter.mpr ⟨present, by simp [omitted]⟩
          simp [empty] at member
        · rfl
      rw [← targetEq, targetAll]
      exact .empty current
    obtain ⟨v, member, highest⟩ := highest_rank rank _ empty
    have present := (List.mem_filter.mp member).1
    have omitted : keep v = false := by simpa using (List.mem_filter.mp member).2
    have avoidsTarget : v ∉ target := by
      rw [← targetEq]
      simp [omitted]
    have fixable : Fixable graph current v := by
      refine ⟨present, ?_⟩
      intro w different path sameDistrict
      have outside : keep w = false := by
        clear different sameDistrict
        induction path with
        | seed _ selected =>
          rw [beq_iff_eq.mp selected]
          exact omitted
        | @step x z pathPrefix inside arrow before =>
          cases outcome : keep z with
          | false => rfl
          | true =>
            have clash := closed x pathPrefix.in_current z inside arrow outcome
            exact False.elim (Bool.noConfusion (before.symm.trans clash))
      have bounded := highest w (List.mem_filter.mpr ⟨path.in_current, by simp [outside]⟩)
      have increasing := (rank_increases_on_descendants ranked path).resolve_left (Ne.symm different)
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

theorem fixing_order_to_ancestors {graph : MixedGraph n} {current target : Vertices n}
    (rank : Fin n → Nat)
    (ranked : ∀ a b, graph.edge a false b true = true → rank a < rank b) :
    FixingOrder graph (ancestors graph current target) current
      (ancestors graph current target) := by
  have order := fixing_order_to_parent_closed (graph := graph) (current := current)
    (ancestors graph current target).contains rank ranked (by
      intro a ha b _ edge member
      exact List.contains_iff_mem.mpr
        (ancestors_closed_under_parents graph current target edge ha
          (List.contains_iff_mem.mp member)))
  have exactList : current.filter (ancestors graph current target).contains =
      ancestors graph current target := by
    unfold ancestors
    dsimp only
    apply List.filter_congr
    intro v present
    simp [List.mem_filter, present]
  simpa only [exactList] using order

end
end OpenCausalScience.Papers.TianPearl2003.IdentifyFixing
