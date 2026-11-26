module
public import OpenCausalScience.Papers.TianPearl2003.IdentifyRecurrence

/-! # Directed ancestry and c-components in Identify

Tian and Pearl (2003), R-290-L, Figure 7. The bounded closure used in
the graph plan is sound and complete for finite walks that stay within
the current free variables. In each nonstationary round its list
strictly increases inside the current list.
Source: https://ftp.cs.ucla.edu/pub/stat_ser/R290-L.pdf#page=26
-/

namespace OpenCausalScience.Papers.TianPearl2003.IdentifyReachability

open IdentifyRecurrence

@[expose] public section

variable {n : Nat}

/-- Reachability from a seed through edges within the current set. -/
inductive Reached (edge : Fin n → Fin n → Bool) (current : Vertices n)
    (seeds : Fin n → Bool) : Fin n → Prop
  | seed {v} : v ∈ current → seeds v = true → Reached edge current seeds v
  | step {u v} : Reached edge current seeds u → v ∈ current →
      edge u v = true → Reached edge current seeds v

theorem Reached.in_current {edge : Fin n → Fin n → Bool} {current : Vertices n}
    {seeds : Fin n → Bool} {v : Fin n} (h : Reached edge current seeds v) :
    v ∈ current := by cases h <;> assumption

private theorem advance_sublist (edge : Fin n → Fin n → Bool) (current : Vertices n)
    (pred : Fin n → Bool) :
    (current.filter pred).Sublist (advance edge current (current.filter pred)) := by
  let growth (v : Fin n) := (current.filter pred).contains v ||
    (current.filter pred).any (fun u => edge u v)
  change (current.filter pred).Sublist (current.filter growth)
  have keeps : (current.filter pred).filter growth = current.filter pred := by
    apply List.filter_eq_self.mpr
    intro v h
    exact Bool.or_eq_true_iff.mpr (.inl (List.contains_iff_mem.mpr h))
  have commute : (current.filter growth).filter pred = (current.filter pred).filter growth := by
    rw [List.filter_filter, List.filter_filter]
    exact congrArg (fun p => current.filter p) (funext fun v => Bool.and_comm _ _)
  rw [← keeps, ← commute]
  exact List.filter_sublist

private theorem close_preserves (edge : Fin n → Fin n → Bool) (current : Vertices n)
    (pred : Fin n → Bool) (rounds : Nat) :
    (current.filter pred).Sublist (close edge current (current.filter pred) rounds) := by
  induction rounds generalizing pred with
  | zero => exact List.Sublist.refl _
  | succ rounds ih =>
    rw [close]
    exact (advance_sublist edge current pred).trans (ih _)

private theorem close_eq_of_fixed (edge : Fin n → Fin n → Bool) (current visited : Vertices n)
    (fixed : advance edge current visited = visited) (rounds : Nat) :
    close edge current visited rounds = visited := by
  induction rounds with
  | zero => rfl
  | succ rounds ih => rwa [close, fixed]

private theorem close_stationary (edge : Fin n → Fin n → Bool) (current : Vertices n)
    (pred : Fin n → Bool) (rounds : Nat)
    (fit : current.length ≤ (current.filter pred).length + rounds) :
    advance edge current (close edge current (current.filter pred) rounds) =
      close edge current (current.filter pred) rounds := by
  induction rounds generalizing pred with
  | zero =>
    rw [close]
    have subset : (current.filter pred).Sublist current := List.filter_sublist
    have same := subset.eq_of_length (Nat.le_antisymm subset.length_le (by simpa using fit))
    rw [same]
    exact List.filter_eq_self.mpr fun v h =>
      Bool.or_eq_true_iff.mpr (.inl (List.contains_iff_mem.mpr h))
  | succ rounds ih =>
    let old := current.filter pred
    let next := advance edge current old
    by_cases same : next = old
    · have all := close_eq_of_fixed edge current old same (rounds + 1)
      rw [all]
      exact same
    · have subset : old.Sublist next := advance_sublist edge current pred
      have growth : old.length < next.length :=
        Nat.lt_of_le_of_ne subset.length_le (fun h => same (subset.eq_of_length h).symm)
      rw [close]
      have enough : current.length ≤ next.length + rounds := by
        change current.length ≤ old.length + (rounds + 1) at fit
        omega
      exact ih _ enough

private theorem close_sound (edge : Fin n → Fin n → Bool) (current : Vertices n)
    (seeds : Fin n → Bool) (visited : Vertices n) (rounds : Nat)
    (sound : ∀ v ∈ visited, Reached edge current seeds v) :
    ∀ v ∈ close edge current visited rounds, Reached edge current seeds v := by
  induction rounds generalizing visited with
  | zero => exact sound
  | succ rounds ih =>
    rw [close]
    apply ih
    intro v present
    obtain ⟨inside, move⟩ := List.mem_filter.mp present
    rcases Bool.or_eq_true_iff.mp move with prior | following
    · exact sound v (List.contains_iff_mem.mp prior)
    · obtain ⟨u, hu, arc⟩ := List.any_eq_true.mp following
      exact .step (sound u hu) inside arc

theorem mem_close_iff_reached (edge : Fin n → Fin n → Bool) (current : Vertices n)
    (seeds : Fin n → Bool) (v : Fin n) :
    v ∈ close edge current (current.filter seeds) current.length ↔
      Reached edge current seeds v := by
  constructor
  · intro present
    exact close_sound edge current seeds _ _ (fun w h =>
      .seed (List.mem_filter.mp h).1 (List.mem_filter.mp h).2) v present
  · let final := close edge current (current.filter seeds) current.length
    have fixed : advance edge current final = final := close_stationary edge current seeds _
      (Nat.le_add_left current.length _)
    intro reachable
    induction reachable with
    | seed inside marked =>
      exact (close_preserves edge current seeds _).subset (List.mem_filter.mpr ⟨inside, marked⟩)
    | step _ inside next ih =>
      change _ ∈ final
      rw [← fixed]
      exact List.mem_filter.mpr ⟨inside,
        Bool.or_eq_true_iff.mpr (.inr (List.any_eq_true.mpr ⟨_, ih, next⟩))⟩

theorem mem_ancestors_iff (graph : MixedGraph n) (current target : Vertices n) (v : Fin n) :
    v ∈ ancestors graph current target ↔
      Reached (fun u w => graph.edge w false u true) current target.contains v := by
  unfold ancestors
  rw [List.mem_filter, List.contains_iff_mem, mem_close_iff_reached]
  exact ⟨And.right, fun h => ⟨h.in_current, h⟩⟩

theorem mem_district_iff (graph : MixedGraph n) (current : Vertices n) (root v : Fin n) :
    v ∈ district graph current root ↔
      Reached (fun u w => graph.edge u true w true) current (· == root) v := by
  unfold district
  rw [List.mem_filter, List.contains_iff_mem, mem_close_iff_reached]
  exact ⟨And.right, fun h => ⟨h.in_current, h⟩⟩

theorem ancestors_closed_under_parents (graph : MixedGraph n) (current target : Vertices n)
    {u v : Fin n} (parent : graph.edge u false v true = true) (inside : u ∈ current)
    (child : v ∈ ancestors graph current target) : u ∈ ancestors graph current target :=
  (mem_ancestors_iff graph current target u).mpr
    (.step ((mem_ancestors_iff graph current target v).mp child) inside parent)

end

end OpenCausalScience.Papers.TianPearl2003.IdentifyReachability
