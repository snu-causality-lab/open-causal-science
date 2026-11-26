module
public import OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

/-! # Orientations with a prescribed initial clique

A finite DAG with no unshielded colliders admits an orientation of its
skeleton that puts any chosen clique first. In particular, each edge of
such a skeleton can be oriented either way. This supplies the orientations
starting at a chosen vertex used in the proof of Proposition 4.1 of
[Andersson, Madigan and Perlman (1997)](https://doi.org/10.1214/aos/1031833662).
-/

namespace OpenCausalScience.Papers.AnderssonEtAl1997.PerfectOrientation

open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n : Nat}

/-- The order orients each edge from lower to higher rank. The earlier
neighbors of any vertex form a clique. -/
private structure PerfectOrder (G : DAG n) (active first : Fin n → Prop)
    (preferred : Fin n → Nat) where
  rank : Fin n → Nat
  bound : Nat
  bounded : ∀ {v}, active v → rank v < bound
  injective : ∀ {u v}, active u → active v → rank u = rank v → u = v
  initial : ∀ {u v}, active u → active v → first u → ¬ first v → rank u < rank v
  respects : ∀ {u v}, active u → active v → first u → first v →
    preferred u < preferred v → rank u < rank v
  shielded : ∀ {x z y}, active x → active z → active y →
    Adjacent G x z → Adjacent G y z → rank x < rank z → rank y < rank z →
    x ≠ y → Adjacent G x y

private def priority (rank : Fin n → Nat) (v : Fin n) : Nat := n * rank v + v.val

private theorem priority_lt_of_rank_lt {rank : Fin n → Nat} {u v : Fin n}
    (ordered : rank u < rank v) : priority rank u < priority rank v := by
  have upper := Nat.mul_le_mul_left n (Nat.succ_le_of_lt ordered)
  rw [Nat.mul_succ] at upper
  have uBound := u.isLt
  unfold priority
  omega

private theorem eq_of_priority_eq {rank : Fin n → Nat} {u v : Fin n}
    (same : priority rank u = priority rank v) : u = v := by
  rcases Nat.lt_trichotomy (rank u) (rank v) with lower | equal | higher
  · exact ((Nat.ne_of_lt (priority_lt_of_rank_lt lower)) same).elim
  · apply Fin.ext
    simpa [priority, equal] using same
  · exact ((Nat.ne_of_lt (priority_lt_of_rank_lt higher)) same.symm).elim

private theorem exists_priority_bound (rank : Fin n → Nat) :
    ∃ bound, ∀ v, priority rank v < bound := by
  let priorities := 0 :: (List.finRange n).map (priority rank)
  have nonempty : priorities ≠ [] := List.cons_ne_nil _ _
  refine ⟨priorities.max nonempty + 1, fun v => Nat.lt_succ_of_le ?_⟩
  exact List.le_max_of_mem (List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_finRange v)))

private theorem neighbors_of_sink_adjacent {G : DAG n} {active : Fin n → Prop} {s : Fin n}
    (noColliders : ∀ x z y, ¬ UnshieldedCollider G x z y)
    (sink : ∀ v, active v → G.edge s v ≠ true)
    {x y : Fin n} (ax : active x) (ay : active y)
    (xs : Adjacent G x s) (ys : Adjacent G y s) (different : x ≠ y) :
    Adjacent G x y := by
  apply Classical.byContradiction
  intro missing
  exact noColliders x s y ⟨different, missing, xs.resolve_right (sink x ax),
    ys.resolve_right (sink y ay)⟩

/-- Restore a sink after every retained vertex. -/
private def appendSink {G : DAG n} {active first : Fin n → Prop}
    {preferred : Fin n → Nat} {s : Fin n}
    (outside : ¬ first s)
    (neighbors : ∀ {x y}, active x → active y → Adjacent G x s → Adjacent G y s →
      x ≠ y → Adjacent G x y)
    (old : PerfectOrder G (fun v => active v ∧ v ≠ s) first preferred) :
    PerfectOrder G active first preferred := by
  let rank (v : Fin n) := if v = s then old.bound else old.rank v
  have before {v} (av : active v) (distinct : v ≠ s) : rank v < rank s := by
    simpa [rank, distinct] using old.bounded ⟨av, distinct⟩
  refine ⟨rank, old.bound + 1, ?_, ?_, ?_, ?_, ?_⟩
  · intro v av
    by_cases same : v = s
    · simp [rank, same]
    · exact Nat.lt_succ_of_lt (by simpa [rank, same] using old.bounded ⟨av, same⟩)
  · intro u v au av equal
    by_cases us : u = s
    · subst u
      apply Classical.byContradiction
      intro different
      exact (Nat.ne_of_lt (before av (Ne.symm different))) equal.symm
    · have vs : v ≠ s := by
        rintro rfl
        exact (Nat.ne_of_lt (before au us)) equal
      exact old.injective ⟨au, us⟩ ⟨av, vs⟩ (by simpa [rank, us, vs] using equal)
  · intro u v au av firstU notFirstV
    have us : u ≠ s := fun same => outside (same ▸ firstU)
    by_cases vs : v = s
    · subst v
      exact before au us
    · simpa [rank, us, vs] using old.initial ⟨au, us⟩ ⟨av, vs⟩ firstU notFirstV
  · intro u v au av fu fv earlier
    have us : u ≠ s := fun same => outside (same ▸ fu)
    have vs : v ≠ s := fun same => outside (same ▸ fv)
    simpa [rank, us, vs] using old.respects ⟨au, us⟩ ⟨av, vs⟩ fu fv earlier
  · intro x z y ax az ay xz yz lowerX lowerY different
    by_cases zs : z = s
    · subst z
      exact neighbors ax ay xz yz different
    · have xs : x ≠ s := by
        rintro rfl
        exact (Nat.not_lt_of_ge (Nat.le_of_lt (before az zs))) lowerX
      have ys : y ≠ s := by
        rintro rfl
        exact (Nat.not_lt_of_ge (Nat.le_of_lt (before az zs))) lowerY
      exact old.shielded ⟨ax, xs⟩ ⟨az, zs⟩ ⟨ay, ys⟩ xz yz
        (by simpa [rank, xs, zs] using lowerX) (by simpa [rank, ys, zs] using lowerY) different

/-- Restore a sink next to its neighbors at the start of the order. Reorder
this clique with the prescribed vertices first. -/
private noncomputable def prependClique {G : DAG n} {active first : Fin n → Prop}
    {preferred : Fin n → Nat} {s : Fin n} {width : Nat}
    (priorityBound : ∀ v, priority preferred v < width)
    (firstInClique : ∀ {v}, first v → v = s ∨ Adjacent G v s)
    (neighbors : ∀ {x y}, active x → active y → Adjacent G x s → Adjacent G y s →
      x ≠ y → Adjacent G x y)
    (old : PerfectOrder G (fun v => active v ∧ v ≠ s)
      (fun v => active v ∧ Adjacent G v s) preferred) :
    PerfectOrder G active first preferred := by
  classical
  let inside (v : Fin n) := v = s ∨ Adjacent G v s
  let rank (v : Fin n) :=
    if first v then priority preferred v else if inside v then width + v.val
    else width + n + old.rank v
  have insideBound {v} (h : inside v) : rank v < width + n := by
    have vBound := v.isLt
    have keyBound := priorityBound v
    by_cases fv : first v <;> simp [rank, fv, h] <;> omega
  have outsideRank {v} (h : ¬ inside v) : rank v = width + n + old.rank v := by
    have notFirst : ¬ first v := fun fv => h (firstInClique fv)
    simp [rank, h, notFirst]
  have outsideNe {v} (h : ¬ inside v) : v ≠ s := fun same => h (.inl same)
  have earlierInside {u v} (order : rank u < rank v) (hv : inside v) : inside u := by
    apply Classical.byContradiction
    intro hu
    have uv := insideBound hv
    rw [outsideRank hu] at order
    omega
  have withinClique {u v} (au : active u) (av : active v)
      (hu : inside u) (hv : inside v) (different : u ≠ v) : Adjacent G u v := by
    rcases hu with rfl | us
    · exact Or.symm (hv.resolve_left different.symm)
    · rcases hv with rfl | vs
      · exact us
      · exact neighbors au av us vs different
  have oldEarlier {u v} (au : active u) (av : active v) (hv : ¬ inside v)
      (adjacent : Adjacent G u v) (order : rank u < rank v) :
      u ≠ s ∧ old.rank u < old.rank v := by
    have us : u ≠ s := by
      rintro rfl
      exact hv (.inr (Or.symm adjacent))
    refine ⟨us, ?_⟩
    by_cases hu : inside u
    · exact old.initial ⟨au, us⟩ ⟨av, outsideNe hv⟩ ⟨au, hu.resolve_left us⟩
        (fun vs => hv (.inr vs.2))
    · rw [outsideRank hu, outsideRank hv] at order
      omega
  refine ⟨rank, width + n + old.bound, ?_, ?_, ?_, ?_, ?_⟩
  · intro v av
    by_cases hv : inside v
    · have bound := insideBound hv
      omega
    · rw [outsideRank hv]
      have bound := old.bounded ⟨av, outsideNe hv⟩
      omega
  · intro u v au av equal
    by_cases hu : inside u
    · have hv : inside v := by
        apply Classical.byContradiction
        intro hv
        have bound := insideBound hu
        rw [outsideRank hv] at equal
        omega
      have keyU := priorityBound u
      have keyV := priorityBound v
      by_cases fu : first u <;> by_cases fv : first v
      · exact eq_of_priority_eq (by simpa [rank, fu, fv] using equal)
      · simp [rank, fu, fv, hv] at equal
        omega
      · simp [rank, fu, fv, hu] at equal
        omega
      · apply Fin.ext
        simp [rank, fu, fv, hu, hv] at equal
        omega
    · have hv : ¬ inside v := by
        intro hv
        have bound := insideBound hv
        rw [outsideRank hu] at equal
        omega
      rw [outsideRank hu, outsideRank hv] at equal
      exact old.injective ⟨au, outsideNe hu⟩ ⟨av, outsideNe hv⟩ (by omega)
  · intro u v _ _ fu fv
    have keyBound := priorityBound u
    by_cases hv : inside v <;> simp [rank, fu, fv, hv] <;> omega
  · intro u v _ _ fu fv before
    simpa [rank, fu, fv] using priority_lt_of_rank_lt before
  · intro x z y ax az ay xz yz lowerX lowerY different
    by_cases hz : inside z
    · exact withinClique ax ay (earlierInside lowerX hz) (earlierInside lowerY hz) different
    · obtain ⟨xs, oldLowerX⟩ := oldEarlier ax az hz xz lowerX
      obtain ⟨ys, oldLowerY⟩ := oldEarlier ay az hz yz lowerY
      exact old.shielded ⟨ax, xs⟩ ⟨az, outsideNe hz⟩ ⟨ay, ys⟩ xz yz
        oldLowerX oldLowerY different

/-- Remove the last active vertex in the original topological order. Its
remaining neighbors are parents and therefore form a clique. -/
private theorem exists_perfectOrder {G : DAG n}
    (noColliders : ∀ x z y, ¬ UnshieldedCollider G x z y)
    (preferred : Fin n → Nat) (width : Nat)
    (priorityBound : ∀ v, priority preferred v < width)
    (budget : Nat) (active first : Fin n → Prop)
    (bounded : ∀ v, active v → priority G.rank v < budget)
    (included : ∀ v, first v → active v)
    (clique : ∀ u v, first u → first v → u ≠ v → Adjacent G u v) :
    Nonempty (PerfectOrder G active first preferred) := by
  classical
  induction budget generalizing active first with
  | zero =>
    have empty {v} (av : active v) : False := Nat.not_lt_zero _ (bounded v av)
    exact ⟨⟨fun _ => 0, 0, fun av => (empty av).elim, fun au _ _ => (empty au).elim,
      fun au _ _ _ => (empty au).elim, fun au _ _ _ _ => (empty au).elim,
      fun ax _ _ _ _ _ _ _ => (empty ax).elim⟩⟩
  | succ budget ih =>
    by_cases attained : ∃ s, active s ∧ priority G.rank s = budget
    · obtain ⟨s, activeS, maximal⟩ := attained
      have smaller v (av : active v ∧ v ≠ s) : priority G.rank v < budget := by
        have upper := bounded v av.1
        have different : priority G.rank v ≠ priority G.rank s := fun same => av.2 (eq_of_priority_eq same)
        omega
      have sink v (av : active v) (edge : G.edge s v = true) : False := by
        have lower := priority_lt_of_rank_lt (G.edge_increases s v edge)
        have upper := bounded v av
        omega
      have neighbors {x y} (ax : active x) (ay : active y) (xs : Adjacent G x s)
          (ys : Adjacent G y s) (different : x ≠ y) : Adjacent G x y :=
        neighbors_of_sink_adjacent noColliders sink ax ay xs ys different
      by_cases firstS : first s
      · let parents (v : Fin n) := active v ∧ Adjacent G v s
        have parentIncluded v (pv : parents v) : active v ∧ v ≠ s := by
          refine ⟨pv.1, ?_⟩
          intro same
          subst v
          exact sink s activeS (pv.2.elim id id)
        obtain ⟨old⟩ := ih (fun v => active v ∧ v ≠ s) parents smaller parentIncluded
          (fun _ _ px py => neighbors px.1 py.1 px.2 py.2)
        have firstInClique {v} (fv : first v) : v = s ∨ Adjacent G v s := by
          by_cases vs : v = s
          · exact .inl vs
          · exact .inr (clique v s fv firstS vs)
        exact ⟨prependClique priorityBound firstInClique neighbors old⟩
      · obtain ⟨old⟩ := ih (fun v => active v ∧ v ≠ s) first smaller
          (fun v fv => ⟨included v fv, fun same => firstS (same ▸ fv)⟩) clique
        exact ⟨appendSink firstS neighbors old⟩
    · apply ih active first _ included clique
      intro v av
      have upper := bounded v av
      have ne : priority G.rank v ≠ budget := fun eq => attained ⟨v, av, eq⟩
      omega

/-- A finite DAG whose colliders are all shielded admits a DAG with the same
skeleton and no unshielded colliders. Every member of a chosen clique
precedes every vertex outside it. Each clique edge points from lower to
higher supplied priority whenever the priorities differ. -/
theorem exists_orientation_with_ordered_initial_clique {G : DAG n}
    (noColliders : ∀ x z y, ¬ UnshieldedCollider G x z y) (first : Fin n → Prop)
    (clique : ∀ u v, first u → first v → u ≠ v → Adjacent G u v)
    (preferred : Fin n → Nat) :
    ∃ H : DAG n, (∀ u v, Adjacent G u v ↔ Adjacent H u v) ∧
      (∀ x z y, ¬ UnshieldedCollider H x z y) ∧
      (∀ u v, first u → ¬ first v → H.rank u < H.rank v) ∧
      (∀ u v, first u → first v → preferred u < preferred v → Adjacent G u v →
        H.edge u v = true) := by
  classical
  obtain ⟨width, priorityBound⟩ := exists_priority_bound preferred
  obtain ⟨budget, bounded⟩ := exists_priority_bound G.rank
  obtain ⟨order⟩ := exists_perfectOrder noColliders preferred width priorityBound budget
    (fun _ => True) first (fun v _ => bounded v) (fun _ _ => trivial) clique
  let H : DAG n :=
    ⟨fun u v => decide (Adjacent G u v ∧ order.rank u < order.rank v),
      order.rank, fun _ _ edge => (of_decide_eq_true edge).2⟩
  have edge_iff (u v) : H.edge u v = true ↔ Adjacent G u v ∧ order.rank u < order.rank v :=
    decide_eq_true_iff
  have skeleton (u v) : Adjacent G u v ↔ Adjacent H u v := by
    constructor
    · intro adj
      rcases Nat.lt_trichotomy (order.rank u) (order.rank v) with before | equal | after
      · exact .inl ((edge_iff u v).mpr ⟨adj, before⟩)
      · have same := order.injective (u := u) (v := v) trivial trivial equal
        subst v
        exact (G.no_directed_cycle u (.single (adj.elim id id))).elim
      · exact .inr ((edge_iff v u).mpr ⟨Or.symm adj, after⟩)
    · intro adj
      exact adj.elim (fun e => ((edge_iff u v).mp e).1)
        (fun e => Or.symm ((edge_iff v u).mp e).1)
  refine ⟨H, skeleton, ?_, fun _ _ => order.initial trivial trivial,
    fun u v fu fv before adj => (edge_iff u v).mpr
      ⟨adj, order.respects trivial trivial fu fv before⟩⟩
  intro x z y collider
  have xz := (edge_iff x z).mp collider.2.2.1
  have yz := (edge_iff y z).mp collider.2.2.2
  exact collider.2.1 ((skeleton x y).mp
    (order.shielded trivial trivial trivial xz.1 yz.1 xz.2 yz.2 collider.1))

/-- Every member of a chosen clique can precede every vertex outside it
while preserving the skeleton and keeping all colliders shielded. -/
theorem exists_orientation_with_initial_clique {G : DAG n}
    (noColliders : ∀ x z y, ¬ UnshieldedCollider G x z y) (first : Fin n → Prop)
    (clique : ∀ u v, first u → first v → u ≠ v → Adjacent G u v) :
    ∃ H : DAG n, (∀ u v, Adjacent G u v ↔ Adjacent H u v) ∧
      (∀ x z y, ¬ UnshieldedCollider H x z y) ∧
      (∀ u v, first u → ¬ first v → H.rank u < H.rank v) := by
  obtain ⟨H, skeleton, shielded, initial, _⟩ :=
    exists_orientation_with_ordered_initial_clique noColliders first clique (fun _ => 0)
  exact ⟨H, skeleton, shielded, initial⟩

/-- A chosen vertex can be a source while preserving the skeleton and
keeping all colliders shielded. -/
theorem exists_orientation_with_source {G : DAG n}
    (noColliders : ∀ x z y, ¬ UnshieldedCollider G x z y) (a : Fin n) :
    ∃ H : DAG n, (∀ u v, Adjacent G u v ↔ Adjacent H u v) ∧
      (∀ x z y, ¬ UnshieldedCollider H x z y) ∧ (∀ u, H.edge u a = false) := by
  obtain ⟨H, skeleton, shielded, first⟩ := exists_orientation_with_initial_clique noColliders
    (fun v => v = a) (fun _ _ ua va distinct => (distinct (ua.trans va.symm)).elim)
  refine ⟨H, skeleton, shielded, fun u => Bool.eq_false_iff.mpr ?_⟩
  intro incoming
  have before := H.edge_increases _ _ incoming
  have different : u ≠ a := by
    rintro rfl
    exact Nat.lt_irrefl _ before
  exact Nat.not_lt_of_ge (Nat.le_of_lt (first a u rfl different)) before

/-- Every skeleton edge can be oriented in the prescribed direction while
preserving the skeleton and keeping all colliders shielded. -/
theorem exists_orientation_of_adjacent {G : DAG n}
    (noColliders : ∀ x y z, ¬ UnshieldedCollider G x y z) {a b : Fin n}
    (adj : Adjacent G a b) :
    ∃ H : DAG n, (∀ x y, Adjacent G x y ↔ Adjacent H x y) ∧
      (∀ x y z, ¬ UnshieldedCollider H x y z) ∧ H.edge a b = true := by
  obtain ⟨H, skeleton, shielded, source⟩ := exists_orientation_with_source noColliders a
  exact ⟨H, skeleton, shielded,
    ((skeleton a b).mp adj).resolve_right (Bool.eq_false_iff.mp (source b))⟩

end
end OpenCausalScience.Papers.AnderssonEtAl1997.PerfectOrientation
