module
public import OpenCausalScience.Papers.Chickering1995.FindEdge

/-! The existence part of the covered-reversal transformation in
Chickering (UAI 1995), Theorem 2. Each step reverses an edge that
differs from the target orientation. -/

namespace OpenCausalScience.Papers.Chickering1995.Transformation

open Moralization Chickering1995.CoveredReversal Chickering1995.FindEdge
open OpenCausalScience.Papers.KimEtAl2026.BayesBallCorrectness
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n : Nat} {G H : DAG n} {a b : Fin n}

theorem sameDConnections_of_reversal (reversal : Reversal G H a b) :
    SameDConnections G H := by
  intro conditioned x y
  by_cases hx : conditioned x = false
  · by_cases hy : conditioned y = false
    · let Q : Query G := ⟨fun v => v == x, fun v => v == y,
        Conditioning.ofPredicate G conditioned⟩
      let T : Query H := ⟨fun v => v == x, fun v => v == y,
        Conditioning.ofPredicate H conditioned⟩
      have h := reversal.dConnection_iff Q T rfl rfl rfl
        (by intro v hv; obtain rfl := beq_iff_eq.mp hv; exact hx)
        (by intro v hv; obtain rfl := beq_iff_eq.mp hv; exact hy)
      simpa [Q, T, Query.DConnection] using h
    · exact iff_of_false (fun c => hy c.2.1) (fun c => hy c.2.1)
  · exact iff_of_false (fun c => hx c.1) (fun c => hx c.1)

private abbrev Endpoints (n : Nat) := Fin n × Fin n

private def arrows (n : Nat) : List (Endpoints n) :=
  (List.finRange n).flatMap (fun u => (List.finRange n).map (fun v => (u, v)))

private theorem mem_arrows (uv : Endpoints n) : uv ∈ arrows n := by
  exact List.mem_flatMap.mpr ⟨uv.1, List.mem_finRange _,
    List.mem_map.mpr ⟨uv.2, List.mem_finRange _, rfl⟩⟩

private def differs (G H : DAG n) (uv : Endpoints n) : Bool :=
  G.edge uv.1 uv.2 && H.edge uv.2 uv.1

private theorem differs_iff (uv : Endpoints n) :
    differs G H uv = true ↔ DifferingEdge G H uv.1 uv.2 := Bool.and_eq_true_iff

private def earlier (G : DAG n) (uv xy : Endpoints n) : Prop :=
  G.rank uv.2 < G.rank xy.2 ∨
    (G.rank uv.2 = G.rank xy.2 ∧ G.rank xy.1 ≤ G.rank uv.1)

private theorem earlier_refl (uv : Endpoints n) : earlier G uv uv :=
  .inr ⟨rfl, Nat.le_refl _⟩

private theorem earlier_total (uv xy : Endpoints n) : earlier G uv xy ∨ earlier G xy uv := by
  unfold earlier
  omega

private theorem earlier_trans {uv xy ab : Endpoints n}
    (first : earlier G uv xy) (second : earlier G xy ab) : earlier G uv ab := by
  unfold earlier at *
  omega

private theorem choose_earliest {edges : List (Endpoints n)} :
    edges ≠ [] → ∃ uv, uv ∈ edges ∧ ∀ xy, xy ∈ edges → earlier G uv xy := by
  induction edges with
  | nil => intro h; exact (h rfl).elim
  | cons head tail ih =>
    intro _
    by_cases empty : tail = []
    · subst tail
      exact ⟨head, .head _, fun xy h => by
        obtain rfl := List.mem_singleton.mp h
        exact earlier_refl _⟩
    · obtain ⟨best, mem, spec⟩ := ih empty
      rcases earlier_total (G := G) head best with first | second
      · refine ⟨head, .head _, fun xy h => ?_⟩
        rcases List.mem_cons.mp h with rfl | ht
        · exact earlier_refl _
        · exact earlier_trans first (spec xy ht)
      · refine ⟨best, .tail _ mem, fun xy h => ?_⟩
        rcases List.mem_cons.mp h with rfl | ht
        · exact second
        · exact spec xy ht

private theorem choose_find_edge (hasDifference : ∃ a b, DifferingEdge G H a b) :
    ∃ a b, DifferingEdge G H a b ∧
      (∀ u v, DifferingEdge G H u v → G.rank b ≤ G.rank v) ∧
      (∀ u, DifferingEdge G H u b → G.rank u ≤ G.rank a) := by
  let choices := (arrows n).filter (differs G H)
  have nonempty : choices ≠ [] := by
    obtain ⟨x, y, d⟩ := hasDifference
    have present : (x, y) ∈ choices :=
      List.mem_filter.mpr ⟨mem_arrows _, (differs_iff _).mpr d⟩
    intro empty
    simp [empty] at present
  obtain ⟨⟨a,b⟩, hab, best⟩ := choose_earliest (G := G) nonempty
  refine ⟨a,b,(differs_iff _).mp (List.mem_filter.mp hab).2, ?_, ?_⟩
  · intro u v diff
    rcases best (u,v) (List.mem_filter.mpr ⟨mem_arrows _, (differs_iff _).mpr diff⟩)
      with lt | ⟨eq, _⟩
    · exact Nat.le_of_lt lt
    · exact Nat.le_of_eq eq
  · intro u diff
    rcases best (u,b) (List.mem_filter.mpr ⟨mem_arrows _, (differs_iff _).mpr diff⟩)
      with lt | ⟨_, bound⟩
    · exact (Nat.lt_irrefl _ lt).elim
    · exact bound

private theorem new_differences {D : DAG n} (step : Reversal G D a b)
    (selected : DifferingEdge G H a b) {uv : Endpoints n} :
    differs D H uv = true → differs G H uv = true := by
  obtain ⟨u,v⟩ := uv
  intro difference
  obtain ⟨forward, opposite⟩ := (differs_iff _).mp difference
  by_cases removed : u = a ∧ v = b
  · obtain ⟨rfl, rfl⟩ := removed
    exact (D.no_directed_cycle _ (.extend (.single forward) step.reverse)).elim
  · by_cases added : u = b ∧ v = a
    · obtain ⟨rfl, rfl⟩ := added
      exact (H.no_directed_cycle _ (.extend (.single opposite) selected.2)).elim
    · exact (differs_iff _).mpr ⟨(step.unchanged _ _ removed added).mpr forward, opposite⟩

private theorem selected_is_removed {D : DAG n} (step : Reversal G D a b) :
    differs D H (a,b) ≠ true := by
  intro selected
  exact D.no_directed_cycle a (.extend (.single ((differs_iff _).mp selected).1) step.reverse)

private theorem count_le {α : Type} {f g : α → Bool}
    (subset : ∀ x, f x = true → g x = true) (items : List α) :
    items.countP f ≤ items.countP g := by
  induction items with
  | nil => exact Nat.le_refl 0
  | cons next _ ih =>
    rw [List.countP_cons, List.countP_cons]
    by_cases found : f next = true
    · simp [found, subset next found, ih]
    · simp [found]
      split <;> omega

private theorem count_lt {α : Type} {f g : α → Bool}
    (subset : ∀ x, f x = true → g x = true) {items : List α} {x : α}
    (mem : x ∈ items) (kept : g x = true) (removed : f x ≠ true) :
    items.countP f < items.countP g := by
  induction items with
  | nil => cases mem
  | cons first rest ih =>
    rw [List.countP_cons, List.countP_cons]
    rcases List.mem_cons.mp mem with rfl | tail
    · have bound := count_le subset rest
      simp [removed, kept]
      omega
    · have bound := ih tail
      by_cases found : f first = true
      · simp [found, subset first found, bound]
      · simp [found]
        split <;> omega

/-- A sequence of covered reversals toward a fixed target DAG. Each step
agrees with the target on the edge just reversed. Ranks may differ
between equivalent representations of the final edge function. -/
inductive ReversalSequence (target : DAG n) : DAG n → Prop
  | done {D} : D.edge = target.edge → ReversalSequence target D
  | next {D E u v} : DifferingEdge D target u v → Reversal D E u v →
      ReversalSequence target E → ReversalSequence target D

/-- For two DAGs with the same d-separations, covered reversals of
differing orientations suffice to reach the target edge function. -/
theorem reversal_sequence (same : SameDConnections G H) : ReversalSequence H G := by
  suffices aux : ∀ k (D : DAG n), (arrows n).countP (differs D H) = k →
      SameDConnections D H → ReversalSequence H D by
    exact aux _ G rfl same
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro D count sameD
    have sk := sameSkeleton_of_sameDConnections sameD
    by_cases existsDiff : ∃ a b, DifferingEdge D H a b
    · obtain ⟨a,b,selected,firstHead,lastParent⟩ := choose_find_edge existsDiff
      have parents := parents_of_find_edge sk (sameUnshieldedColliders_of_sameDConnections sameD)
        selected firstHead lastParent
      let E := Reversal.flip D a b selected.1 parents
      have step : Reversal D E a b :=
        Reversal.flip_is_covered_reversal D a b selected.1 parents
      have less : (arrows n).countP (differs E H) < k := count ▸
        count_lt (fun _ => new_differences step selected) (mem_arrows (a,b))
          ((differs_iff _).mpr selected) (selected_is_removed step)
      apply ReversalSequence.next selected step
      exact ih _ less E rfl (fun C x y => (sameDConnections_of_reversal step C x y).symm.trans (sameD C x y))
    · apply ReversalSequence.done
      funext x y
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro xy
        rcases (sk x y).mp (.inl xy) with h | h
        · exact h
        · exact (existsDiff ⟨x,y,xy,h⟩).elim
      · intro xy
        rcases (sk x y).mpr (.inl xy) with h | h
        · exact h
        · exact (existsDiff ⟨y,x,h,xy⟩).elim

end
end OpenCausalScience.Papers.Chickering1995.Transformation
