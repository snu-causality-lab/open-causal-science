module
public import OpenCausalScience.Papers.Runge2021.OSet

/-! # Forbidden-set avoidance for the O-set

Runge (2021), arXiv:2102.10324v4, Lemma B.3 and the first part of the
validity proof in Appendix B.7. We prove avoidance of the forbidden set
for an acyclic directed part with fixed conditioning variables that are
nondescendants of the treatment. For the treatment itself as a potential
collider parent, these premises give a direct proof of exclusion. The
noncausal-path blocking condition is an additional proof obligation.

Source: https://arxiv.org/html/2102.10324v4#App.B.SS7.
-/

namespace OpenCausalScience.Papers.Runge2021.OSetForbidden

open OpenCausalScience.Papers.Runge2021.OSet

@[expose] public section

variable {n : Nat}

private theorem reach_to_child {graph : MixedGraph n} {a b c : Fin n}
    (reaches : DirectedReach graph a b) (edge : graph.edge b false c true = true) :
    DirectedReach graph a c := by
  induction reaches with
  | @conditioned v atEnd =>
    have same : v = b := by simpa using atEnd
    subst v
    exact .parent edge (.conditioned (by simp))
  | parent first _ ih => exact .parent first ih

private theorem reach_rank_le {graph : MixedGraph n} {rank : Fin n → Nat}
    (increases : ∀ a b, graph.edge a false b true = true → rank a < rank b)
    {a b : Fin n} (reaches : DirectedReach graph a b) : rank a ≤ rank b := by
  induction reaches with
  | @conditioned v atEnd =>
    have same : v = b := by simpa using atEnd
    subst v
    exact Nat.le_refl _
  | parent edge _ ih => exact Nat.le_trans (Nat.le_of_lt (increases _ _ edge)) ih

private theorem reaches_conditioning_vertex {graph : MixedGraph n} {mask : Fin n → Bool}
    {u : Fin n} (reaches : graph.AncestorOf mask u) :
    ∃ w, mask w = true ∧ DirectedReach graph u w := by
  induction reaches with
  | conditioned member => exact ⟨_, member, .conditioned (by simp)⟩
  | parent edge _ ih =>
    obtain ⟨w, member, tail⟩ := ih
    exact ⟨w, member, .parent edge tail⟩

private theorem treatment_not_collider_parent {graph : MixedGraph n} {rank : Fin n → Nat}
    (increases : ∀ a b, graph.edge a false b true = true → rank a < rank b)
    {x y c : Fin n} {fixed : Fin n → Bool}
    (fixedPretreatment : ∀ v, fixed v = true → ¬ DirectedReach graph x v)
    (collider : Collider graph x y fixed c) (edge : graph.edge x false c true = true) : False := by
  have eligible := collider_eligible collider
  have cNeX : c ≠ x := by
    intro same
    exact eligible.1 (.inl same)
  rcases eligible.2 with validAncestor | separated
  · obtain ⟨w, member, reaches⟩ := reaches_conditioning_vertex validAncestor.1
    simp only [Bool.or_eq_true, beq_iff_eq] at member
    rcases member with (rfl | rfl) | fixedMember
    · exact (Nat.not_lt_of_ge (reach_rank_le increases reaches)) (increases _ _ edge)
    · have xReachesC : DirectedReach graph x c := .parent edge (.conditioned (by simp))
      exact eligible.1 (.inr ⟨c, .inr ⟨cNeX, xReachesC, reaches⟩, .conditioned (by simp)⟩)
    · exact fixedPretreatment w fixedMember (.parent edge reaches)
  · apply separated
    have backwards : graph.edge c true x false = true := (graph.symmetric _ _ _ _).trans edge
    exact ⟨c, true, (x, false), [], (x, false), by simp, backwards, .nil _, by simp,
      by simp [cNeX]⟩

/-- The first conjunct of the O-set validity proof, for the graph domain
with a topological ranking and pretreatment fixed conditions. -/
theorem o_set_avoids_forbidden (graph : MixedGraph n) (rank : Fin n → Nat)
    (increases : ∀ a b, graph.edge a false b true = true → rank a < rank b)
    (x y : Fin n) (fixed : Fin n → Bool)
    (fixedPretreatment : ∀ v, fixed v = true → ¬ DirectedReach graph x v)
    (v : Fin n) (inOSet : InOSet graph x y fixed v) : ¬ Forbidden graph x y v := by
  rcases inOSet with parent | collider | ⟨c, collider, edge⟩
  · exact parent.1
  · exact (collider_eligible collider).1
  · rintro (rfl | ⟨w, seed, descends⟩)
    · exact treatment_not_collider_parent increases fixedPretreatment collider edge
    · exact (collider_eligible collider).1 (.inr ⟨w, seed, reach_to_child descends edge⟩)

private theorem lift_reach_to_ancestor_of_target {graph : MixedGraph n} {mask : Fin n → Bool}
    {u v : Fin n} (path : DirectedReach graph u v) (target : mask v = true) :
    graph.AncestorOf mask u := by
  induction path with
  | @conditioned w member =>
    have same : w = v := by simpa using member
    exact .conditioned (same.symm ▸ target)
  | parent edge _ ih => exact .parent edge ih

private theorem connected_along_parent {graph : MixedGraph n} {x c p : Fin n}
    {conditioning : Fin n → Bool} (edge : graph.edge p false c true = true)
    (parentOutside : conditioning p = false) (childOutside : conditioning c = false)
    (unequal : c ≠ x)
    (connection : graph.PathConnected (· == p) (· == x) conditioning) :
    graph.PathConnected (· == c) (· == x) conditioning := by
  obtain ⟨source, outgoing, start, visited, last, leftHit, firstEdge, walk, rightHit, _⟩ := connection
  have identifies : source = p := by simpa using leftHit
  subst source
  have returnEdge : graph.edge c true p false = true :=
    (graph.symmetric p false c true).symm.trans edge
  have step : graph.Step conditioning (p, false) start :=
    ⟨outgoing, firstEdge, by simpa [MixedGraph.openTurn] using parentOutside⟩
  have reached := MixedGraph.reachable_iff_active_walk.mpr
    ⟨start.1 :: visited, MixedGraph.ActiveWalk.cons step walk⟩
  apply (graph.walkConnected_iff_pathConnected (· == c) (· == x) conditioning ?_ ?_).mp
  · exact ⟨(p, false), last, ⟨c, true, by simp, returnEdge⟩, reached, rightHit⟩
  · intro v hv
    have same : v = c := by simpa using hv
    exact same.symm ▸ childOutside
  · intro v hv
    have same : v = c := by simpa using hv
    simpa [same] using unequal

/-- The collider-parent eligibility conclusion of Lemma B.3, with
the same fixed nondescendant domain as forbidden-set avoidance. -/
theorem collider_parent_eligible (graph : MixedGraph n) (rank : Fin n → Nat)
    (increases : ∀ a b, graph.edge a false b true = true → rank a < rank b)
    (x y : Fin n) (fixed : Fin n → Bool)
    (fixedPretreatment : ∀ v, fixed v = true → ¬ DirectedReach graph x v)
    {p c : Fin n} (collider : Collider graph x y fixed c) (edge : graph.edge p false c true = true) :
    Eligible graph x y fixed p := by
  classical
  have parentAllowed := o_set_avoids_forbidden graph rank increases x y fixed fixedPretreatment p
    (.inr (.inr ⟨c, collider, edge⟩))
  refine ⟨parentAllowed, ?_⟩
  by_cases parentAncestor : ValidAncestor graph x y fixed p
  · exact .inl parentAncestor
  · refine .inr ?_
    intro parentConnection
    have childOutside : ¬ ValidAncestor graph x y fixed c :=
      fun cA => parentAncestor ⟨.parent edge cA.1, parentAllowed⟩
    have childNotTreatment : c ≠ x := fun same => (collider_eligible collider).1 (.inl same)
    have childConnection := connected_along_parent edge
      (by simp [validAncestors, parentAncestor]) (by simp [validAncestors, childOutside])
      childNotTreatment parentConnection
    exact (collider_eligible collider).2.elim childOutside (fun sep => sep childConnection)

/-- Every vertex in the O-set satisfies the eligibility predicate of
Definition 3 in the stated fixed nondescendant domain. -/
theorem o_set_eligible (graph : MixedGraph n) (rank : Fin n → Nat)
    (increases : ∀ a b, graph.edge a false b true = true → rank a < rank b)
    (x y : Fin n) (fixed : Fin n → Bool)
    (fixedPretreatment : ∀ v, fixed v = true → ¬ DirectedReach graph x v)
    {p : Fin n} (selected : InOSet graph x y fixed p) : Eligible graph x y fixed p := by
  rcases selected with ⟨outside, w, mediator, parent⟩ | included | ⟨c, included, parent⟩
  · refine ⟨outside, .inl ⟨.parent parent ?_, outside⟩⟩
    have reachesY : DirectedReach graph w y := by
      rcases mediator with rfl | ⟨_, _, reaches⟩
      · exact .conditioned (by simp)
      · exact reaches
    exact lift_reach_to_ancestor_of_target reachesY (by simp)
  · exact collider_eligible included
  · exact collider_parent_eligible graph rank increases x y fixed fixedPretreatment included parent

/-- The descendant portion of the forbidden set, with the outcome and
mediators included through reflexive directed reachability. -/
def ForbiddenDescendant (graph : MixedGraph n) (x y v : Fin n) : Prop :=
  ∃ w, OutcomeAndMediators graph x y w ∧ DirectedReach graph w v

private theorem forbidden_descendant_of_edge {graph : MixedGraph n} {x y u v : Fin n}
    (forbidden : ForbiddenDescendant graph x y u) (edge : graph.edge u false v true = true) :
    ForbiddenDescendant graph x y v := by
  obtain ⟨w, seed, reaches⟩ := forbidden
  exact ⟨w, seed, reach_to_child reaches edge⟩

private theorem forbidden_inactive {graph : MixedGraph n} {x y v : Fin n}
    {conditioning : Fin n → Bool}
    (avoids : ∀ u, ForbiddenDescendant graph x y u → conditioning u = false)
    (forbidden : ForbiddenDescendant graph x y v) : ¬ graph.AncestorOf conditioning v := by
  intro active
  induction active with
  | conditioned member =>
    simp [avoids _ forbidden] at member
  | parent edge _ ih =>
    exact ih (forbidden_descendant_of_edge forbidden edge)

/-- Once an active walk enters a forbidden descendant at a head, its
remaining edges point forward and cannot leave the descendant set.
The conditioning set must avoid the descendants. This is the general
path-propagation argument used in Appendix B.4 and B.5. -/
theorem forbidden_descendant_walk_continuation {graph : MixedGraph n} {x y : Fin n}
    {conditioning : Fin n → Bool}
    (avoids : ∀ u, ForbiddenDescendant graph x y u → conditioning u = false)
    {first last : MixedGraph.Arrival n} {visits : List (Fin n)}
    (walk : graph.ActiveWalk conditioning first visits last)
    (forbidden : ForbiddenDescendant graph x y first.1)
    (head : first.2 = true)
    (incident : ∃ w mark, graph.edge first.1 true w mark = true) :
    DirectedReach graph first.1 last.1 ∧
      ForbiddenDescendant graph x y last.1 := by
  induction walk with
  | nil => exact ⟨.conditioned (by simp), forbidden⟩
  | @cons first next _ _ move _ ih =>
    obtain ⟨outgoing, edge, turn⟩ := move
    have tail : outgoing = false := by
      cases outgoing with
      | false => rfl
      | true =>
        have active : graph.AncestorOf conditioning first.1 := by
          simpa [MixedGraph.openTurn, head] using turn
        exact (forbidden_inactive avoids forbidden active).elim
    have nextHead : next.2 = true := by
      cases arrival : next.2 with
      | true => rfl
      | false =>
        have undirected : graph.edge first.1 false next.1 false = true := by
          simpa [tail, arrival] using edge
        obtain ⟨w, mark, inEdge⟩ := incident
        rw [graph.no_arrow_of_undirected undirected] at inEdge
        contradiction
    have directed : graph.edge first.1 false next.1 true = true := by
      simpa [tail, nextHead] using edge
    have reverse : graph.edge next.1 true first.1 false = true :=
      (graph.symmetric _ _ _ _).symm.trans directed
    obtain ⟨reaches, stillForbidden⟩ := ih (forbidden_descendant_of_edge forbidden directed)
      nextHead ⟨first.1, false, reverse⟩
    exact ⟨.parent directed reaches, stillForbidden⟩

/-- An active path with an allowed endpoint cannot enter a forbidden
descendant at a head. Here the incoming head is witnessed explicitly
as the initial edge of the remaining walk. -/
theorem no_active_walk_from_forbidden_arrowhead {graph : MixedGraph n} {x y : Fin n}
    {conditioning : Fin n → Bool}
    (avoids : ∀ u, ForbiddenDescendant graph x y u → conditioning u = false)
    {u v : Fin n} {mark : Bool} (incoming : graph.edge u mark v true = true)
    (forbidden : ForbiddenDescendant graph x y v) {last : MixedGraph.Arrival n}
    {visits : List (Fin n)} (allowedLast : ¬ ForbiddenDescendant graph x y last.1) :
    ¬ graph.ActiveWalk conditioning (v, true) visits last := by
  intro walk
  have reverse : graph.edge v true u mark = true := (graph.symmetric _ _ _ _).symm.trans incoming
  exact allowedLast (forbidden_descendant_walk_continuation avoids walk forbidden rfl
    ⟨u, mark, reverse⟩).2

end

end OpenCausalScience.Papers.Runge2021.OSetForbidden
