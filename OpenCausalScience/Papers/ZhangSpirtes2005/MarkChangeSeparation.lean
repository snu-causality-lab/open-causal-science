module
public import OpenCausalScience.Graph.MixedSeparation
public import OpenCausalScience.Papers.ZhangSpirtes2005.LegitimateMarkChange

/-! Path transfer for the mark change in Zhang and Spirtes (2005), Lemma 2. -/

namespace OpenCausalScience.Papers.ZhangSpirtes2005.LegitimateMarkChange

open MixedGraph (ActiveWalk AncestorOf Arrival Reach Step openTurn)
open Zhang2008OrientationRules.Orientations (Directed)

@[expose] public section

variable {n : Nat}

/-- Regard a singly marked graph without undirected edges as a mixed graph. -/
def asMixed (G : MarkedGraph n) (noLines : NoLines G) : MixedGraph n where
  edge u p v q := decide (G.marks u v = some (p, q))
  symmetric u p v q := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    rw [G.swap_marks u v]
    cases G.marks u v with
    | none => simp
    | some marks => cases marks; simp [Prod.swap, and_comm]
  loop_free u p q := by simp [G.loop_free]
  no_arrow_of_undirected e := (noLines _ _ (of_decide_eq_true e)).elim

private theorem mixed_edge_iff {G : MarkedGraph n} {noLines : NoLines G}
    {u v : Fin n} {p q : Bool} :
    (asMixed G noLines).edge u p v q = true ↔ G.marks u v = some (p, q) :=
  decide_eq_true_iff

theorem no_lines_after {G H : MarkedGraph n} {a b : Fin n}
    (noLines : NoLines G) (edit : AddedHead G H a b) : NoLines H := by
  intro u v marks
  by_cases forward : u = a ∧ v = b
  · obtain ⟨rfl, rfl⟩ := forward
    rw [show H.marks _ _ = some (true, true) from edit.changed] at marks
    contradiction
  by_cases backward : u = b ∧ v = a
  · obtain ⟨rfl, rfl⟩ := backward
    rw [H.swap_marks _ _, show H.marks _ _ = some (true, true) from edit.changed] at marks
    contradiction
  exact noLines u v ((edit.other u v (by by_cases h : u = a; exact Or.inr (fun hv => forward ⟨h, hv⟩); exact Or.inl h)
    (by by_cases h : u = b; exact Or.inr (fun hv => backward ⟨h, hv⟩); exact Or.inl h)).symm.trans marks)

/-- The mark change can remove activation only at its source. In that case
its target is still activated. -/
theorem ancestor_after_change {G H : MarkedGraph n} {a b v : Fin n} {C : Fin n → Bool}
    {noLines : NoLines G} {noLines' : NoLines H} (edit : AddedHead G H a b)
    (matching : MatchingParentsSpouses G a b)
    (active : (asMixed G noLines).AncestorOf C v) :
    (asMixed H noLines').AncestorOf C v ∨ v = a ∧ (asMixed H noLines').AncestorOf C b := by
  have parents := (parent_and_spouse_conditions edit.original matching).1
  induction active with
  | conditioned h => exact Or.inl (.conditioned h)
  | @parent u v edge _ ih =>
    have directed : Directed G u v := mixed_edge_iff.mp edge
    have keep (h : u ≠ a ∨ v ≠ b) : (asMixed H noLines').edge u false v true = true :=
      mixed_edge_iff.mpr ((directed_iff_without edit u v).mpr ⟨directed, h⟩)
    rcases ih with activated | ⟨same, targetActivated⟩
    · by_cases changed : u = a ∧ v = b
      · obtain ⟨rfl, rfl⟩ := changed
        exact Or.inr ⟨rfl, activated⟩
      · have other : u ≠ a ∨ v ≠ b := by
          by_cases h : u = a
          · exact Or.inr (fun hv => changed ⟨h, hv⟩)
          · exact Or.inl h
        exact Or.inl (.parent (keep other) activated)
    · subst v
      have shortcut := parents u directed
      have ua : u ≠ a := by
        rintro rfl
        simp [Directed, G.loop_free] at directed
      exact Or.inl (.parent (mixed_edge_iff.mpr ((directed_iff_without edit u b).mpr
        ⟨shortcut, Or.inl ua⟩)) targetActivated)

private theorem ancestor_before_change {G H : MarkedGraph n} {a b v : Fin n} {C : Fin n → Bool}
    {noLines : NoLines G} {noLines' : NoLines H} (edit : AddedHead G H a b)
    (active : (asMixed H noLines').AncestorOf C v) : (asMixed G noLines).AncestorOf C v := by
  induction active with
  | conditioned h => exact .conditioned h
  | @parent u v e _ ih =>
    exact .parent (mixed_edge_iff.mpr ((directed_iff_without edit u v).mp (mixed_edge_iff.mp e)).1) ih

private structure Transfer (G H : MixedGraph n) (C : Fin n → Bool)
    (a b : Fin n) (oldMark newMark : Bool) : Prop where
  away : ∀ u p v q, (u ≠ a ∨ v ≠ b) → (u ≠ b ∨ v ≠ a) →
    G.edge u p v q = H.edge u p v q
  before : ∀ p q, G.edge a p b q = true ↔ p = oldMark ∧ q = true
  after : H.edge a newMark b true = true
  matched : ∀ c p, c ≠ a → c ≠ b → G.edge a true c p = true → H.edge b true c p = true
  activation : ∀ v, G.AncestorOf C v → H.AncestorOf C v ∨ v = a ∧ H.AncestorOf C b

variable {G H : MixedGraph n} {C : Fin n → Bool} {a b : Fin n} {oldMark newMark : Bool}

private theorem Transfer.turn_away (t : Transfer G H C a b oldMark newMark)
    {u : Fin n} (ua : u ≠ a) {incoming outgoing : Bool}
    (turn : G.openTurn C (u, incoming) outgoing) : H.openTurn C (u, incoming) outgoing := by
  cases incoming <;> cases outgoing <;> simp [openTurn] at turn ⊢ <;> try assumption
  exact (t.activation u turn).resolve_right (fun h => ua h.1)

private theorem Transfer.pair_away (t : Transfer G H C a b oldMark newMark)
    {u v : Fin n} {p q : Bool} (ua : u ≠ a) (va : v ≠ a)
    (e : G.edge u p v q = true) : H.edge u p v q = true :=
  (t.away u p v q (.inl ua) (.inr va)).symm.trans e

private theorem reach_two {α : Type} {R : α → α → Prop} {s m z : α}
    (first : R s m) (second : R m z) : Reach R s z :=
  .extend (.extend (.refl _) first) second

private theorem Transfer.around_a (t : Transfer G H C a b oldMark newMark)
    {x y : Fin n} (xa : x ≠ a) (ya : y ≠ a) (xy : x ≠ y)
    {i xMark p q yMark : Bool}
    (ax : G.edge x xMark a p = true) (ay : G.edge a q y yMark = true)
    (turnX : G.openTurn C (x, i) xMark) (turnA : G.openTurn C (a, p) q) :
    Reach (H.Step C) (x, i) (y, yMark) := by
  have keepX := t.turn_away xa turnX
  by_cases xb : x = b
  · subst x
    have marks := (t.before p xMark).mp ((G.symmetric _ _ _ _).symm.trans ax)
    obtain ⟨rfl, rfl⟩ := marks
    cases q with
    | true =>
      exact .extend (.refl _) ⟨true, t.matched y yMark ya (Ne.symm xy) ay, keepX⟩
    | false =>
      have first := (H.symmetric _ _ _ _).symm.trans t.after
      have second := (t.away a false y yMark (.inr (Ne.symm xy)) (.inr ya)).symm.trans ay
      exact reach_two (m := (a, newMark)) ⟨true, first, keepX⟩
        ⟨false, second, by simpa [openTurn] using turnA⟩
  by_cases yb : y = b
  · subst y
    obtain ⟨rfl, rfl⟩ := (t.before q yMark).mp ay
    cases p with
    | true =>
      have shortcut := t.matched x xMark xa xb ((G.symmetric _ _ _ _).symm.trans ax)
      exact .extend (.refl _) ⟨xMark, (H.symmetric _ _ _ _).symm.trans shortcut, keepX⟩
    | false =>
      have first := (t.away x xMark a false (.inl xa) (.inl xb)).symm.trans ax
      exact reach_two (m := (a, false)) ⟨xMark, first, keepX⟩
        ⟨newMark, t.after, by simpa [openTurn] using turnA⟩
  have first := (t.away x xMark a p (.inl xa) (.inl xb)).symm.trans ax
  have second := (t.away a q y yMark (.inr yb) (.inr ya)).symm.trans ay
  by_cases heads : p && q = true
  · have both : p = true ∧ q = true := by simpa using heads
    obtain ⟨rfl, rfl⟩ := both
    have active : G.AncestorOf C a := by simpa [openTurn] using turnA
    rcases t.activation a active with still | ⟨_, target⟩
    · exact reach_two (m := (a, true)) ⟨xMark, first, keepX⟩
        ⟨true, second, by simpa [openTurn] using still⟩
    · have fromX := t.matched x xMark xa xb ((G.symmetric _ _ _ _).symm.trans ax)
      have toY := t.matched y yMark ya yb ay
      exact reach_two (m := (b, true)) ⟨xMark, (H.symmetric _ _ _ _).symm.trans fromX, keepX⟩
        ⟨true, toY, by simpa [openTurn] using target⟩
  · have notHeads : ¬ (p = true ∧ q = true) := by simpa using heads
    exact reach_two (m := (a, p)) ⟨xMark, first, keepX⟩
      ⟨q, second, by simpa [openTurn, notHeads] using turnA⟩

private theorem reach_then {α : Type} {R : α → α → Prop} {s m z : α}
    (first : Reach R s m) (second : Reach R m z) : Reach R s z := by
  induction second with
  | refl => exact first
  | extend _ step ih => exact .extend ih step

private theorem Transfer.into_a (t : Transfer G H C a b oldMark newMark)
    {x : Fin n} (xa : x ≠ a) {xMark aMark : Bool}
    (edge : G.edge x xMark a aMark = true) : ∃ arrival, H.edge x xMark a arrival = true := by
  by_cases xb : x = b
  · subst x
    have marks := (t.before aMark xMark).mp ((G.symmetric _ _ _ _).symm.trans edge)
    obtain ⟨_, rfl⟩ := marks
    exact ⟨newMark, (H.symmetric _ _ _ _).symm.trans t.after⟩
  · exact ⟨aMark, (t.away x xMark a aMark (.inl xa) (.inl xb)).symm.trans edge⟩

private theorem Transfer.from_a (t : Transfer G H C a b oldMark newMark)
    {y : Fin n} (ya : y ≠ a) {aMark yMark : Bool}
    (edge : G.edge a aMark y yMark = true) : ∃ outgoing, H.edge a outgoing y yMark = true := by
  by_cases yb : y = b
  · subst y
    obtain ⟨_, rfl⟩ := (t.before aMark yMark).mp edge
    exact ⟨newMark, t.after⟩
  · exact ⟨aMark, (t.away a aMark y yMark (.inr yb) (.inr ya)).symm.trans edge⟩

private theorem Transfer.walk_from_away (t : Transfer G H C a b oldMark newMark)
    {start final : Arrival n} {visited : List (Fin n)}
    (walk : G.ActiveWalk C start visited final) (simple : (start.1 :: visited).Nodup)
    (away : start.1 ≠ a) :
    ∃ last, last.1 = final.1 ∧ Reach (H.Step C) start last := by
  induction size : visited.length using Nat.strongRecOn generalizing start final visited with
  | ind lengthBound ih =>
    cases walk with
    | nil => exact ⟨start, rfl, .refl _⟩
    | @cons start next final rest move tail =>
      rcases start with ⟨x, incoming⟩
      rcases next with ⟨v, arrival⟩
      obtain ⟨outgoing, edge, turn⟩ := move
      have tailSimple := (List.nodup_cons.mp simple).2
      by_cases va : v = a
      · subst v
        cases tail with
        | nil =>
          obtain ⟨newArrival, newEdge⟩ := t.into_a away edge
          exact ⟨(a, newArrival), rfl, .extend (.refl _) ⟨outgoing, newEdge, t.turn_away away turn⟩⟩
        | @cons _ next final suffix move tail =>
          rcases next with ⟨y, yMark⟩
          obtain ⟨aMark, nextEdge, turnA⟩ := move
          have ya : y ≠ a := by
            intro same
            exact (List.nodup_cons.mp tailSimple).1 (by simp [same])
          have xy : x ≠ y := by
            intro same
            exact (List.nodup_cons.mp simple).1 (by simp [same])
          have rewritten := t.around_a away ya xy edge nextEdge turn turnA
          have small : suffix.length < lengthBound := by simp at size; omega
          obtain ⟨last, endVertex, reached⟩ :=
            ih suffix.length small tail (List.nodup_cons.mp tailSimple).2 ya rfl
          exact ⟨last, endVertex, reach_then rewritten reached⟩
      · have rewritten : H.Step C (x, incoming) (v, arrival) :=
          ⟨outgoing, t.pair_away away va edge, t.turn_away away turn⟩
        have small : rest.length < lengthBound := by simp at size; omega
        obtain ⟨last, endVertex, reached⟩ := ih rest.length small tail tailSimple va rfl
        exact ⟨last, endVertex, reach_then (.extend (.refl _) rewritten) reached⟩

private theorem Transfer.path_to_walk (t : Transfer G H C a b oldMark newMark)
    {left right : Fin n → Bool} (outside : ∀ v, left v = true → C v = false)
    (disjoint : ∀ v, left v = true → right v = false)
    (path : G.PathConnected left right C) : H.WalkConnected left right C := by
  obtain ⟨source, outgoing, first, visited, final, memLeft, edge, walk, memRight, simple⟩ := path
  have fromArrival (reached : ∃ last, last.1 = final.1 ∧ Reach (H.Step C) (source, false) last) :
      H.WalkConnected left right C := by
    obtain ⟨last, endVertex, reach⟩ := reached
    obtain ⟨_, walk⟩ := MixedGraph.reachable_iff_active_walk.mp reach
    cases walk with
    | nil =>
      have finalIsSource : source = final.1 := endVertex
      exact (Bool.false_ne_true ((disjoint source memLeft).symm.trans (finalIsSource ▸ memRight))).elim
    | cons move suffix =>
      obtain ⟨newOutgoing, newEdge, _⟩ := move
      exact ⟨_, _, ⟨source, newOutgoing, memLeft, newEdge⟩,
        MixedGraph.reachable_iff_active_walk.mpr ⟨_, suffix⟩, endVertex ▸ memRight⟩
  by_cases sourceA : source = a
  · subst source
    rcases first with ⟨v, arrival⟩
    have va : v ≠ a := by
      intro same
      exact (List.nodup_cons.mp simple).1 (by simp [same])
    obtain ⟨newOutgoing, newEdge⟩ := t.from_a va edge
    obtain ⟨last, endVertex, reached⟩ := t.walk_from_away walk (List.nodup_cons.mp simple).2 va
    exact ⟨_, last, ⟨a, newOutgoing, memLeft, newEdge⟩, reached, endVertex ▸ memRight⟩
  · have firstStep : G.Step C (source, false) first :=
      ⟨outgoing, edge, by simpa [openTurn] using outside source memLeft⟩
    exact fromArrival (t.walk_from_away (.cons firstStep walk) simple sourceA)

private theorem mixed_away {G H : MarkedGraph n} {a b : Fin n} {noLines : NoLines G}
    {noLines' : NoLines H} (edit : AddedHead G H a b) (u : Fin n) (p : Bool) (v : Fin n) (q : Bool)
    (forward : u ≠ a ∨ v ≠ b) (backward : u ≠ b ∨ v ≠ a) :
    (asMixed G noLines).edge u p v q = (asMixed H noLines').edge u p v q := by
  apply Bool.eq_iff_iff.mpr
  simp only [mixed_edge_iff, edit.other u v forward backward]

private theorem matched_incoming {G : MarkedGraph n} {a b c : Fin n} {p : Bool}
    (matching : MatchingParentsSpouses G a b) (ca : c ≠ a) (cb : c ≠ b) :
    G.marks a c = some (true, p) ↔ G.marks b c = some (true, p) := by
  have flip (v : Fin n) : G.marks v c = some (true, p) ↔ G.marks c v = some (p, true) := by
    rw [G.swap_marks c v]
    cases G.marks c v with
    | none => simp
    | some marks => cases marks; simp [Prod.swap, and_comm]
  rw [flip a, flip b]
  cases p with
  | false => exact (matching c ca cb).1
  | true => exact (matching c ca cb).2

private theorem transfer_forward {G H : MarkedGraph n} {a b : Fin n} {C : Fin n → Bool}
    {noLines : NoLines G} {noLines' : NoLines H} (edit : AddedHead G H a b)
    (matching : MatchingParentsSpouses G a b) :
    Transfer (asMixed G noLines) (asMixed H noLines') C a b false true where
  away := mixed_away edit
  before p q := by
    have original : G.marks a b = some (false, true) := edit.original
    simp [mixed_edge_iff, original]
  after := mixed_edge_iff.mpr edit.changed
  matched c p ca cb edge := by
    have moved := (matched_incoming matching ca cb).mp (mixed_edge_iff.mp edge)
    rw [← edit.other b c (.inr cb) (.inr ca)] at moved
    exact mixed_edge_iff.mpr moved
  activation _ := ancestor_after_change edit matching

private theorem transfer_backward {G H : MarkedGraph n} {a b : Fin n} {C : Fin n → Bool}
    {noLines : NoLines G} {noLines' : NoLines H} (edit : AddedHead G H a b)
    (matching : MatchingParentsSpouses G a b) :
    Transfer (asMixed H noLines') (asMixed G noLines) C a b true false where
  away u p v q forward backward := (mixed_away edit u p v q forward backward).symm
  before p q := by
    have changed : H.marks a b = some (true, true) := edit.changed
    simp [mixed_edge_iff, changed]
  after := mixed_edge_iff.mpr edit.original
  matched c p ca cb edge := by
    have original := mixed_edge_iff.mp edge
    rw [edit.other a c (.inr cb) (.inr ca)] at original
    exact mixed_edge_iff.mpr ((matched_incoming matching ca cb).mp original)
  activation _ h := Or.inl (ancestor_before_change edit h)

/-- The edited graph has the same active-path queries. The two graphs
share the external parents and spouses of the edited edge's endpoints. -/
theorem path_connected_iff_of_matching {G H : MarkedGraph n} {a b : Fin n}
    (noLines : NoLines G) (edit : AddedHead G H a b) (matching : MatchingParentsSpouses G a b)
    (left right C : Fin n → Bool) (outside : ∀ v, left v = true → C v = false)
    (disjoint : ∀ v, left v = true → right v = false) :
    (asMixed G noLines).PathConnected left right C ↔
      (asMixed H (no_lines_after noLines edit)).PathConnected left right C := by
  constructor
  · intro path
    apply ((asMixed H _).walkConnected_iff_pathConnected left right C outside disjoint).mp
    exact (transfer_forward edit matching).path_to_walk outside disjoint path
  · intro path
    apply ((asMixed G noLines).walkConnected_iff_pathConnected left right C outside disjoint).mp
    exact (transfer_backward edit matching).path_to_walk outside disjoint path

/-- Changing a directed edge to a bidirected edge preserves m-separation
when the endpoints have matching external parents and spouses. -/
theorem m_separated_eq_of_matching {G H : MarkedGraph n} {a b : Fin n}
    (noLines : NoLines G) (edit : AddedHead G H a b) (matching : MatchingParentsSpouses G a b)
    (left right C : Fin n → Bool) (outside : ∀ v, left v = true → C v = false)
    (disjoint : ∀ v, left v = true → right v = false) :
    (asMixed G noLines).mSeparated left right C =
      (asMixed H (no_lines_after noLines edit)).mSeparated left right C := by
  apply Bool.eq_iff_iff.mpr
  rw [(asMixed G noLines).m_separated_iff_no_path left right C outside disjoint,
    (asMixed H _).m_separated_iff_no_path left right C outside disjoint,
    path_connected_iff_of_matching noLines edit matching left right C outside disjoint]

/-- Two edits with the same bidirected intermediate graph leave the external
parent and spouse sets at each endpoint unchanged. -/
theorem matching_of_reverse_edits {G H K : MarkedGraph n} {a b : Fin n}
    (forward : AddedHead G H a b) (backward : AddedHead K H b a)
    (matching : MatchingParentsSpouses G a b) : MatchingParentsSpouses K b a := by
  intro c cb ca
  have sameA : K.marks c a = G.marks c a :=
    (backward.other c a (.inl cb) (.inl ca)).symm.trans
      (forward.other c a (.inl ca) (.inl cb))
  have sameB : K.marks c b = G.marks c b :=
    (backward.other c b (.inl cb) (.inl ca)).symm.trans
      (forward.other c b (.inl ca) (.inl cb))
  simpa only [Directed, Spouse, sameA, sameB] using
    And.intro (matching c ca cb).1.symm (matching c ca cb).2.symm

/-- Reverse a directed edge through the common bidirected graph. External
parents and spouses need only be matched in the original graph. -/
theorem m_separated_eq_of_reversal {G H K : MarkedGraph n} {a b : Fin n}
    (noLines : NoLines G) (noLines' : NoLines K)
    (forward : AddedHead G H a b) (backward : AddedHead K H b a)
    (matching : MatchingParentsSpouses G a b)
    (left right C : Fin n → Bool) (outside : ∀ v, left v = true → C v = false)
    (disjoint : ∀ v, left v = true → right v = false) :
    (asMixed G noLines).mSeparated left right C = (asMixed K noLines').mSeparated left right C := by
  have matchedReverse := matching_of_reverse_edits forward backward matching
  exact (m_separated_eq_of_matching noLines forward matching left right C outside disjoint).trans
    (m_separated_eq_of_matching noLines' backward matchedReverse left right C outside disjoint).symm

end
end OpenCausalScience.Papers.ZhangSpirtes2005.LegitimateMarkChange
