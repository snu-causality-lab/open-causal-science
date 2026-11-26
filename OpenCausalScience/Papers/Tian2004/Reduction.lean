module
public import OpenCausalScience.Papers.Tian2004.FactorGraph

/-! Moving an evidence vertex whose factor block does not reach the
outcome preserves every outcome-linked district. At a stationary
query, the remaining districts are precisely those in outcome-linked
blocks of the original query. -/

namespace OpenCausalScience.Papers.Tian2004.Reduction

open MixedGraph (Reach)
open FactorGraph

@[expose] public section

variable {n : Nat}

/-- The random vertices before the ancestral restriction and the two
disjoint query sets. Vertices outside allowed are intervened on. -/
structure Query (n : Nat) where
  allowed : Vertices n
  outcome : Vertices n
  evidence : Vertices n
  outcome_allowed : ∀ {v}, outcome v → allowed v
  evidence_allowed : ∀ {v}, evidence v → allowed v
  disjoint : ∀ {v}, outcome v → ¬ evidence v

namespace Query

def terminal (q : Query n) (v : Fin n) : Prop := q.outcome v ∨ q.evidence v

theorem terminal_allowed (q : Query n) {v : Fin n} (h : q.terminal v) : q.allowed v :=
  h.elim q.outcome_allowed q.evidence_allowed

def live (q : Query n) (G : MixedGraph n) (v : Fin n) : Prop :=
  q.allowed v ∧ ∃ t, q.terminal t ∧ Reach (Within q.allowed (Dir G)) v t

def linked (q : Query n) (G : MixedGraph n) (v : Fin n) : Prop :=
  Linked G (q.live G) q.outcome q.evidence v

def district (q : Query n) (G : MixedGraph n) (v : Fin n) : Vertices n :=
  FactorGraph.district G (q.live G) v

theorem live_of_terminal (q : Query n) (G : MixedGraph n) {v : Fin n}
    (h : q.terminal v) : q.live G v :=
  ⟨q.terminal_allowed h, v, h, .refl v⟩

/-- Move one observed value from evidence to the intervention. -/
def move (q : Query n) (z : Fin n) (hz : q.evidence z) : Query n where
  allowed v := q.allowed v ∧ v ≠ z
  outcome := q.outcome
  evidence v := q.evidence v ∧ v ≠ z
  outcome_allowed h := ⟨q.outcome_allowed h, fun equal => q.disjoint h (equal ▸ hz)⟩
  evidence_allowed h := ⟨q.evidence_allowed h.1, h.2⟩
  disjoint h new := q.disjoint h new.1

theorem move_live_subset {G : MixedGraph n} {q : Query n} {z v : Fin n} {hz : q.evidence z}
    (new : (q.move z hz).live G v) : q.live G v := by
  obtain ⟨hv, t, tTerm, path⟩ := new
  exact ⟨hv.1, t, tTerm.imp id And.left,
    reach_map (fun e => ⟨e.1.1, e.2.1.1, e.2.2⟩) path⟩

theorem parent_live {G : MixedGraph n} {q : Query n} {u v : Fin n}
    (edge : Within q.allowed (Dir G) u v) (target : q.live G v) : q.live G u := by
  obtain ⟨_, w, last, route⟩ := target
  exact ⟨edge.1, w, last, reach_trans (.extend (.refl u) edge) route⟩

private theorem route_in_live {G : MixedGraph n} {q : Query n} {u v : Fin n}
    (route : Reach (Within q.allowed (Dir G)) u v) :
    q.live G v → q.live G u ∧ Reach (Within (q.live G) (Dir G)) u v := by
  induction route with
  | refl => exact fun h => ⟨h, .refl _⟩
  | extend _ edge ih =>
    intro atTarget
    have before := parent_live edge atTarget
    obtain ⟨first, earlier⟩ := ih before
    exact ⟨first, .extend earlier ⟨before, atTarget, edge.2.2⟩⟩

private theorem first_terminal {α : Type} {R : α → α → Prop}
    (terminal : α → Prop) {u v : α} (route : Reach R u v) :
    (∃ t, terminal t ∧ Reach (fun a b => ¬ terminal a ∧ R a b) u t) ∨
      Reach (fun a b => ¬ terminal a ∧ R a b) u v := by
  classical
  induction route with
  | refl => exact Or.inr (.refl _)
  | @extend a b earlier last ih =>
    rcases ih with found | before
    · exact Or.inl found
    · by_cases atTerminal : terminal a
      · exact Or.inl ⟨a, atTerminal, before⟩
      · exact Or.inr (.extend before ⟨atTerminal, last⟩)

/-- A live vertex can reach a first terminal along directed edges whose
sources are all summed variables. -/
theorem route_to_first_terminal {G : MixedGraph n} {q : Query n} {u : Fin n}
    (isLive : q.live G u) :
    ∃ t, q.terminal t ∧ Reach (fun a b => Free q.outcome q.evidence a ∧
      Within (q.live G) (Dir G) a b) u t := by
  obtain ⟨_, target, targetTerm, route⟩ := isLive
  have inLive := (route_in_live route (q.live_of_terminal G targetTerm)).2
  have first := first_terminal q.terminal inLive
  obtain ⟨t, hit, before⟩ :
      ∃ t, q.terminal t ∧ Reach (fun a b => ¬ q.terminal a ∧
        Within (q.live G) (Dir G) a b) u t :=
    first.elim id (fun path => ⟨target, targetTerm, path⟩)
  exact ⟨t, hit, reach_map (fun e =>
    ⟨⟨fun h => e.1 (Or.inl h), fun h => e.1 (Or.inr h)⟩, e.2⟩) before⟩

private theorem free_edge_bridge {G : MixedGraph n} {q : Query n} {u v : Fin n}
    (edge : Free q.outcome q.evidence u ∧ Within (q.live G) (Dir G) u v) :
    Bridge G (q.live G) q.outcome q.evidence u v :=
  ⟨edge.2.1, edge.2.2.1, Or.inr (Or.inl ⟨edge.1, edge.2.2.2⟩)⟩

/-- Moving an outcome-unlinked evidence vertex preserves every
outcome-linked vertex in the exact ancestral restriction. -/
theorem linked_retained {G : MixedGraph n} {q : Query n} {z u : Fin n}
    (hz : q.evidence z) (eligible : ¬ q.linked G z) (linked : q.linked G u) :
    (q.move z hz).live G u := by
  have keeps {v : Fin n} (h : q.linked G v) : (q.move z hz).allowed v :=
    ⟨(linked_is_live h).1, fun equal => eligible (equal ▸ h)⟩
  obtain ⟨t, terminal, path⟩ := route_to_first_terminal (linked_is_live linked)
  have retained_path {v : Fin n}
      (route : Reach (fun a b => Free q.outcome q.evidence a ∧
        Within (q.live G) (Dir G) a b) u v) :
      q.linked G v ∧ Reach (Within (q.move z hz).allowed (Dir G)) u v := by
    induction route with
    | refl => exact ⟨linked, .refl _⟩
    | extend _ last ih =>
      have atEnd := (linked_iff_of_steps (.extend (.refl _) (free_edge_bridge last))).mp ih.1
      exact ⟨atEnd, .extend ih.2 ⟨keeps ih.1, keeps atEnd, last.2.2.2⟩⟩
  have after := retained_path path
  have terminalAfter : (q.move z hz).terminal t := terminal.imp id (fun h => ⟨h, (keeps after.1).2⟩)
  exact ⟨keeps linked, t, terminalAfter, after.2⟩

private theorem free_iff_after {q : Query n} {z v : Fin n} {hz : q.evidence z}
    (different : v ≠ z) : Free q.outcome q.evidence v ↔
      Free (q.move z hz).outcome (q.move z hz).evidence v :=
  ⟨fun free => ⟨free.1, fun ev => free.2 ev.1⟩, fun free =>
    ⟨free.1, fun ev => free.2 ⟨ev, different⟩⟩⟩

private theorem bridge_after {G : MixedGraph n} {q : Query n} {z u v : Fin n} {hz : q.evidence z}
    (hu : (q.move z hz).live G u) (hv : (q.move z hz).live G v)
    (edge : Bridge G (q.live G) q.outcome q.evidence u v) :
    Bridge G ((q.move z hz).live G) (q.move z hz).outcome (q.move z hz).evidence u v :=
  ⟨hu, hv, edge.2.2.imp id (Or.imp
    (fun e => ⟨(free_iff_after hu.1.2).mp e.1, e.2⟩)
    (fun e => ⟨(free_iff_after hv.1.2).mp e.1, e.2⟩))⟩

private theorem bridge_before {G : MixedGraph n} {q : Query n} {z u v : Fin n} {hz : q.evidence z}
    (edge : Bridge G ((q.move z hz).live G) (q.move z hz).outcome (q.move z hz).evidence u v) :
    Bridge G (q.live G) q.outcome q.evidence u v :=
  ⟨move_live_subset edge.1, move_live_subset edge.2.1, edge.2.2.imp id (Or.imp
    (fun e => ⟨(free_iff_after edge.1.1.2).mpr e.1, e.2⟩)
    (fun e => ⟨(free_iff_after edge.2.1.1.2).mpr e.1, e.2⟩))⟩

/-- Both directions of preservation of the vertices connected to an
outcome factor after a single eligible move. -/
theorem linked_iff_after_move {G : MixedGraph n} {q : Query n} {z u : Fin n}
    (hz : q.evidence z) (eligible : ¬ q.linked G z) :
    q.linked G u ↔ (q.move z hz).linked G u := by
  constructor
  · rintro ⟨t, path, hit⟩
    have touchedLinked : q.linked G t := ⟨t, .refl t, hit⟩
    have lift {v : Fin n}
        (route : Reach (Bridge G (q.live G) q.outcome q.evidence) u v)
        (endLinked : q.linked G v) :
        Reach (Bridge G ((q.move z hz).live G) (q.move z hz).outcome
          (q.move z hz).evidence) u v := by
      induction route with
      | refl => exact .refl _
      | extend _ edge ih =>
        have previous := linked_of_steps (.extend (.refl _) edge) endLinked
        exact .extend (ih previous)
          (bridge_after (linked_retained hz eligible previous)
            (linked_retained hz eligible endLinked) edge)
    exact ⟨t, lift path touchedLinked, linked_retained hz eligible touchedLinked, hit.2⟩
  · rintro ⟨t, path, hit⟩
    exact ⟨t, reach_map bridge_before path, move_live_subset hit.1, hit.2⟩

/-- No member of an outcome-linked district is lost through an eligible
move, and all its bidirected routes are unchanged. -/
theorem district_eq_after_move {G : MixedGraph n} {q : Query n} {z u : Fin n}
    (hz : q.evidence z) (eligible : ¬ q.linked G z) (linked : q.linked G u) :
    (q.move z hz).district G u = q.district G u := by
  funext v
  apply propext
  constructor
  · intro new
    exact ⟨move_live_subset new.1,
      reach_map (fun e => ⟨move_live_subset e.1, move_live_subset e.2.1, e.2.2⟩) new.2⟩
  · intro old
    have lift {t : Fin n} (route : Reach (Within (q.live G) (Bidir G)) u t) :
        (q.move z hz).live G t ∧ Reach (Within ((q.move z hz).live G) (Bidir G)) u t := by
      induction route with
      | refl => exact ⟨linked_retained hz eligible linked, .refl _⟩
      | extend earlier edge ih =>
        have reached := (linked_iff_of_steps
          (paths_in_district_are_bridges (.extend earlier edge))).mp linked
        have atEnd := linked_retained hz eligible reached
        exact ⟨atEnd, .extend ih.2 ⟨ih.1, atEnd, edge.2.2⟩⟩
    exact lift old.2

end Query

open Query

/-- Each remaining evidence vertex is in an outcome-linked block. -/
def Stationary (G : MixedGraph n) (q : Query n) : Prop :=
  ∀ z, q.evidence z → q.linked G z

theorem live_iff_linked_at_stationary {G : MixedGraph n} {q : Query n}
    (finished : Stationary G q) {v : Fin n} : q.live G v ↔ q.linked G v := by
  refine ⟨?_, linked_is_live⟩
  intro live
  obtain ⟨t, terminal, route⟩ := route_to_first_terminal live
  have last : q.linked G t :=
    terminal.elim (fun outcome => ⟨t, .refl t, q.live_of_terminal G terminal,
      Or.inl outcome⟩) (fun ev => finished t ev)
  exact linked_of_steps (reach_map free_edge_bridge route) last

/-- A sequence moves only evidence vertices whose factor blocks avoid the outcome. -/
inductive Moves (G : MixedGraph n) (start : Query n) : Query n → Prop
  | refl : Moves G start start
  | step {q} : Moves G start q → (z : Fin n) → (hz : q.evidence z) →
      ¬ q.linked G z → Moves G start (q.move z hz)

namespace Moves

variable {G : MixedGraph n} {start last : Query n}

theorem trans {middle : Query n} (p : Moves G start middle) (q : Moves G middle last) :
    Moves G start last := by
  induction q with
  | refl => exact p
  | step _ z hz eligible ih => exact .step ih z hz eligible

theorem linked_iff (run : Moves G start last) (v : Fin n) :
    start.linked G v ↔ last.linked G v := by
  induction run with
  | refl => exact Iff.rfl
  | step _ _ hz eligible ih => exact ih.trans (linked_iff_after_move hz eligible)

theorem district_eq (run : Moves G start last) {v : Fin n} (linked : start.linked G v) :
    last.district G v = start.district G v := by
  induction run with
  | refl => rfl
  | step p _ hz eligible ih =>
    exact (district_eq_after_move hz eligible ((p.linked_iff v).mp linked)).trans ih

theorem evidence_iff (run : Moves G start last) (v : Fin n) :
    last.evidence v ↔ start.evidence v ∧ last.allowed v := by
  induction run with
  | refl => exact ⟨fun h => ⟨h, start.evidence_allowed h⟩, And.left⟩
  | step _ _ _ _ ih =>
    exact ⟨fun h => ⟨(ih.mp h.1).1, (ih.mp h.1).2, h.2⟩,
      fun h => ⟨ih.mpr ⟨h.1, h.2.1⟩, h.2.2⟩⟩

/-- A stationary run keeps exactly the evidence in the original
outcome-linked blocks, independent of its order. -/
theorem stationary_evidence_iff (run : Moves G start last) (finished : Stationary G last)
    (v : Fin n) : last.evidence v ↔ start.evidence v ∧ start.linked G v := by
  refine ⟨fun h => ⟨((run.evidence_iff v).mp h).1, (run.linked_iff v).mpr (finished v h)⟩, ?_⟩
  rintro ⟨he, linked⟩
  exact (run.evidence_iff v).mpr ⟨he, (linked_is_live ((run.linked_iff v).mp linked)).1⟩

end Moves

/-- Tian's failure test in terms of the blocks that survive conditional normalization. -/
def TianFails (G : MixedGraph n) (q : Query n) (intrinsic : Vertices n → Prop) : Prop :=
  ∃ v, q.linked G v ∧ ¬ intrinsic (q.district G v)

/-- The reduced joint's intrinsic-district failure test. -/
def JointFails (G : MixedGraph n) (q : Query n) (intrinsic : Vertices n → Prop) : Prop :=
  ∃ v, q.live G v ∧ ¬ intrinsic (q.district G v)

/-- The conditional factor test agrees with the exact reduced joint
test for any property of a district, including intrinsic reachability. -/
theorem tian_fails_iff_joint_fails {G : MixedGraph n} {start last : Query n}
    (run : Moves G start last) (finished : Stationary G last)
    (intrinsic : Vertices n → Prop) :
    TianFails G start intrinsic ↔ JointFails G last intrinsic := by
  constructor
  · rintro ⟨v, linked, fails⟩
    exact ⟨v, linked_is_live ((run.linked_iff v).mp linked),
      (run.district_eq linked).symm ▸ fails⟩
  · rintro ⟨v, live, fails⟩
    have linked := (run.linked_iff v).mpr ((live_iff_linked_at_stationary finished).mp live)
    exact ⟨v, linked, run.district_eq linked ▸ fails⟩

noncomputable def evidenceSize (q : Query n) : Nat :=
  ((List.finRange n).filter (fun v => @decide (q.evidence v)
    (Classical.propDecidable _))).length

private theorem move_evidence_decreases {q : Query n} {z : Fin n} (hz : q.evidence z) :
    evidenceSize (q.move z hz) < evidenceSize q := by
  classical
  let old := (List.finRange n).filter (fun v => decide (q.evidence v))
  let remaining := old.filter (· != z)
  have remaining_matches : evidenceSize (q.move z hz) = remaining.length := by
    have tests : (fun v => decide ((q.move z hz).evidence v)) =
        fun v => (v != z) && decide (q.evidence v) := by
      funext v
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne]
      exact And.comm
    unfold evidenceSize
    rw [tests]
    simp [remaining, old, List.filter_filter]
  have seen : z ∈ old := by simp [old, hz]
  have absent : z ∉ remaining := by simp [remaining]
  have subset : remaining.Sublist old := List.filter_sublist
  have strict : remaining.length < old.length :=
    Nat.lt_of_le_of_ne subset.length_le
      (fun eq => absent ((subset.length_eq.mp eq).symm ▸ seen))
  exact remaining_matches.symm ▸ strict

/-- Moving eligible observations can always continue to a stationary query. -/
theorem exists_stationary_run (G : MixedGraph n) (start : Query n) :
    ∃ last, Moves G start last ∧ Stationary G last := by
  classical
  suffices h : ∀ k (q : Query n), evidenceSize q = k →
      ∃ last, Moves G q last ∧ Stationary G last from h _ start rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k smaller =>
    intro q eq
    by_cases finished : Stationary G q
    · exact ⟨q, .refl, finished⟩
    · have available : ∃ z, q.evidence z ∧ ¬ q.linked G z := by
        apply Classical.byContradiction
        intro none
        exact finished fun z ev => Classical.byContradiction fun unlinked =>
          none ⟨z, ev, unlinked⟩
      obtain ⟨z, ev, unlinked⟩ := available
      obtain ⟨last, later, stationary⟩ :=
        smaller _ (eq ▸ move_evidence_decreases ev) (q.move z ev) rfl
      exact ⟨last, (Moves.step .refl z ev unlinked).trans later, stationary⟩

end
end OpenCausalScience.Papers.Tian2004.Reduction
