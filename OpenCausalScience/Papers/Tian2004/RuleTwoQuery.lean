module
public import OpenCausalScience.Graph.MixedPath
public import OpenCausalScience.Papers.Tian2004.Reduction
public import OpenCausalScience.Papers.Tian2004.RuleTwoIncidence

/-! IDC's singleton graph test is exactly absence of an outcome link in
Tian's factor graph. The intervention vertices in the full graph have no
arrowheads and are conditioned on. An active walk can therefore use only
random ancestors of the outcome and evidence. See Shpitser and Pearl (2006),
Figure 3, line 1. Source: https://ftp.cs.ucla.edu/pub/stat_ser/r329-uai.pdf
-/

namespace OpenCausalScience.Papers.Tian2004.RuleTwoQuery

open MixedGraph FactorGraph Reduction RuleTwoIncidence

@[expose] public section

variable {n : Nat} {G : MixedGraph n} {q : Query n} {z : Fin n}

private noncomputable abbrev Full (G : MixedGraph n) (q : Query n) (z : Fin n) :=
  exchangeCut G q.allowed z
private noncomputable abbrev Sub (G : MixedGraph n) (q : Query n) (z : Fin n) :=
  ancestralCut G (q.live G) z
private noncomputable abbrev FullCond (q : Query n) (z : Fin n) :=
  exchangeEvidence q.allowed q.evidence z
private noncomputable abbrev SubCond (q : Query n) (z : Fin n) := evidence q.evidence z

private theorem full_spec {u v : Fin n} {a b : Bool} :
    (Full G q z).edge u a v b = true ↔
      ((q.allowed u ∨ a = false) ∧ keepsAfterExchange z u a) ∧
      ((q.allowed v ∨ b = false) ∧ keepsAfterExchange z v b) ∧ G.edge u a v b = true :=
  keep_marks_iff

private theorem full_to_sub {u v : Fin n} {a b : Bool} (hu : q.live G u) (hv : q.live G v)
    (e : (Full G q z).edge u a v b = true) : (Sub G q z).edge u a v b = true := by
  obtain ⟨⟨_, cutU⟩, ⟨_, cutV⟩, original⟩ := full_spec.mp e
  exact (ancestral_cut_spec G (q.live G) z _ _ _ _).mpr ⟨hu, hv, original, cutU, cutV⟩

private theorem sub_to_full {u v : Fin n} {a b : Bool}
    (e : (Sub G q z).edge u a v b = true) : (Full G q z).edge u a v b = true := by
  obtain ⟨hu, hv, original, cutU, cutV⟩ := (ancestral_cut_spec G (q.live G) z _ _ _ _).mp e
  exact full_spec.mpr ⟨⟨Or.inl hu.1, cutU⟩, ⟨Or.inl hv.1, cutV⟩, original⟩

private theorem full_anc_to_sub {v : Fin n}
    (h : (Full G q z).AncestorOf (FullCond q z) v) (vAllowed : q.allowed v) :
    q.live G v ∧ (Sub G q z).AncestorOf (SubCond q z) v := by
  classical
  induction h with
  | @conditioned v included =>
    have h : q.evidence v ∧ v ≠ z := by simpa [exchangeEvidence, vAllowed] using included
    exact ⟨q.live_of_terminal G (Or.inr h.1), .conditioned (by simpa [evidence] using h)⟩
  | @parent u v edge _ ih =>
    have e := full_spec.mp edge
    have vAllowed := e.2.1.1.resolve_right (by decide)
    obtain ⟨vLive, vAncestor⟩ := ih vAllowed
    have uLive := Query.parent_live ⟨‹q.allowed u›, vAllowed, e.2.2⟩ vLive
    exact ⟨uLive, .parent (full_to_sub uLive vLive edge) vAncestor⟩

private theorem sub_anc_to_full {v : Fin n} (h : (Sub G q z).AncestorOf (SubCond q z) v) :
    (Full G q z).AncestorOf (FullCond q z) v := by
  classical
  induction h with
  | @conditioned v included =>
    have here : q.evidence v ∧ v ≠ z := by simpa [evidence] using included
    exact .conditioned (by simp [exchangeEvidence, here])
  | parent edge _ ih => exact .parent (sub_to_full edge) ih

private theorem same_evidence {v : Fin n} (allowed : q.allowed v) :
    FullCond q z v = SubCond q z v := by
  simp [exchangeEvidence, evidence, allowed]

private theorem turn_to_sub {s : Arrival n} {a : Bool} (allowed : q.allowed s.1)
    (turn : (Full G q z).openTurn (FullCond q z) s a) :
    (Sub G q z).openTurn (SubCond q z) s a := by
  unfold openTurn at *
  split at turn
  · rename_i h
    simp only [h, ite_true]
    exact (full_anc_to_sub turn allowed).2
  · rename_i h
    simpa [h, same_evidence allowed] using turn

private theorem turn_to_full {s : Arrival n} {a : Bool} (allowed : q.allowed s.1)
    (turn : (Sub G q z).openTurn (SubCond q z) s a) :
    (Full G q z).openTurn (FullCond q z) s a := by
  unfold openTurn at *
  split at turn
  · rename_i h
    simp only [h, ite_true]
    exact sub_anc_to_full turn
  · rename_i h
    simpa [h, same_evidence allowed] using turn

private theorem head_start_live (directedMixed : ∀ u v, G.edge u false v false = false)
    {s last : Arrival n} {vs : List (Fin n)}
    (walk : (Full G q z).ActiveWalk (FullCond q z) s vs last)
    (endLive : q.live G last.1) (head : s.2 = true) (allowed : q.allowed s.1) :
    q.live G s.1 := by
  induction walk with
  | nil => exact endLive
  | @cons u v _ _ move _ ih =>
    obtain ⟨out, edge, turn⟩ := move
    have e := full_spec.mp edge
    cases out
    · cases h : v.2
      · have noEdge := directedMixed u.1 v.1
        have original := e.2.2
        simp [h, noEdge] at original
      · have vAllowed : q.allowed v.1 := e.2.1.1.resolve_right (by simp [h])
        have dir : Dir G u.1 v.1 := by simpa [Dir, h] using e.2.2
        exact Query.parent_live ⟨allowed, vAllowed, dir⟩ (ih endLive h vAllowed)
    · have ancestor : (Full G q z).AncestorOf (FullCond q z) u.1 :=
        by simpa [openTurn, head] using turn
      exact (full_anc_to_sub ancestor allowed).1

private theorem next_live (directedMixed : ∀ u v, G.edge u false v false = false)
    {u : Fin n} {a : Bool} {v last : Arrival n} {vs : List (Fin n)}
    (e : (Full G q z).edge u a v.1 v.2 = true) (uLive : q.live G u)
    (walk : (Full G q z).ActiveWalk (FullCond q z) v vs last) (endLive : q.live G last.1) :
    q.live G v.1 := by
  classical
  have full := full_spec.mp e
  cases h : v.2
  · cases a
    · have noEdge := directedMixed u v.1
      have original := full.2.2
      simp [h, noEdge] at original
    · cases walk with
      | nil => exact endLive
      | cons move _ =>
        obtain ⟨_, _, turn⟩ := move
        have notConditioned : FullCond q z v.1 = false := by simpa [openTurn, h] using turn
        have vAllowed : q.allowed v.1 := by
          by_cases inside : q.allowed v.1
          · exact inside
          · simp [exchangeEvidence, inside] at notConditioned
        have reverse : Dir G v.1 u := by
          unfold Dir
          rw [G.symmetric]
          simpa [h] using full.2.2
        exact Query.parent_live ⟨vAllowed, uLive.1, reverse⟩ uLive
  · exact head_start_live directedMixed walk endLive h (full.2.1.1.resolve_right (by simp [h]))

private theorem full_active_to_sub (directedMixed : ∀ u v, G.edge u false v false = false)
    {s last : Arrival n} {vs : List (Fin n)}
    (walk : (Full G q z).ActiveWalk (FullCond q z) s vs last)
    (startLive : q.live G s.1) (endLive : q.live G last.1) :
    (Sub G q z).ActiveWalk (SubCond q z) s vs last := by
  induction walk with
  | nil => exact .nil _
  | cons move tail ih =>
    obtain ⟨out, edge, turn⟩ := move
    have alive := next_live directedMixed edge startLive tail endLive
    exact .cons ⟨out, full_to_sub startLive alive edge, turn_to_sub startLive.1 turn⟩ (ih alive endLive)

private theorem sub_step_to_full {s t : Arrival n} (step : (Sub G q z).Step (SubCond q z) s t) :
    (Full G q z).Step (FullCond q z) s t := by
  obtain ⟨out, edge, turn⟩ := step
  have allowed := ((ancestral_cut_spec G (q.live G) z _ _ _ _).mp edge).1.1
  exact ⟨out, sub_to_full edge, turn_to_full allowed turn⟩

private theorem full_walk_iff_sub_walk (hz : q.evidence z)
    (directedMixed : ∀ u v, G.edge u false v false = false) :
    (Full G q z).WalkConnected (singleton z) (membership q.outcome) (FullCond q z) ↔
    (Sub G q z).WalkConnected (singleton z) (membership q.outcome) (SubCond q z) := by
  constructor
  · rintro ⟨first, last, ⟨source, mark, initial, edge⟩, reach, finish⟩
    have eq : source = z := by simpa [RuleTwoIncidence.singleton] using initial
    subst source
    have zLive := q.live_of_terminal G (Or.inr hz)
    have lastLive := q.live_of_terminal G
      (Or.inl (by simpa [membership] using finish : q.outcome last.1))
    obtain ⟨vs, walk⟩ := MixedGraph.reachable_iff_active_walk.mp reach
    have firstLive := next_live directedMixed edge zLive walk lastLive
    have walksInSub := full_active_to_sub directedMixed walk firstLive lastLive
    exact ⟨first, last, ⟨z, mark, initial, full_to_sub zLive firstLive edge⟩,
      MixedGraph.reachable_iff_active_walk.mpr ⟨vs, walksInSub⟩, finish⟩
  · rintro ⟨first, last, ⟨source, mark, initial, edge⟩, reach, finish⟩
    exact ⟨first, last, ⟨source, mark, initial, sub_to_full edge⟩,
      reach_map sub_step_to_full reach, finish⟩

private theorem cut_ancestor {u : Fin n} (hz : q.evidence z) (uLive : q.live G u) :
    (Sub G q z).AncestorOf
      (fun v => SubCond q z v || membership q.outcome v || singleton z v) u := by
  classical
  obtain ⟨t, terminal, route⟩ := q.route_to_first_terminal uLive
  have target : (SubCond q z t || membership q.outcome t || singleton z t) = true := by
    obtain hy | hZ := terminal
    · simp [membership, hy]
    · by_cases ht : t = z
      · simp [RuleTwoIncidence.singleton, ht]
      · simp [evidence, hZ, ht]
  have propagate {a b : Fin n}
      (p : Reach (fun a b => Free q.outcome q.evidence a ∧ Within (q.live G) (Dir G) a b) a b)
      (endAnc : (Sub G q z).AncestorOf
        (fun v => SubCond q z v || membership q.outcome v || singleton z v) b) :
      (Sub G q z).AncestorOf
        (fun v => SubCond q z v || membership q.outcome v || singleton z v) a := by
    induction p with
    | refl => exact endAnc
    | @extend a b _ step ih =>
      obtain ⟨free, ha, hb, dir⟩ := step
      have notZ : a ≠ z := fun same => free.2 (same.symm ▸ hz)
      have edge := (ancestral_cut_spec G (q.live G) z a false b true).mpr
        ⟨ha, hb, dir, Or.inl notZ, Or.inr rfl⟩
      exact ih (.parent edge endAnc)
  exact propagate route (.conditioned target)

/-- Rule 2 can exchange the evidence vertex exactly when its district is
outside the factor blocks that reach an outcome. This uses IDC's full
mutilated graph, including the conditioned intervention vertices. -/
theorem rule_two_separated_iff_not_linked (hz : q.evidence z)
    (directedMixed : ∀ u v, G.edge u false v false = false) :
    ¬ (exchangeCut G q.allowed z).WalkConnected (singleton z) (membership q.outcome)
      (exchangeEvidence q.allowed q.evidence z) ↔ ¬ q.linked G z := by
  have equivalence := (full_walk_iff_sub_walk hz directedMixed).trans
    (walk_connected_iff_linked (ancestral_cut_spec G (q.live G) z) hz
      (q.live_of_terminal G (Or.inr hz)) (fun _ => q.disjoint)
      (fun _ hy => q.live_of_terminal G (Or.inl hy)) directedMixed (fun _ => cut_ancestor hz))
  exact not_congr equivalence

/-- In a graph with directed and bidirected edges, IDC can exchange an
observed `z` precisely when its factor block does not reach the outcome.
The left side is m-separation by the other evidence and the intervention
vertices in IDC’s mutilated graph. -/
theorem rule_two_path_separated_iff_not_linked (hz : q.evidence z)
    (directedMixed : ∀ u v, G.edge u false v false = false) :
    ¬ (exchangeCut G q.allowed z).PathConnected (singleton z) (membership q.outcome)
      (exchangeEvidence q.allowed q.evidence z) ↔ ¬ q.linked G z := by
  have firstOutside : ∀ v, RuleTwoIncidence.singleton z v = true → FullCond q z v = false := by
    intro v hv
    have eq : v = z := by simpa [RuleTwoIncidence.singleton] using hv
    subst v
    simp [exchangeEvidence, q.evidence_allowed hz]
  have endpointsDisjoint : ∀ v, RuleTwoIncidence.singleton z v = true →
      membership q.outcome v = false := by
    intro v hv
    have eq : v = z := by simpa [RuleTwoIncidence.singleton] using hv
    subst v
    have notOutcome : ¬ q.outcome z := fun hy => q.disjoint hy hz
    simp [membership, notOutcome]
  have walks := (exchangeCut G q.allowed z).walkConnected_iff_pathConnected
    (singleton z) (membership q.outcome) (exchangeEvidence q.allowed q.evidence z)
    firstOutside endpointsDisjoint
  exact (not_congr walks.symm).trans (rule_two_separated_iff_not_linked hz directedMixed)

end
end OpenCausalScience.Papers.Tian2004.RuleTwoQuery
