module
public import OpenCausalScience.Papers.Tian2004.FactorGraph

/-! The factor block of a conditioning variable reaches an outcome exactly
when the singleton action/observation exchange test finds an active walk.
The ancestor set includes the exchanged variable itself. For the factor
scopes, see Tian (2004), §4.
Source: https://faculty.sites.iastate.edu/jtian/files/inline-files/uai-04.pdf
-/

namespace OpenCausalScience.Papers.Tian2004.RuleTwoIncidence

open MixedGraph FactorGraph

@[expose] public section

variable {n : Nat}

abbrev Marks (n : Nat) := Fin n → Bool

open Classical in
noncomputable def membership (S : Vertices n) : Marks n := fun v => decide (S v)

def singleton (z : Fin n) : Marks n := fun v => decide (v = z)

open Classical in
noncomputable def evidence (Z : Vertices n) (z : Fin n) : Marks n :=
  fun v => decide (Z v ∧ v ≠ z)

/-- The edges left by inducing on `live` and removing each edge with a tail at `z`. -/
def OutgoingCut (G H : MixedGraph n) (live : Vertices n) (z : Fin n) : Prop :=
  ∀ u a v b, H.edge u a v b = true ↔
    live u ∧ live v ∧ G.edge u a v b = true ∧
      (u ≠ z ∨ a = true) ∧ (v ≠ z ∨ b = true)

/-- The turn constraint obtained by provisionally allowing all colliders. -/
private def LooseStep (H : MixedGraph n) (W : Marks n) (s t : Arrival n) : Prop :=
  ∃ a, H.edge s.1 a t.1 t.2 = true ∧ ((s.2 && a) = true ∨ W s.1 = false)

private def From (H : MixedGraph n) (z : Fin n) (W : Marks n) (v : Arrival n) : Prop :=
  ∃ s, H.Seed (singleton z) s ∧ Reach (H.Step W) s v

private theorem from_edge {H : MixedGraph n} {z : Fin n} {W : Marks n} {t : Arrival n}
    {a : Bool} (edge : H.edge z a t.1 t.2 = true) : From H z W t :=
  ⟨t, ⟨z, a, by simp [singleton], edge⟩, .refl _⟩

private theorem from_extend {H : MixedGraph n} {z : Fin n} {W : Marks n} {s t : Arrival n}
    (path : From H z W s) (step : H.Step W s t) : From H z W t := by
  obtain ⟨first, seed, reach⟩ := path
  exact ⟨first, seed, .extend reach step⟩

private theorem connected_of_from {H : MixedGraph n} {z : Fin n} {W R : Marks n}
    {t : Arrival n} (path : From H z W t) (right : R t.1 = true) :
    H.WalkConnected (singleton z) R W := by
  obtain ⟨first, seed, reach⟩ := path
  exact ⟨first, t, seed, reach, right⟩

private theorem unconditioned_of_inactive {H : MixedGraph n} {W : Marks n} {v : Fin n}
    (inactive : ¬ H.AncestorOf W v) : W v = false := by
  cases h : W v with
  | false => rfl
  | true => exact (inactive (.conditioned h)).elim

private theorem from_tail_of_ancestor {H : MixedGraph n} {z : Fin n} {W : Marks n} {v : Fin n}
    (ancestral : H.AncestorOf (singleton z) v) (inactive : ¬ H.AncestorOf W v) :
    v = z ∨ From H z W (v, false) := by
  induction ancestral with
  | conditioned hx => exact Or.inl (by simpa [singleton] using hx)
  | @parent u v edge _ ih =>
    have inverse := (H.symmetric u false v true).symm.trans edge
    obtain rfl | path := ih (fun h => inactive (.parent edge h))
    · exact Or.inr (from_edge (t := (u, false)) inverse)
    · apply Or.inr
      apply from_extend path
      exact ⟨true, inverse, by simpa [openTurn] using (unconditioned_of_inactive
        (fun h => inactive (.parent edge h)))⟩

private theorem finish_of_ancestor {H : MixedGraph n} {z : Fin n} {W R : Marks n} {v : Fin n}
    (ancestral : H.AncestorOf R v) (inactive : ¬ H.AncestorOf W v) {a : Bool}
    (path : From H z W (v, a)) : H.WalkConnected (singleton z) R W := by
  induction ancestral generalizing a with
  | conditioned hr => exact connected_of_from path hr
  | @parent u v edge _ ih =>
    apply ih (fun h => inactive (.parent edge h))
    apply from_extend path (t := (v, true))
    exact ⟨false, edge, by simpa [openTurn] using unconditioned_of_inactive inactive⟩

private theorem ancestor_split {H : MixedGraph n} {W R S : Marks n} {v : Fin n}
    (h : H.AncestorOf (fun u => W u || R u || S u) v) :
    H.AncestorOf W v ∨ H.AncestorOf R v ∨ H.AncestorOf S v := by
  induction h with
  | conditioned h =>
    simp only [Bool.or_eq_true] at h
    obtain h | h := h
    · exact h.elim (fun h => Or.inl (.conditioned h)) (fun h => Or.inr (Or.inl (.conditioned h)))
    · exact Or.inr (Or.inr (.conditioned h))
  | parent edge _ ih =>
    exact ih.elim (fun h => Or.inl (.parent edge h)) fun h =>
      h.elim (fun h => Or.inr (Or.inl (.parent edge h))) (fun h => Or.inr (Or.inr (.parent edge h)))

private theorem loose_active {H : MixedGraph n} {live : Vertices n} {z : Fin n} {W R : Marks n}
    (edgesLive : ∀ u a v b, H.edge u a v b = true → live u)
    (ancestral : ∀ v, live v → H.AncestorOf (fun u => W u || R u || singleton z u) v)
    {t : Arrival n} (loose : Reach (LooseStep H W) (z, false) t) :
    t = (z, false) ∨ From H z W t ∨ H.WalkConnected (singleton z) R W := by
  induction loose with
  | refl => exact Or.inl rfl
  | @extend v t _ move ih =>
    obtain ⟨outgoing, edge, turn⟩ := move
    obtain same | path | done := ih
    · subst v
      exact Or.inr (Or.inl (from_edge edge))
    · by_cases collider : (v.2 && outgoing) = true
      · by_cases activated : H.AncestorOf W v.1
        · exact Or.inr (Or.inl (from_extend path ⟨outgoing, edge, by simpa [openTurn, collider] using activated⟩))
        · obtain bad | y | zAncestor := ancestor_split
            (ancestral _ (edgesLive _ _ _ _ edge))
          · exact (activated bad).elim
          · exact Or.inr (Or.inr (finish_of_ancestor (a := v.2) y activated (by simpa using path)))
          · obtain equal | earlier := from_tail_of_ancestor zAncestor activated
            · exact Or.inr (Or.inl (from_edge (by simpa [equal] using edge)))
            · exact Or.inr (Or.inl (from_extend earlier
                ⟨outgoing, edge, by simpa [openTurn] using unconditioned_of_inactive activated⟩))
      · have noncollider : (v.2 && outgoing) = false := Bool.eq_false_iff.mpr collider
        exact Or.inr (Or.inl (from_extend path
          ⟨outgoing, edge, by simpa [openTurn, noncollider] using turn.resolve_left collider⟩))
    · exact Or.inr (Or.inr done)

variable {G H : MixedGraph n} {live Y Z : Vertices n} {z : Fin n}

private theorem free_evidence (h : Free Y Z v) : evidence Z z v = false := by
  simp [evidence, h.2]

private theorem cut_bidir (cut : OutgoingCut G H live z) {u v : Fin n}
    (hu : live u) (hv : live v) (edge : Bidir G u v) : H.edge u true v true = true :=
  (cut u true v true).mpr ⟨hu, hv, edge, Or.inr rfl, Or.inr rfl⟩

private theorem cut_dir (cut : OutgoingCut G H live z) {u v : Fin n}
    (hu : live u) (hv : live v) (notZ : u ≠ z) (edge : Dir G u v) :
    H.edge u false v true = true :=
  (cut u false v true).mpr ⟨hu, hv, edge, Or.inl notZ, Or.inr rfl⟩

private theorem bridge_loose (cut : OutgoingCut G H live z) (hz : Z z)
    {v : Fin n} (route : Reach (Bridge G live Y Z) z v) :
    ∃ a, Reach (LooseStep H (evidence Z z)) (z, false) (v, a) ∧
      (a = false → evidence Z z v = false) := by
  induction route with
  | refl => exact ⟨false, .refl _, fun _ => by simp [evidence]⟩
  | @extend u v _ step ih =>
    obtain ⟨a, earlier, tail⟩ := ih
    obtain ⟨hu, hv, bidir | ⟨free, edge⟩ | ⟨free, edge⟩⟩ := step
    · refine ⟨true, .extend earlier ⟨true, cut_bidir cut hu hv bidir, ?_⟩, by simp⟩
      cases a with
      | false => exact Or.inr (tail rfl)
      | true => exact Or.inl rfl
    · have sourceNotZ : u ≠ z := fun same => free.2 (same.symm ▸ hz)
      exact ⟨true, .extend earlier ⟨false, cut_dir cut hu hv sourceNotZ edge,
        Or.inr (free_evidence free)⟩, by simp⟩
    · have sourceNotZ : v ≠ z := fun same => free.2 (same.symm ▸ hz)
      have inv := (H.symmetric v false u true).symm.trans (cut_dir cut hv hu sourceNotZ edge)
      refine ⟨false, .extend earlier ⟨true, inv, ?_⟩, fun _ => free_evidence free⟩
      cases a with
      | false => exact Or.inr (tail rfl)
      | true => exact Or.inl rfl

private theorem connected_of_linked (cut : OutgoingCut G H live z) (hz : Z z)
    (disjoint : ∀ v, Y v → ¬ Z v) (outcomesLive : ∀ v, Y v → live v)
    (ancestors : ∀ v, live v → H.AncestorOf
      (fun u => evidence Z z u || membership Y u || singleton z u) v)
    (linked : Linked G live Y Z z) :
    H.WalkConnected (singleton z) (membership Y) (evidence Z z) := by
  have finish {t : Arrival n}
      (path : Reach (LooseStep H (evidence Z z)) (z, false) t) (hy : Y t.1) :
      H.WalkConnected (singleton z) (membership Y) (evidence Z z) := by
    obtain same | reached | done := loose_active
      (fun u a v b edge => ((cut u a v b).mp edge).1) ancestors path
    · have hyz : Y z := by simpa [same] using hy
      exact (disjoint z hyz hz).elim
    · exact connected_of_from reached (by simp [membership, hy])
    · exact done
  obtain ⟨v, route, hv, hit | ⟨y, hy, edge⟩⟩ := linked
  · obtain ⟨a, loose, _⟩ := bridge_loose cut hz route
    exact finish (t := (v, a)) loose hit
  · obtain ⟨a, loose, tail⟩ := bridge_loose cut hz route
    have sourceNotZ : y ≠ z := fun same => disjoint y hy (same.symm ▸ hz)
    have inverse := (H.symmetric y false v true).symm.trans
      (cut_dir cut (outcomesLive y hy) hv sourceNotZ edge)
    apply finish (t := (y, false)) _ hy
    refine .extend loose ⟨true, inverse, ?_⟩
    cases a with
    | false => exact Or.inr (tail rfl)
    | true => exact Or.inl rfl

private theorem incidence_step (cut : OutgoingCut G H live z)
    (directedMixed : ∀ u v, G.edge u false v false = false)
    {s t : Arrival n} (route : Reach (Bridge G live Y Z) z s.1)
    (step : H.Step (evidence Z z) s t) :
    Linked G live Y Z z ∨ (live t.1 ∧ Reach (Bridge G live Y Z) z t.1) ∨
      (t.2 = false ∧ evidence Z z t.1 = true) := by
  classical
  obtain ⟨out, edge, turn⟩ := step
  obtain ⟨sourceLive, targetLive, original, sourceMark, targetMark⟩ := (cut _ _ _ _).mp edge
  cases hout : out <;> cases harr : t.2
  · have impossible := directedMixed s.1 t.1
    rw [hout, harr, impossible] at original
    contradiction
  · rw [hout] at sourceMark
    have sourceNotZ := sourceMark.resolve_right Bool.false_ne_true
    rw [hout, harr] at original
    have outside : evidence Z z s.1 = false := by simpa [openTurn, hout] using turn
    have notConditioning : ¬Z s.1 := fun hz => by simp [evidence, hz, sourceNotZ] at outside
    by_cases hy : Y s.1
    · exact Or.inl ⟨s.1, route, sourceLive, Or.inl hy⟩
    · exact Or.inr (Or.inl ⟨targetLive, .extend route
        ⟨sourceLive, targetLive, Or.inr (Or.inl ⟨⟨hy, notConditioning⟩, original⟩)⟩⟩)
  · rw [harr] at targetMark
    have targetNotZ := targetMark.resolve_right Bool.false_ne_true
    rw [hout, harr] at original
    have inverse := (G.symmetric t.1 false s.1 true).trans original
    by_cases hy : Y t.1
    · exact Or.inl ⟨s.1, route, sourceLive, Or.inr ⟨t.1, hy, inverse⟩⟩
    · by_cases hz : Z t.1
      · exact Or.inr (Or.inr ⟨rfl, by simp [evidence, hz, targetNotZ]⟩)
      · exact Or.inr (Or.inl ⟨targetLive, .extend route
          ⟨sourceLive, targetLive, Or.inr (Or.inr ⟨⟨hy, hz⟩, inverse⟩)⟩⟩)
  · rw [hout, harr] at original
    exact Or.inr (Or.inl ⟨targetLive, .extend route ⟨sourceLive, targetLive, Or.inl original⟩⟩)

private theorem linked_of_connected (cut : OutgoingCut G H live z) (zLive : live z)
    (disjoint : ∀ v, Y v → ¬ Z v)
    (directedMixed : ∀ u v, G.edge u false v false = false)
    (connected : H.WalkConnected (singleton z) (membership Y) (evidence Z z)) :
    Linked G live Y Z z := by
  obtain ⟨first, last, ⟨source, out, hs, edge⟩, reach, right⟩ := connected
  have equal : source = z := by simpa [singleton] using hs
  subst source
  have firstStep : H.Step (evidence Z z) (z, false) first :=
    ⟨out, edge, by simp [openTurn, evidence]⟩
  have scan {t : Arrival n} (walk : Reach (H.Step (evidence Z z)) (z, false) t) :
      Linked G live Y Z z ∨ (live t.1 ∧ Reach (Bridge G live Y Z) z t.1) ∨
        (t.2 = false ∧ evidence Z z t.1 = true) := by
    induction walk with
    | refl => exact Or.inr (Or.inl ⟨zLive, .refl _⟩)
    | @extend u _ _ step ih =>
      obtain linked | ⟨_, previous⟩ | ⟨arrived, conditioned⟩ := ih
      · exact Or.inl linked
      · exact incidence_step cut directedMixed previous step
      · obtain ⟨out, _, turn⟩ := step
        have outside : evidence Z z u.1 = false := by simpa [openTurn, arrived] using turn
        simp [conditioned] at outside
  obtain linked | ⟨alive, previous⟩ | ⟨_, conditioned⟩ :=
    scan (reach_trans (.extend (.refl _) firstStep) reach)
  · exact linked
  · exact ⟨last.1, previous, alive, Or.inl (by simpa [membership] using right)⟩
  · have hy : Y last.1 := by simpa [membership] using right
    simp [evidence, disjoint _ hy] at conditioned

/-- On the ancestral graph for the exchange test, a conditioning variable is
m-connected to the outcome exactly when its district belongs to a factor
block that uses the outcome. -/
theorem walk_connected_iff_linked (cut : OutgoingCut G H live z) (hz : Z z) (zLive : live z)
    (disjoint : ∀ v, Y v → ¬ Z v) (outcomesLive : ∀ v, Y v → live v)
    (directedMixed : ∀ u v, G.edge u false v false = false)
    (ancestors : ∀ v, live v → H.AncestorOf
      (fun u => evidence Z z u || membership Y u || singleton z u) v) :
    H.WalkConnected (singleton z) (membership Y) (evidence Z z) ↔ Linked G live Y Z z :=
  ⟨linked_of_connected cut zLive disjoint directedMixed,
    connected_of_linked cut hz disjoint outcomesLive ancestors⟩

open Classical in
/-- Keep an edge only when both endpoint marks pass the stated filter. -/
noncomputable def keepMarks (G : MixedGraph n) (keep : Fin n → Bool → Prop) : MixedGraph n where
  edge u a v b := if keep u a ∧ keep v b then G.edge u a v b else false
  symmetric u a v b := by
    simp [and_comm, G.symmetric u a v b]
  loop_free u a b := by simp [G.loop_free]
  no_arrow_of_undirected {u v w mark} h := by
    have original : G.edge u false v false = true := by
      split at h <;> simp_all
    simp [G.no_arrow_of_undirected (w := w) (mark := mark) original]

theorem keep_marks_iff {G : MixedGraph n} {keep : Fin n → Bool → Prop}
    {u v : Fin n} {a b : Bool} :
    (keepMarks G keep).edge u a v b = true ↔ keep u a ∧ keep v b ∧ G.edge u a v b = true := by
  classical
  simp [keepMarks, and_assoc]

def keepsAfterExchange (z v : Fin n) (a : Bool) : Prop := v ≠ z ∨ a = true

/-- Induce on the ancestor set and remove each edge with a tail at `z`. -/
noncomputable def ancestralCut (G : MixedGraph n) (live : Vertices n) (z : Fin n) : MixedGraph n :=
  keepMarks G fun v a => live v ∧ keepsAfterExchange z v a

theorem ancestral_cut_spec (G : MixedGraph n) (live : Vertices n) (z : Fin n) :
    OutgoingCut G (ancestralCut G live z) live z := by
  intro u a v b
  rw [ancestralCut, keep_marks_iff]
  unfold keepsAfterExchange
  constructor
  · rintro ⟨⟨hu, hza⟩, ⟨hv, hzb⟩, edge⟩
    exact ⟨hu, hv, edge, hza, hzb⟩
  · rintro ⟨hu, hv, edge, hza, hzb⟩
    exact ⟨⟨hu, hza⟩, ⟨hv, hzb⟩, edge⟩

/-- Keep the intervention vertices and remove each edge with an arrowhead at
an intervention vertex or a tail at `z`. On ADMGs this is the IDC cut. -/
noncomputable def exchangeCut (G : MixedGraph n) (allowed : Vertices n) (z : Fin n) : MixedGraph n :=
  keepMarks G fun v a => (allowed v ∨ a = false) ∧ keepsAfterExchange z v a

open Classical in
/-- IDC conditions on intervention vertices and on the other evidence. -/
noncomputable def exchangeEvidence (allowed Z : Vertices n) (z : Fin n) : Marks n :=
  fun v => decide (¬ allowed v ∨ (Z v ∧ v ≠ z))

end
end OpenCausalScience.Papers.Tian2004.RuleTwoIncidence
