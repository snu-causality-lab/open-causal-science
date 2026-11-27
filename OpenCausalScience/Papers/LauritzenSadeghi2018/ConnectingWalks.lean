module
public import OpenCausalScience.Graph.MixedSeparators

/-!
# Connecting walks and m-separation

Lauritzen and Sadeghi (2018), Lemma 2. In the mixed edge representation
used here, no arrowhead can meet a line endpoint. Hence collider sections
are singleton vertices. A collider in the ancestry of the conditioning set
can be replaced by a directed detour to a conditioned vertex and back.
-/

namespace OpenCausalScience.MixedGraph

@[expose] public section

variable {n : Nat} {G : MixedGraph n} {C : Fin n → Bool}

/-- A section preceded by an arrowhead cannot start with a line. -/
theorem collider_section_starts_without_line {u v w : Fin n} {mark : Bool}
    (first : G.edge u true v mark = true) :
    G.edge u false w false = false := by
  cases line : G.edge u false w false
  · rfl
  · exact Bool.noConfusion ((G.no_arrow_of_undirected line).symm.trans first)

/-- For the supported mixed graphs, the section conditions can be
expressed per interior vertex. Collider singletons must occur in `C`
and each vertex along a noncollider section must lie outside `C`. -/
def CStep (G : MixedGraph n) (C : Fin n → Bool) (s t : Arrival n) : Prop :=
  ∃ mark, G.edge s.1 mark t.1 t.2 = true ∧ C s.1 = (s.2 && mark)

/-- End sections are noncolliders, including the two end vertices. -/
def CConnected (G : MixedGraph n) (X Y C : Fin n → Bool) : Prop :=
  ∃ first last, G.Seed (fun u => X u && !C u) first ∧ Reach (G.CStep C) first last ∧
    Y last.1 = true ∧ C last.1 = false

private theorem c_step_is_active {s t : Arrival n} (step : G.CStep C s t) :
    G.Step C s t := by
  obtain ⟨outgoing, edge, visited⟩ := step
  refine ⟨outgoing, edge, ?_⟩
  unfold openTurn
  cases turn : s.2 && outgoing
  · simpa [turn] using visited.trans turn
  · simpa [turn] using AncestorOf.conditioned (G := G) (visited.trans turn)

private theorem splice {α : Type} {R : α → α → Prop} {u v w : α}
    (first : Reach R u v) (second : Reach R v w) : Reach R u w := by
  induction second with
  | refl => exact first
  | extend _ step ih => exact .extend ih step

private theorem detour_to_conditioning {u : Fin n}
    (reachable : G.AncestorOf C u) {v : Fin n} {mark : Bool}
    (upcoming : G.edge u true v mark = true) :
    Reach (G.CStep C) (u, true) (v, mark) := by
  induction reachable generalizing v mark with
  | conditioned present =>
    exact .extend (.refl _) ⟨true, upcoming, by simpa using present⟩
  | @parent u w arrow _ ih =>
    cases present : C u
    · have down : G.CStep C (u, true) (w, true) :=
        ⟨false, arrow, by simpa using present⟩
      have back : Reach (G.CStep C) (w, true) (u, false) :=
        ih ((G.symmetric _ _ _ _).symm.trans arrow)
      have finish : G.CStep C (u, false) (v, mark) :=
        ⟨true, upcoming, by simpa using present⟩
      exact .extend (splice (.extend (.refl _) down) back) finish
    · exact .extend (.refl _) ⟨true, upcoming, by simpa using present⟩

private theorem active_step_has_c_walk {s t : Arrival n} (step : G.Step C s t) :
    Reach (G.CStep C) s t := by
  obtain ⟨outgoing, edge, turn⟩ := step
  unfold openTurn at turn
  cases collider : s.2 && outgoing
  · have outside : C s.1 = false := by simpa [collider] using turn
    exact .extend (.refl _) ⟨outgoing, edge, outside.trans collider.symm⟩
  · have heads := Bool.and_eq_true_iff.mp collider
    obtain ⟨u, incoming⟩ := s
    obtain ⟨v, target⟩ := t
    dsimp only at heads ⊢
    obtain ⟨rfl, rfl⟩ := heads
    exact detour_to_conditioning (by simpa using turn) edge

/-- Conditioning activates a collider ancestor in the m-walk
presentation exactly when a connecting walk exists in the section
presentation. In legal separation queries the two endpoint sets avoid
the conditioning set, so the end vertices satisfy the section condition. -/
theorem c_connected_iff_m_connected {X Y : Fin n → Bool}
    (leftOutside : ∀ u, X u = true → C u = false)
    (rightOutside : ∀ u, Y u = true → C u = false) :
    G.CConnected X Y C ↔ G.WalkConnected X Y C := by
  constructor
  · rintro ⟨first, last, ⟨x, mark, start, edge⟩, path, hit, outside⟩
    refine ⟨first, last, ⟨x, mark, (Bool.and_eq_true_iff.mp start).1, edge⟩, ?_, hit⟩
    clear hit outside
    induction path with
    | refl => exact .refl _
    | extend _ next ih => exact .extend ih (c_step_is_active next)
  · rintro ⟨first, last, ⟨x, mark, start, edge⟩, path, hit⟩
    refine ⟨first, last, ⟨x, mark, by simp [start, leftOutside _ start], edge⟩, ?_,
      hit, rightOutside _ hit⟩
    clear hit
    induction path with
    | refl => exact .refl _
    | extend _ next ih => exact splice ih (active_step_has_c_walk next)

end
end OpenCausalScience.MixedGraph
