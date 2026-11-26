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

end

end OpenCausalScience.Papers.Runge2021.OSetForbidden
