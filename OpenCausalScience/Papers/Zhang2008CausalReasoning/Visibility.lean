module
public import OpenCausalScience.Graph.MixedGraph

/-! # Visibility and inducing walks

Jiji Zhang, *Causal Reasoning with Ancestral Graphs*, JMLR 9 (2008),
Definition 8, Lemma 9, and Appendix B. The result isolates the
concatenation argument from the construction of an induced MAG.

Source: https://www.jmlr.org/papers/v9/zhang08a.html
-/

namespace OpenCausalScience.Papers.Zhang2008CausalReasoning.Visibility

open MixedGraph

@[expose] public section

variable {n : Nat}

/-- Reflexive ancestry by directed edges of the underlying graph. -/
def Ancestor (G : MixedGraph n) : Fin n → Fin n → Prop :=
  Reach (fun u v => G.edge u false v true = true)

/-- An inducing walk may visit unobserved noncolliders. Every interior
collider must be an ancestor of at least one endpoint. -/
def InducingStep (G : MixedGraph n) (latent : Fin n → Bool)
    (source target : Fin n) (before after : Arrival n) : Prop :=
  ∃ outgoing, G.edge before.1 outgoing after.1 after.2 = true ∧
    (if before.2 && outgoing then
      Ancestor G before.1 source ∨ Ancestor G before.1 target
    else latent before.1 = true)

/-- A nonempty inducing walk with specified endpoint marks. -/
def InducingWalk (G : MixedGraph n) (latent : Fin n → Bool)
    (source target : Fin n) (firstMark lastMark : Bool) : Prop :=
  ∃ first : Arrival n, G.edge source firstMark first.1 first.2 = true ∧
    Reach (InducingStep G latent source target) first (target, lastMark)

/-- The no-selection projection facts used in the proof of Lemma 9.
Projection is over the vertices where `latent` is false. Only preservation
of arrowheads is required for the inducing witnesses of projected edges. -/
structure ProjectionFacts (G M : MixedGraph n) (latent : Fin n → Bool) : Prop where
  observed : ∀ {u v a b}, M.edge u a v b = true → latent u = false ∧ latent v = false
  directed_ancestry : ∀ {u v}, M.edge u false v true = true → Ancestor G u v
  inducing_witness : ∀ {u v a b}, M.edge u a v b = true →
    ∃ a' b', (a = true → a' = true) ∧ (b = true → b' = true) ∧
      InducingWalk G latent u v a' b'
  adjacency_of_inducing_walk : ∀ {u v a b}, latent u = false → latent v = false →
    u ≠ v → InducingWalk G latent u v a b → ∃ a' b', M.edge u a' v b' = true

/-- Visibility witnesses consist of an edge into the source, or a collider
chain into it with all intermediate vertices parents of the target. The
reflexive case of the chain includes a one-edge witness. -/
def Visible (M : MixedGraph n) (source target : Fin n) : Prop :=
  M.edge source false target true = true ∧
  ∃ witness first mark, witness ≠ target ∧
    (∀ a b, M.edge witness a target b = false) ∧
    M.edge witness mark first true = true ∧
    (first = source ∨ M.edge first false target true = true) ∧
    Reach (fun u v => M.edge u true v true = true ∧ M.edge v false target true = true)
      first source

private theorem reach_trans {α : Type} {R : α → α → Prop} {u v w : α}
    (left : Reach R u v) (right : Reach R v w) : Reach R u w := by
  induction right with
  | refl => exact left
  | extend _ step ih => exact .extend ih step

private theorem ancestor_trans {G : MixedGraph n} {u v w : Fin n}
    (left : Ancestor G u v) (right : Ancestor G v w) : Ancestor G u w :=
  reach_trans left right

private theorem reach_map {α : Type} {R S : α → α → Prop}
    (map : ∀ {u v}, R u v → S u v) {u v} (walk : Reach R u v) : Reach S u v := by
  induction walk with
  | refl => exact .refl _
  | extend _ step ih => exact .extend ih (map step)

private theorem widen_ancestry {G : MixedGraph n} {latent : Fin n → Bool}
    {u v source target : Fin n}
    (sourceAnc : Ancestor G u source ∨ Ancestor G u target)
    (targetAnc : Ancestor G v source ∨ Ancestor G v target)
    {before after : Arrival n}
    (step : InducingStep G latent u v before after) :
    InducingStep G latent source target before after := by
  obtain ⟨outgoing, edge, allowed⟩ := step
  refine ⟨outgoing, edge, ?_⟩
  cases isCollider : before.2 && outgoing with
  | false => simpa [isCollider] using allowed
  | true =>
    simp [isCollider] at allowed ⊢
    rcases allowed with toSource | toTarget
    · exact sourceAnc.elim
        (fun anc => .inl (ancestor_trans toSource anc))
        (fun anc => .inr (ancestor_trans toSource anc))
    · exact targetAnc.elim
        (fun anc => .inl (ancestor_trans toTarget anc))
        (fun anc => .inr (ancestor_trans toTarget anc))

/-- A prefix of the concatenated inducing walk, with all of its interior
ancestry tests already referring to the final pair of endpoints. -/
private def IntoPrefix (G : MixedGraph n) (latent : Fin n → Bool)
    (source target endpoint : Fin n) : Prop :=
  ∃ (first : Arrival n) (mark : Bool), G.edge source mark first.1 first.2 = true ∧
    Reach (InducingStep G latent source target) first (endpoint, true)

private theorem into_prefix {G : MixedGraph n} {latent : Fin n → Bool}
    {source target endpoint : Fin n} {mark : Bool}
    (walk : InducingWalk G latent source endpoint mark true)
    (anc : Ancestor G endpoint target) : IntoPrefix G latent source target endpoint := by
  obtain ⟨first, edge, reached⟩ := walk
  exact ⟨first, mark, edge, reach_map
    (widen_ancestry (.inl (.refl source)) (.inr anc)) reached⟩

private theorem append_into_prefix {G : MixedGraph n} {latent : Fin n → Bool}
    {source target u v : Fin n} {finishMark : Bool}
    (initialWalk : IntoPrefix G latent source target u)
    (walk : InducingWalk G latent u v true finishMark)
    (uAncestor : Ancestor G u target) (vAncestor : Ancestor G v target) :
    ∃ (first : Arrival n) (mark : Bool), G.edge source mark first.1 first.2 = true ∧
      Reach (InducingStep G latent source target) first (v, finishMark) := by
  obtain ⟨first, mark, edge, before⟩ := initialWalk
  obtain ⟨next, edgeNext, after⟩ := walk
  have join : InducingStep G latent source target (u, true) next :=
    ⟨true, edgeNext, Or.inr uAncestor⟩
  refine ⟨first, mark, edge, reach_trans (.extend before join) ?_⟩
  exact reach_map (widen_ancestry (.inr uAncestor) (.inr vAncestor)) after

/-- A visible arrow excludes an inducing walk into its source in the
underlying graph. This is the visibility conclusion of Zhang's Lemma 9
under the explicit projection facts. -/
theorem visible_edge_excludes_inducing_walk_into_source
    {G M : MixedGraph n} {latent : Fin n → Bool} {source target : Fin n} {lastMark : Bool}
    (projection : ProjectionFacts G M latent) (visible : Visible M source target)
    (walk : InducingWalk G latent source target true lastMark) : False := by
  obtain ⟨arrow, witness, first, _, different, notAdjacent, edge, parent, chain⟩ := visible
  have sourceAncestor : Ancestor G source target := projection.directed_ancestry arrow
  have firstAncestor : Ancestor G first target := parent.elim
    (fun same => by simpa [same] using sourceAncestor) projection.directed_ancestry
  obtain ⟨_, b, _, preserve, initial⟩ := projection.inducing_witness edge
  have hb : b = true := preserve rfl
  subst b
  have base := into_prefix initial firstAncestor
  have extended : ∀ {endpt},
      Reach (fun u v => M.edge u true v true = true ∧ M.edge v false target true = true)
          first endpt → IntoPrefix G latent witness target endpt ∧ Ancestor G endpt target := by
    intro endpt reached
    induction reached with
    | refl => exact ⟨base, firstAncestor⟩
    | extend _ step ih =>
      obtain ⟨a, b, ha, hb, inducing⟩ := projection.inducing_witness step.1
      have ha' : a = true := ha rfl
      have hb' : b = true := hb rfl
      subst a
      subst b
      have nextAncestor := projection.directed_ancestry step.2
      exact ⟨append_into_prefix ih.1 inducing ih.2 nextAncestor, nextAncestor⟩
  obtain ⟨initial', mark', edge', reached'⟩ :=
    append_into_prefix (extended chain).1 walk sourceAncestor (.refl target)
  obtain ⟨a, b, adjacency⟩ := projection.adjacency_of_inducing_walk
    (projection.observed edge).1 (projection.observed arrow).2 different
    (show InducingWalk G latent witness target mark' lastMark from ⟨initial', edge', reached'⟩)
  simp [notAdjacent a b] at adjacency

/-- In particular, a no-selection directed–bidirected diagram cannot
contain a bidirected edge over a visible directed edge of its induced MAG. -/
theorem visible_edge_excludes_bidirected_edge
    {G M : MixedGraph n} {latent : Fin n → Bool} {source target : Fin n}
    (projection : ProjectionFacts G M latent) (visible : Visible M source target) :
    G.edge source true target true = false := by
  cases edge : G.edge source true target true with
  | false => rfl
  | true =>
    exact (visible_edge_excludes_inducing_walk_into_source projection visible
      (show InducingWalk G latent source target true true from
        ⟨(target, true), edge, .refl _⟩)).elim

end
end OpenCausalScience.Papers.Zhang2008CausalReasoning.Visibility
