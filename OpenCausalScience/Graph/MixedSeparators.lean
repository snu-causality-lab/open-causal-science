module
public import OpenCausalScience.Graph.ColliderAugmentation
public import OpenCausalScience.Graph.MixedAnterior
public import OpenCausalScience.Graph.MixedPath
public import OpenCausalScience.Graph.SeparatorBoundary
public import OpenCausalScience.Graph.AugmentedConnection

/-! # Constrained m-separators in mixed graphs

The search starts with the allowed vertices anterior to the endpoints and
the required vertices. It constructs the undirected collider augmentation
and prunes its separator by searching from the two endpoint sets.

Sources: Richardson and Spirtes (2002), §3.4, and van der Zander and
Liśkiewicz (2020), §5.
-/

namespace OpenCausalScience.MixedGraph

@[expose] public section

variable {n : Nat} {G : MixedGraph n}

/-- The anterior set used by augmentation for a particular query. -/
def queryAnterior (G : MixedGraph n) (left right conditioning : Fin n → Bool) :
    Fin n → Bool :=
  G.anterior (fun v => (left v || right v) || conditioning v)

private theorem relevant_left {X Y Z : Fin n → Bool} {v : Fin n} (hx : X v = true) :
    G.queryAnterior X Y Z v = true :=
  (G.anterior_iff _ v).mpr (.seed (by simp [hx]))

private theorem relevant_right {X Y Z : Fin n → Bool} {v : Fin n} (hy : Y v = true) :
    G.queryAnterior X Y Z v = true :=
  (G.anterior_iff _ v).mpr (.seed (by simp [hy]))

theorem relevant_condition {X Y Z : Fin n → Bool} {v : Fin n} (hz : Z v = true) :
    G.queryAnterior X Y Z v = true :=
  (G.anterior_iff _ v).mpr (.seed (by simp [hz]))

private theorem relevant_tail {X Y Z : Fin n → Bool} {u v : Fin n} {mark : Bool}
    (edge : G.edge u false v mark = true) (child : G.queryAnterior X Y Z v = true) :
    G.queryAnterior X Y Z u = true :=
  (G.anterior_iff _ u).mpr (.step edge ((G.anterior_iff _ v).mp child))

private theorem relevant_ancestor {X Y Z : Fin n → Bool} {v : Fin n}
    (ancestor : G.AncestorOf Z v) : G.queryAnterior X Y Z v = true :=
  (G.anterior_iff _ v).mpr (ancestor.to_anterior.mono (fun _ hz => by simp [hz]))

private theorem head_arrival_relevant {X Y Z : Fin n → Bool}
    {s t : Arrival n} {visits : List (Fin n)} (walk : G.ActiveWalk Z s visits t)
    (head : s.2 = true) (incident : ∃ w mark, G.edge s.1 true w mark = true)
    (target : G.queryAnterior X Y Z t.1 = true) : G.queryAnterior X Y Z s.1 = true := by
  induction walk with
  | nil => exact target
  | @cons s next _ _ move _ ih =>
    obtain ⟨outgoing, edge, turn⟩ := move
    cases outgoing with
    | true =>
      exact relevant_ancestor (by simpa [openTurn, head] using turn)
    | false =>
      cases nextHead : next.2 with
      | false =>
        have undirected : G.edge s.1 false next.1 false = true := by
          simpa [nextHead] using edge
        obtain ⟨w, mark, arrow⟩ := incident
        rw [G.no_arrow_of_undirected undirected] at arrow
        contradiction
      | true =>
        have incoming := (G.symmetric _ _ _ _).symm.trans edge
        exact relevant_tail edge (ih nextHead ⟨s.1, false, by simpa [nextHead] using incoming⟩ target)

private theorem next_relevant {X Y Z : Fin n → Bool} {s next last : Arrival n}
    {visits : List (Fin n)} {outgoing : Bool}
    (edge : G.edge s.1 outgoing next.1 next.2 = true) (suffix : G.ActiveWalk Z next visits last)
    (source : G.queryAnterior X Y Z s.1 = true) (target : G.queryAnterior X Y Z last.1 = true) :
    G.queryAnterior X Y Z next.1 = true := by
  have reverse := (G.symmetric _ _ _ _).symm.trans edge
  cases nextMark : next.2 with
  | false => exact relevant_tail (by simpa [nextMark] using reverse) source
  | true =>
    exact head_arrival_relevant suffix nextMark
      ⟨s.1, outgoing, by simpa [nextMark] using reverse⟩ target

open SeparatorBoundary (Separated)

/-- Reachability in the augmentation with the conditioned vertices as blockers. -/
abbrev AugmentedReach (G : MixedGraph n) (A X Z : Fin n → Bool) (v : Fin n) :=
  SeparatorBoundary.Reach (fun u w => G.colliderAugmented A u w = true)
    (fun u => X u = true) (fun u => Z u = true) v

private def BoundaryPrefix (G : MixedGraph n) (A X Z : Fin n → Bool) (s : Arrival n) : Prop :=
  ∃ u, Z u = false ∧ G.AugmentedReach A X Z u ∧
    (u = s.1 ∨ ∃ mark, G.ColliderWalk A (u, mark) s)

private theorem boundary_prefix_finish {A X Z : Fin n → Bool} {s : Arrival n}
    (trail : BoundaryPrefix G A X Z s) : G.AugmentedReach A X Z s.1 := by
  obtain ⟨u, outside, reached, same | ⟨mark, segment⟩⟩ := trail
  · exact same ▸ reached
  · by_cases same : u = s.1
    · exact same ▸ reached
    · exact .step reached (by simp [outside])
        ((G.collider_augmented_iff _ _ _).mpr ⟨same, mark, s.2, segment⟩)

/-- Compress a run of conditioned colliders into one augmented edge. -/
private theorem active_walk_to_boundary {X Y Z : Fin n → Bool} {s last : Arrival n}
    {visits : List (Fin n)} (walk : G.ActiveWalk Z s visits last)
    (source : G.queryAnterior X Y Z s.1 = true) (target : G.queryAnterior X Y Z last.1 = true)
    (trail : BoundaryPrefix G (G.queryAnterior X Y Z) X Z s) :
    G.AugmentedReach (G.queryAnterior X Y Z) X Z last.1 := by
  induction walk with
  | nil => exact boundary_prefix_finish trail
  | @cons s next _ _ move suffix ih =>
    obtain ⟨mark, edge, turn⟩ := move
    have nextRelevant := next_relevant edge suffix source target
    have oneEdge : G.ColliderWalk (G.queryAnterior X Y Z) (s.1, mark) next :=
      .single source nextRelevant edge
    apply ih nextRelevant target
    cases conditioned : Z s.1 with
    | false => exact ⟨s.1, conditioned, boundary_prefix_finish trail, .inr ⟨mark, oneEdge⟩⟩
    | true =>
      have heads : s.2 = true ∧ mark = true := by
        cases h : s.2 <;> cases m : mark <;> simp_all [openTurn]
      obtain ⟨u, openU, reached, same | ⟨startMark, segment⟩⟩ := trail
      · simp [same, conditioned] at openU
      · have shape : (s.1, true) = s := by cases s; simp_all
        have before : G.ColliderWalk (G.queryAnterior X Y Z) (u, startMark) (s.1, true) :=
          shape.symm ▸ segment
        have after : G.ColliderWalk (G.queryAnterior X Y Z) (s.1, true) next :=
          heads.2 ▸ oneEdge
        exact ⟨u, openU, reached, .inr ⟨startMark, .join before after⟩⟩

theorem augmented_reachable_of_walkConnected {X Y Z : Fin n → Bool}
    (leftOutside : ∀ v, X v = true → Z v = false)
    (path : G.WalkConnected X Y Z) :
    ∃ v, Y v = true ∧ G.AugmentedReach (G.queryAnterior X Y Z) X Z v := by
  obtain ⟨first, last, ⟨x, mark, hx, edge⟩, reached, hy⟩ := path
  obtain ⟨visits, walk⟩ := reachable_iff_active_walk.mp reached
  have source : G.queryAnterior X Y Z x = true := relevant_left hx
  have target : G.queryAnterior X Y Z last.1 = true := relevant_right hy
  have firstRelevant := next_relevant (s := (x, false)) edge walk source target
  exact ⟨last.1, hy, active_walk_to_boundary walk firstRelevant target
    ⟨x, leftOutside _ hx, .seed hx, .inr ⟨mark, .single source firstRelevant edge⟩⟩⟩

private theorem augmented_walk_append_edge {A Z : Fin n → Bool} {u v w : Fin n}
    (path : G.AugmentedWalk A Z u v) (edge : G.colliderAugmented A v w = true)
    (before : Z v = false) (after : Z w = false) : G.AugmentedWalk A Z u w := by
  induction path with
  | nil => exact .cons edge before after (.nil _)
  | cons e leftOutside rightOutside _ ih => exact .cons e leftOutside rightOutside (ih edge before)

private theorem augmented_walk_of_reach {A X Z : Fin n → Bool} {v : Fin n}
    (reach : G.AugmentedReach A X Z v) (outside : Z v = false) :
    ∃ u, X u = true ∧ G.AugmentedWalk A Z u v := by
  induction reach with
  | seed hx => exact ⟨_, hx, .nil _⟩
  | step _ openU edge ih =>
    have before := Bool.eq_false_iff.mpr openU
    obtain ⟨u, hx, path⟩ := ih before
    exact ⟨u, hx, augmented_walk_append_edge path edge before outside⟩

/-- Mixed-graph separation is undirected separation after anterior
restriction and collider augmentation. Endpoint sets must be disjoint
from each other and the conditioning set. -/
theorem no_walkConnected_iff_augmented_separated
    (G : MixedGraph n) (X Y Z : Fin n → Bool)
    (leftOutside : ∀ v, X v = true → Z v = false)
    (rightOutside : ∀ v, Y v = true → Z v = false)
    (disjoint : ∀ v, X v = true → Y v = false) :
    ¬ G.WalkConnected X Y Z ↔
      Separated (fun u v => G.colliderAugmented (G.queryAnterior X Y Z) u v = true)
        (fun v => X v = true) (fun v => Y v = true) (fun v => Z v = true) := by
  constructor
  · intro separated v hy route
    obtain ⟨u, hx, walk⟩ := augmented_walk_of_reach route (rightOutside v hy)
    exact separated (G.walkConnected_of_augmentedWalk X Y Z walk hx hy disjoint)
  · intro separated path
    obtain ⟨v, hy, reach⟩ := augmented_reachable_of_walkConnected leftOutside path
    exact separated v hy reach

private theorem query_anterior_mono {X Y I Z : Fin n → Bool}
    (sub : ∀ v, I v = true → Z v = true) {v : Fin n}
    (present : G.queryAnterior X Y I v = true) : G.queryAnterior X Y Z v = true :=
  (G.anterior_iff _ v).mpr (((G.anterior_iff _ v).mp present).mono (by
    intro u mem
    exact (Bool.or_eq_true_iff.mp mem).elim (fun h => by simp [h])
      (fun h => by simp [sub u h])))

theorem query_anterior_eq {X Y I Z : Fin n → Bool}
    (required : ∀ v, I v = true → Z v = true)
    (relevant : ∀ v, Z v = true → G.queryAnterior X Y I v = true) :
    G.queryAnterior X Y I = G.queryAnterior X Y Z := by
  funext v
  apply Bool.eq_iff_iff.mpr
  refine ⟨query_anterior_mono required, ?_⟩
  intro here
  apply (G.anterior_iff _ v).mpr
  apply ((G.anterior_iff _ v).mp here).trans
  intro w mem
  rcases Bool.or_eq_true_iff.mp mem with endpoint | hz
  · exact .seed (by simp [endpoint])
  · exact (G.anterior_iff _ w).mp (relevant w hz)

private theorem collider_walk_mono {A B : Fin n → Bool} {u v : Arrival n}
    (sub : ∀ w, A w = true → B w = true) (path : G.ColliderWalk A u v) :
    G.ColliderWalk B u v := by
  induction path with
  | single hu hv edge => exact .single (sub _ hu) (sub _ hv) edge
  | join _ _ first second => exact .join first second

theorem lift_clamped_reach {X Y I Z : Fin n → Bool}
    (required : ∀ v, I v = true → Z v = true) {v : Fin n}
    (reached : SeparatorBoundary.Reach
      (fun u w => G.colliderAugmented (G.queryAnterior X Y I) u w = true)
      (fun u => X u = true) (fun u => Z u = true ∧ G.queryAnterior X Y I u = true) v) :
    G.AugmentedReach (G.queryAnterior X Y Z) X Z v := by
  induction reached with
  | seed hx => exact .seed hx
  | @step u w _ openU edge ih =>
    obtain ⟨distinct, outgoing, incoming, path⟩ := (G.collider_augmented_iff _ u w).mp edge
    exact .step ih (fun hz => openU ⟨hz, path.source_relevant⟩)
      ((G.collider_augmented_iff _ u w).mpr
        ⟨distinct, outgoing, incoming, collider_walk_mono (fun _ => query_anterior_mono required) path⟩)

/-- A candidate is permitted when it includes every mandatory vertex,
uses only allowed vertices, and m-separates the endpoint sets. -/
def IsMSeparator (G : MixedGraph n) (X Y I R Z : Fin n → Bool) : Prop :=
  (∀ v, I v = true → Z v = true) ∧ (∀ v, Z v = true → R v = true) ∧
    ¬ G.WalkConnected X Y Z

/-- Minimality is relative to the required set. -/
def IsMinimalMSeparator (G : MixedGraph n) (X Y I R Z : Fin n → Bool) : Prop :=
  G.IsMSeparator X Y I R Z ∧
    ∀ W, G.IsMSeparator X Y I R W → (∀ v, W v = true → Z v = true) →
      ∀ v, Z v = true → W v = true

/-- The allowed relevant vertices form the initial blocker set for the two
boundary passes. -/
def findMinimalMSeparator (G : MixedGraph n) (X Y I R : Fin n → Bool) :
    Option (Fin n → Bool) :=
  let A := G.queryAnterior X Y I
  SeparatorBoundary.findMinimalSeparator (G.colliderAugmented A) X Y I (fun v => R v && A v)

/-- For legal endpoint and covariate sets, the executable mixed-graph
search returns an inclusion-minimal permitted separator, or proves that
there is no permitted m-separator. -/
theorem find_minimal_m_separator_correct (G : MixedGraph n) (X Y I R : Fin n → Bool)
    (disjoint : ∀ v, X v = true → Y v = false)
    (requiredAllowed : ∀ v, I v = true → R v = true)
    (allowedLeft : ∀ v, R v = true → X v = false)
    (allowedRight : ∀ v, R v = true → Y v = false) :
    match G.findMinimalMSeparator X Y I R with
    | none => ¬ ∃ Z, G.IsMSeparator X Y I R Z
    | some Z => G.IsMinimalMSeparator X Y I R Z := by
  let A := G.queryAnterior X Y I
  let adj := G.colliderAugmented A
  let initial : Fin n → Bool := fun v => R v && A v
  have initialRequired (v) (h : I v = true) : initial v = true :=
    Bool.and_eq_true_iff.mpr ⟨requiredAllowed v h, relevant_condition h⟩
  have allowed (v) (h : initial v = true) : R v = true :=
    (Bool.and_eq_true_iff.mp h).1
  have relevant (v) (h : initial v = true) : A v = true :=
    (Bool.and_eq_true_iff.mp h).2
  have graphOutput := SeparatorBoundary.find_minimal_separator_correct adj X Y I initial
    (fun u v h => (G.collider_augmented_symmetric A u v).symm.trans h)
    initialRequired
    (fun v h => Bool.eq_false_iff.mp (allowedLeft v (allowed v h)))
    (fun v h => Bool.eq_false_iff.mp (allowedRight v (allowed v h)))
  have separation (Z : Fin n → Bool) (onlyAllowed : ∀ v, Z v = true → R v = true) :=
    G.no_walkConnected_iff_augmented_separated X Y Z
      (fun v hx => Bool.eq_false_iff.mpr (fun hz =>
        Bool.eq_false_iff.mp (allowedLeft v (onlyAllowed v hz)) hx))
      (fun v hy => Bool.eq_false_iff.mpr (fun hz =>
        Bool.eq_false_iff.mp (allowedRight v (onlyAllowed v hz)) hy)) disjoint
  unfold findMinimalMSeparator
  change match SeparatorBoundary.findMinimalSeparator adj X Y I initial with
    | none => ¬ ∃ Z, G.IsMSeparator X Y I R Z
    | some Z => G.IsMinimalMSeparator X Y I R Z
  generalize SeparatorBoundary.findMinimalSeparator adj X Y I initial = result at graphOutput ⊢
  cases result with
  | none =>
    rintro ⟨Z, includes, inR, separated⟩
    apply graphOutput
    refine ⟨fun v => Z v = true ∧ A v = true, fun v hi => ⟨includes v hi, relevant_condition hi⟩,
      fun v h => Bool.and_eq_true_iff.mpr ⟨inR v h.1, h.2⟩, ?_⟩
    exact fun v hy reach => ((separation Z inR).mp separated) v hy (lift_clamped_reach includes reach)
  | some Z =>
    obtain ⟨⟨includes, inInitial, separated⟩, minimal⟩ := graphOutput
    have inR : ∀ v, Z v = true → R v = true := fun v h => allowed v (inInitial v h)
    have inA : ∀ v, Z v = true → A v = true := fun v h => relevant v (inInitial v h)
    have same : A = G.queryAnterior X Y Z := query_anterior_eq includes inA
    refine ⟨⟨includes, inR, (separation Z inR).mpr ?_⟩, ?_⟩
    · simpa only [← same] using separated
    · rintro W ⟨contains, allowedW, sepW⟩ subset
      have sameW : A = G.queryAnterior X Y W :=
        query_anterior_eq contains (fun v h => inA v (subset v h))
      apply minimal (fun v => W v = true) _ subset
      refine ⟨contains, fun v h => inInitial v (subset v h), ?_⟩
      simpa only [← sameW] using (separation W allowedW).mp sepW

end
end OpenCausalScience.MixedGraph
