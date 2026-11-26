module
public import OpenCausalScience.Graph.MixedPath
public import OpenCausalScience.Graph.MixedSeparators

/-! # Separation under explicit latent-root expansion

Replace each bidirected observed edge by an unconditioned root with the
two endpoints as children. Directed observed edges retain their marks.
The expansion preserves separation between observed sets even when a
directed edge and a bidirected edge have the same endpoints.
-/

namespace OpenCausalScience.MixedGraph

@[expose] public section

variable {n k : Nat}

abbrev RootChildren (n k : Nat) := Fin k → Fin n × Fin n

def childOf (children : RootChildren n k) (root : Fin k) (v : Fin n) : Bool :=
  v == (children root).1 || v == (children root).2

def expandedEdge (G : MixedGraph n) (children : RootChildren n k)
    (u : Fin (n + k)) (a : Bool) (v : Fin (n + k)) (b : Bool) : Bool :=
  Fin.addCases
    (fun x => Fin.addCases (fun y => G.edge x a y b && (a != b))
      (fun root => a && !b && childOf children root x) v)
    (fun root => Fin.addCases (fun y => !a && b && childOf children root y)
      (fun _ => false) v) u

/-- The observed vertices come first, followed by one root per listed
endpoint pair. The list determines the representation, so the theorem
requires precisely the head/head edges declared by the original graph. -/
def explicitLatentExpansion (G : MixedGraph n) (children : RootChildren n k) : MixedGraph (n + k) where
  edge := expandedEdge G children
  symmetric := by
    intro u a v b
    refine Fin.addCases (fun x => ?_) (fun i => ?_) u
    · refine Fin.addCases (fun y => ?_) (fun j => ?_) v
      · have marks : (a != b) = (b != a) := bne_comm
        simp [expandedEdge, G.symmetric x a y b, marks]
      · simp [expandedEdge, Bool.and_comm a (!b)]
    · refine Fin.addCases (fun y => ?_) (fun j => ?_) v
      · simp [expandedEdge, Bool.and_comm (!a) b]
      · simp [expandedEdge]
  loop_free := by
    intro u a b
    refine Fin.addCases (fun x => ?_) (fun _ => ?_) u <;> simp [expandedEdge, G.loop_free]
  no_arrow_of_undirected := by
    intro u v _ _ edge
    revert edge
    refine Fin.addCases (fun x => ?_) (fun i => ?_) u <;>
      refine Fin.addCases (fun y => ?_) (fun j => ?_) v <;> simp [expandedEdge]

private abbrev obs (k : Nat) (v : Fin n) : Fin (n + k) := Fin.castAdd k v
private abbrev latent (n : Nat) (i : Fin k) : Fin (n + k) := Fin.natAdd n i

/-- Retain an observed set and exclude all newly added roots. -/
def liftObservedSet (k : Nat) (S : Fin n → Bool) : Fin (n + k) → Bool :=
  Fin.addCases S (fun _ => false)

variable {G : MixedGraph n} {children : RootChildren n k}

@[simp] private theorem expanded_oo (u v : Fin n) (a b : Bool) :
    (G.explicitLatentExpansion children).edge (obs k u) a (obs k v) b =
      (G.edge u a v b && (a != b)) := by
  simp [explicitLatentExpansion, expandedEdge]

@[simp] private theorem expanded_ol (u : Fin n) (i : Fin k) (a b : Bool) :
    (G.explicitLatentExpansion children).edge (obs k u) a (latent n i) b =
      (a && !b && childOf children i u) := by
  simp [explicitLatentExpansion, expandedEdge]

@[simp] private theorem expanded_lo (i : Fin k) (v : Fin n) (a b : Bool) :
    (G.explicitLatentExpansion children).edge (latent n i) a (obs k v) b =
      (!a && b && childOf children i v) := by
  simp [explicitLatentExpansion, expandedEdge]

@[simp] private theorem expanded_ll (i j : Fin k) (a b : Bool) :
    (G.explicitLatentExpansion children).edge (latent n i) a (latent n j) b = false := by
  simp [explicitLatentExpansion, expandedEdge]

@[simp] private theorem lifted_observed (S : Fin n → Bool) (v : Fin n) :
    liftObservedSet k S (obs k v) = S v := by simp [liftObservedSet]

@[simp] private theorem lifted_latent (S : Fin n → Bool) (i : Fin k) :
    liftObservedSet k S (latent n i) = false := by simp [liftObservedSet]

private theorem observed_injective {u v : Fin n} (same : obs k u = obs k v) : u = v :=
  Fin.ext (congrArg (fun t : Fin (n + k) => t.val) same)

private theorem observed_ne_latent (u : Fin n) (i : Fin k) : obs k u ≠ latent n i := by
  intro same
  have vals := congrArg Fin.val same
  change u.val = n + i.val at vals
  omega

private theorem vertex_cases (v : Fin (n + k)) :
    (∃ u, v = obs k u) ∨ ∃ i, v = latent n i :=
  Fin.addCases (fun u => .inl ⟨u, rfl⟩) (fun i => .inr ⟨i, rfl⟩) v

private theorem reach_append {α : Type} {R : α → α → Prop} {u v w : α}
    (front : Reach R u v) (back : Reach R v w) : Reach R u w := by
  induction back with
  | refl => exact front
  | extend _ step ih => exact .extend ih step

variable {conditioning : Fin n → Bool}

private theorem lift_ancestor {v : Fin n} (path : G.AncestorOf conditioning v) :
    (G.explicitLatentExpansion children).AncestorOf (liftObservedSet k conditioning) (obs k v) := by
  induction path with
  | conditioned present => exact .conditioned (by simpa using present)
  | parent edge _ ih => exact .parent (by simpa using edge) ih

private theorem directed_observed_child {u : Fin n} {v : Fin (n + k)}
    (edge : (G.explicitLatentExpansion children).edge (obs k u) false v true = true) :
    ∃ w : Fin n, v = obs k w ∧ G.edge u false w true = true := by
  rcases vertex_cases v with ⟨w, rfl⟩ | ⟨i, rfl⟩
  · exact ⟨w, rfl, by simpa using edge⟩
  · simp at edge

private theorem project_ancestor {v : Fin (n + k)}
    (path : (G.explicitLatentExpansion children).AncestorOf (liftObservedSet k conditioning) v)
    {u : Fin n} (same : v = obs k u) : G.AncestorOf conditioning u := by
  induction path generalizing u with
  | conditioned present => exact .conditioned (by simpa [same] using present)
  | parent edge _ ih =>
    rw [same] at edge
    obtain ⟨_, child, baseEdge⟩ := directed_observed_child edge
    exact .parent baseEdge (ih child)

private theorem observed_turn (v : Fin n) (incoming outgoing : Bool) :
    (G.explicitLatentExpansion children).openTurn (liftObservedSet k conditioning)
      (obs k v, incoming) outgoing ↔ G.openTurn conditioning (v, incoming) outgoing := by
  have ancestry :
      (G.explicitLatentExpansion children).AncestorOf (liftObservedSet k conditioning) (obs k v) ↔
      G.AncestorOf conditioning v :=
    ⟨fun path => project_ancestor path rfl, lift_ancestor⟩
  simp [openTurn, ancestry]

/-- Each root represents a bidirected edge, and each bidirected edge has a
root. Ordered root indices need not match any order of the vertices. -/
def RepresentsBidirected (G : MixedGraph n) (children : RootChildren n k) : Prop :=
  ∀ u v, G.edge u true v true = true ↔ ∃ i,
    ((children i).1 = u ∧ (children i).2 = v) ∨
    ((children i).2 = u ∧ (children i).1 = v)

/-- Enumerate each bidirected edge once, in increasing endpoint order. -/
def bidirectedPairs (G : MixedGraph n) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun u =>
    ((List.finRange n).filter fun v => decide (u < v) && G.edge u true v true).map (u, ·)

theorem mem_bidirectedPairs_iff (G : MixedGraph n) (u v : Fin n) :
    (u, v) ∈ G.bidirectedPairs ↔ u < v ∧ G.edge u true v true = true := by
  simp [bidirectedPairs, List.mem_flatMap, List.mem_map, List.mem_filter]

theorem bidirected_pairs_represent (G : MixedGraph n) :
    G.RepresentsBidirected G.bidirectedPairs.get := by
  intro u v
  constructor
  · intro edge
    rcases Nat.lt_trichotomy u.val v.val with forward | same | backward
    · have member := (G.mem_bidirectedPairs_iff u v).mpr ⟨Fin.lt_def.mpr forward, edge⟩
      obtain ⟨i, equal⟩ := List.mem_iff_get.mp member
      exact ⟨i, .inl ⟨congrArg Prod.fst equal, congrArg Prod.snd equal⟩⟩
    · have eq : u = v := Fin.ext same
      subst v
      rw [G.loop_free] at edge
      contradiction
    · have member := (G.mem_bidirectedPairs_iff v u).mpr
        ⟨Fin.lt_def.mpr backward, (G.symmetric _ _ _ _).symm.trans edge⟩
      obtain ⟨i, equal⟩ := List.mem_iff_get.mp member
      exact ⟨i, .inr ⟨congrArg Prod.snd equal, congrArg Prod.fst equal⟩⟩
  · rintro ⟨i, same | reversed⟩
    · have equal : G.bidirectedPairs.get i = (u, v) := Prod.ext same.1 same.2
      have member : (u, v) ∈ G.bidirectedPairs := equal ▸ (G.bidirectedPairs.get_mem i)
      exact ((G.mem_bidirectedPairs_iff u v).mp member).2
    · have equal : G.bidirectedPairs.get i = (v, u) := Prod.ext reversed.2 reversed.1
      have member : (v, u) ∈ G.bidirectedPairs := equal ▸ (G.bidirectedPairs.get_mem i)
      exact (G.symmetric _ _ _ _).trans ((G.mem_bidirectedPairs_iff v u).mp member).2

private theorem children_of_bidirected (rep : G.RepresentsBidirected children) {u v : Fin n}
    (edge : G.edge u true v true = true) :
    ∃ i, childOf children i u = true ∧ childOf children i v = true := by
  obtain ⟨i, order | order⟩ := (rep u v).mp edge
  · exact ⟨i, by simp [childOf, order.1], by simp [childOf, order.2]⟩
  · exact ⟨i, by simp [childOf, order.1], by simp [childOf, order.2]⟩

private theorem bidirected_of_children (rep : G.RepresentsBidirected children) {u v : Fin n}
    {i : Fin k} (hu : childOf children i u = true) (hv : childOf children i v = true)
    (different : u ≠ v) : G.edge u true v true = true := by
  apply (rep u v).mpr
  have hu' : u = (children i).1 ∨ u = (children i).2 := by simpa [childOf] using hu
  have hv' : v = (children i).1 ∨ v = (children i).2 := by simpa [childOf] using hv
  rcases hu' with uFirst | uSecond <;> rcases hv' with vFirst | vSecond
  · exact (different (uFirst.trans vFirst.symm)).elim
  · exact ⟨i, .inl ⟨uFirst.symm, vSecond.symm⟩⟩
  · exact ⟨i, .inr ⟨uSecond.symm, vFirst.symm⟩⟩
  · exact (different (uSecond.trans vSecond.symm)).elim

private def liftState (k : Nat) (state : Arrival n) : Arrival (n + k) :=
  (obs k state.1, state.2)

private theorem lift_step (rep : G.RepresentsBidirected children)
    (directedBidirected : ∀ u v, G.edge u false v false = false)
    {source target : Arrival n} (step : G.Step conditioning source target) :
    Reach ((G.explicitLatentExpansion children).Step (liftObservedSet k conditioning))
      (liftState k source) (liftState k target) := by
  obtain ⟨u, incoming⟩ := source
  obtain ⟨v, arrival⟩ := target
  obtain ⟨outgoing, edge, turn⟩ := step
  have opens := (observed_turn (G := G) (children := children) u incoming outgoing).mpr turn
  cases outgoing <;> cases arrival
  · simp [directedBidirected] at edge
  · exact .extend (.refl _) ⟨false, by simpa [liftState] using edge, opens⟩
  · exact .extend (.refl _) ⟨true, by simpa [liftState] using edge, opens⟩
  · obtain ⟨i, first, second⟩ := children_of_bidirected rep edge
    have into : (G.explicitLatentExpansion children).Step (liftObservedSet k conditioning)
        (liftState k (u, incoming)) (latent n i, false) :=
      ⟨true, by simpa [liftState] using first, opens⟩
    have outOf : (G.explicitLatentExpansion children).Step (liftObservedSet k conditioning)
        (latent n i, false) (liftState k (v, true)) :=
      ⟨false, by simpa [liftState] using second, by simp [openTurn]⟩
    exact .extend (.extend (.refl _) into) outOf

private theorem lift_reach (rep : G.RepresentsBidirected children)
    (directedBidirected : ∀ u v, G.edge u false v false = false)
    {u v : Arrival n} (reached : Reach (G.Step conditioning) u v) :
    Reach ((G.explicitLatentExpansion children).Step (liftObservedSet k conditioning))
      (liftState k u) (liftState k v) := by
  induction reached with
  | refl => exact .refl _
  | extend _ step ih => exact reach_append ih (lift_step rep directedBidirected step)

private theorem project_observed_step {u v : Fin n} {incoming arrival : Bool}
    (step : (G.explicitLatentExpansion children).Step (liftObservedSet k conditioning)
      (obs k u, incoming) (obs k v, arrival)) : G.Step conditioning (u, incoming) (v, arrival) := by
  obtain ⟨outgoing, edge, turn⟩ := step
  have base : G.edge u outgoing v arrival = true ∧ (outgoing != arrival) = true := by
    simpa only [expanded_oo, Bool.and_eq_true] using edge
  exact ⟨outgoing, base.1, (observed_turn u incoming outgoing).mp turn⟩

private theorem project_root_steps (rep : G.RepresentsBidirected children)
    {u v : Fin n} {i : Fin k} {incoming rootMark arrival : Bool} (different : u ≠ v)
    (first : (G.explicitLatentExpansion children).Step (liftObservedSet k conditioning)
      (obs k u, incoming) (latent n i, rootMark))
    (second : (G.explicitLatentExpansion children).Step (liftObservedSet k conditioning)
      (latent n i, rootMark) (obs k v, arrival)) : G.Step conditioning (u, incoming) (v, arrival) := by
  obtain ⟨departure, legIn, turn⟩ := first
  obtain ⟨exitMark, legOut, _⟩ := second
  have hIn : (departure = true ∧ (!rootMark) = true) ∧ childOf children i u = true := by
    simpa only [expanded_ol, Bool.and_eq_true] using legIn
  have hOut : ((!exitMark) = true ∧ arrival = true) ∧ childOf children i v = true := by
    simpa only [expanded_lo, Bool.and_eq_true] using legOut
  rcases hIn with ⟨⟨rfl, _⟩, into⟩
  rcases hOut with ⟨⟨_, rfl⟩, outOf⟩
  exact ⟨true, bidirected_of_children rep into outOf different, (observed_turn u incoming true).mp turn⟩

private theorem root_step_target_observed {i : Fin k} {mark : Bool} {t : Arrival (n + k)}
    (step : (G.explicitLatentExpansion children).Step (liftObservedSet k conditioning)
      (latent n i, mark) t) : ∃ v : Fin n, t.1 = obs k v := by
  rcases vertex_cases t.1 with observed | ⟨_, atRoot⟩
  · exact observed
  · obtain ⟨outgoing, edge, _⟩ := step
    change (G.explicitLatentExpansion children).edge (latent n i) outgoing t.1 t.2 = true at edge
    simp [atRoot] at edge

private theorem project_simple_walk (rep : G.RepresentsBidirected children)
    {s t : Arrival (n + k)} {visits : List (Fin (n + k))}
    (walk : (G.explicitLatentExpansion children).ActiveWalk (liftObservedSet k conditioning) s visits t)
    (simple : (s.1 :: visits).Nodup) {u v : Fin n}
    (source : s.1 = obs k u) (target : t.1 = obs k v) :
    Reach (G.Step conditioning) (u, s.2) (v, t.2) := by
  induction size : visits.length using Nat.strongRecOn generalizing visits s t u v with
  | ind bound ih =>
    cases walk with
    | nil =>
      have same := observed_injective (source.symm.trans target)
      subst v
      exact .refl _
    | @cons _ middle _ remaining move suffix =>
      have openSuffix := (List.nodup_cons.mp simple).2
      have startEq : s = (obs k u, s.2) := Prod.ext source rfl
      rcases vertex_cases middle.1 with ⟨w, middleObserved⟩ | ⟨i, middleRoot⟩
      · have middleEq : middle = (obs k w, middle.2) := Prod.ext middleObserved rfl
        have small : remaining.length < bound := by simp at size; omega
        rw [startEq, middleEq] at move
        have first := project_observed_step move
        exact reach_append (.extend (.refl _) first)
          (ih _ small suffix openSuffix middleObserved target rfl)
      · have middleEq : middle = (latent n i, middle.2) := Prod.ext middleRoot rfl
        cases suffix with
        | nil =>
          exact (observed_ne_latent v i (target.symm.trans middleRoot)).elim
        | @cons middle after last tail nextMove remainder =>
          rw [middleEq] at nextMove
          obtain ⟨w, afterObserved⟩ := root_step_target_observed nextMove
          have afterEq : after = (obs k w, after.2) := Prod.ext afterObserved rfl
          have different : u ≠ w := by
            intro same
            have duplicate : s.1 = after.1 := source.trans (same ▸ afterObserved.symm)
            exact (List.nodup_cons.mp simple).1 (by simp [duplicate])
          rw [startEq, middleEq] at move
          rw [afterEq] at nextMove
          have first := project_root_steps rep different move nextMove
          have small : tail.length < bound := by simp at size; omega
          exact reach_append (.extend (.refl _) first)
            (ih _ small remainder (List.nodup_cons.mp openSuffix).2 afterObserved target rfl)

private theorem connected_of_reach_from_source {N : Nat} {H : MixedGraph N}
    {left right C : Fin N → Bool} {u : Fin N} {target : Arrival N}
    (separate : ∀ w, left w = true → right w = false) (hx : left u = true)
    (hy : right target.1 = true) (path : Reach (H.Step C) (u, false) target) :
    H.WalkConnected left right C := by
  obtain ⟨_, walk⟩ := reachable_iff_active_walk.mp path
  cases walk with
  | nil =>
    rw [separate _ hx] at hy
    contradiction
  | cons first suffix =>
    obtain ⟨outgoing, edge, _⟩ := first
    exact ⟨_, target, ⟨u, outgoing, hx, edge⟩, reachable_iff_active_walk.mpr ⟨_, suffix⟩, hy⟩

/-- The actual root expansion preserves observed set-valued m-connection.
No latent root belongs to the query sets or the conditioning set. -/
theorem walkConnected_explicitLatentExpansion_iff
    (G : MixedGraph n) (children : RootChildren n k) (left right conditioning : Fin n → Bool)
    (rep : G.RepresentsBidirected children)
    (directedBidirected : ∀ u v, G.edge u false v false = false)
    (leftOutside : ∀ u, left u = true → conditioning u = false)
    (disjoint : ∀ u, left u = true → right u = false) :
    (G.explicitLatentExpansion children).WalkConnected (liftObservedSet k left)
      (liftObservedSet k right) (liftObservedSet k conditioning) ↔
    G.WalkConnected left right conditioning := by
  constructor
  · rintro ⟨first, last, ⟨source, outgoing, hx, edge⟩, reached, hy⟩
    rcases vertex_cases source with ⟨u, rfl⟩ | ⟨_, rfl⟩
    · rcases vertex_cases last.1 with ⟨v, lastObserved⟩ | ⟨_, lastLatent⟩
      · have baseLeft : left u = true := by simpa using hx
        have baseRight : right v = true := by simpa [lastObserved] using hy
        have step : (G.explicitLatentExpansion children).Step (liftObservedSet k conditioning)
            (obs k u, false) first :=
          ⟨outgoing, edge, by simpa [openTurn] using leftOutside u baseLeft⟩
        obtain ⟨_, tail⟩ := reachable_iff_active_walk.mp reached
        obtain ⟨_, target, path, same, simple, _⟩ := (ActiveWalk.cons step tail).to_simple
        exact connected_of_reach_from_source disjoint baseLeft baseRight
          (project_simple_walk rep path simple rfl (same.trans lastObserved))
      · simp [lastLatent] at hy
    · simp at hx
  · rintro ⟨first, last, ⟨source, outgoing, hx, edge⟩, reached, hy⟩
    have step : G.Step conditioning (source, false) first :=
      ⟨outgoing, edge, by simpa [openTurn] using leftOutside source hx⟩
    have liftedDisjoint : ∀ u, liftObservedSet k left u = true → liftObservedSet k right u = false := by
      intro u
      rcases vertex_cases u with ⟨v, rfl⟩ | ⟨i, rfl⟩
      · simpa using disjoint v
      · simp
    have path := lift_reach rep directedBidirected (reach_append (.extend (.refl _) step) reached)
    exact connected_of_reach_from_source liftedDisjoint
      (by simpa using hx) (by simpa [liftState] using hy) path

def restrictObservedSet (k : Nat) (S : Fin (n + k) → Bool) : Fin n → Bool :=
  fun v => S (Fin.castAdd k v)

/-- The CGA route for a directed-bidirected graph runs the boundary search
on the explicit latent expansion, with conditioning confined to observed
vertices, and projects the result to the observed labels. -/
def findMinimalMSeparatorViaLatents (G : MixedGraph n) (children : RootChildren n k)
    (X Y I R : Fin n → Bool) : Option (Fin n → Bool) :=
  ((G.explicitLatentExpansion children).findMinimalMSeparator
    (liftObservedSet k X) (liftObservedSet k Y) (liftObservedSet k I) (liftObservedSet k R)).map
    (restrictObservedSet k)

private theorem lift_implies {S T : Fin n → Bool} {flag : Bool}
    (implies : ∀ u, S u = true → T u = flag) :
    ∀ u, liftObservedSet k S u = true → liftObservedSet k T u = flag := by
  intro u
  rcases vertex_cases u with ⟨v, rfl⟩ | ⟨i, rfl⟩
  · simpa using implies v
  · simp

private theorem restrict_lift {S : Fin n → Bool} {Z : Fin (n + k) → Bool}
    (allowed : ∀ u, Z u = true → liftObservedSet k S u = true) :
    liftObservedSet k (restrictObservedSet k Z) = Z := by
  funext u
  rcases vertex_cases u with ⟨v, rfl⟩ | ⟨i, rfl⟩
  · simp [restrictObservedSet]
  · have outside : Z (latent n i) = false := Bool.eq_false_iff.mpr fun present => by
      simpa using allowed (latent n i) present
    simpa using outside.symm

private theorem lifted_separator_iff {X Y I R Z : Fin n → Bool}
    (represented : G.RepresentsBidirected children)
    (directedBidirected : ∀ u v, G.edge u false v false = false)
    (disjoint : ∀ v, X v = true → Y v = false)
    (allowedLeft : ∀ v, R v = true → X v = false) :
    (G.explicitLatentExpansion children).IsMSeparator
      (liftObservedSet k X) (liftObservedSet k Y) (liftObservedSet k I) (liftObservedSet k R)
      (liftObservedSet k Z) ↔ G.IsMSeparator X Y I R Z := by
  have transfer (allowed : ∀ v, Z v = true → R v = true) :=
    walkConnected_explicitLatentExpansion_iff G children X Y Z represented directedBidirected
      (fun v hx => Bool.eq_false_iff.mpr fun hz => Bool.eq_false_iff.mp
        (allowedLeft v (allowed v hz)) hx) disjoint
  constructor
  · rintro ⟨required, allowed, separated⟩
    have allowed' (v) (hz : Z v = true) : R v = true := by
      simpa using allowed (obs k v) (by simpa using hz)
    have required' (v) (hi : I v = true) : Z v = true := by
      simpa using required (obs k v) (by simpa using hi)
    exact ⟨required', allowed', fun h => separated ((transfer allowed').mpr h)⟩
  · rintro ⟨required, allowed, separated⟩
    exact ⟨lift_implies required, lift_implies allowed, fun h => separated ((transfer allowed).mp h)⟩

/-- Success and failure of the latent-DAG boundary search have their
m-separation meaning in the original graph, including in the presence of
parallel directed and bidirected edges. -/
theorem find_minimal_m_separator_via_latents_correct (G : MixedGraph n) (children : RootChildren n k)
    (X Y I R : Fin n → Bool)
    (represented : G.RepresentsBidirected children)
    (directedBidirected : ∀ u v, G.edge u false v false = false)
    (disjoint : ∀ v, X v = true → Y v = false)
    (requiredAllowed : ∀ v, I v = true → R v = true)
    (allowedLeft : ∀ v, R v = true → X v = false)
    (allowedRight : ∀ v, R v = true → Y v = false) :
    match G.findMinimalMSeparatorViaLatents children X Y I R with
    | none => ¬ ∃ Z, G.IsMSeparator X Y I R Z
    | some Z => G.IsMinimalMSeparator X Y I R Z := by
  let extended := G.explicitLatentExpansion children
  have result := extended.find_minimal_m_separator_correct
    (liftObservedSet k X) (liftObservedSet k Y) (liftObservedSet k I) (liftObservedSet k R)
    (lift_implies disjoint) (lift_implies requiredAllowed)
    (lift_implies allowedLeft) (lift_implies allowedRight)
  have equivalent {Z : Fin n → Bool} :
      extended.IsMSeparator (liftObservedSet k X) (liftObservedSet k Y)
        (liftObservedSet k I) (liftObservedSet k R) (liftObservedSet k Z) ↔
        G.IsMSeparator X Y I R Z :=
    lifted_separator_iff represented directedBidirected disjoint allowedLeft
  unfold findMinimalMSeparatorViaLatents
  generalize extended.findMinimalMSeparator
    (liftObservedSet k X) (liftObservedSet k Y) (liftObservedSet k I) (liftObservedSet k R) =
      found at result ⊢
  cases found with
  | none =>
    rintro ⟨Z, gap⟩
    exact result ⟨liftObservedSet k Z, equivalent.mpr gap⟩
  | some Z =>
    obtain ⟨passes, minimal⟩ := result
    let original := restrictObservedSet k Z
    have reconstruct : liftObservedSet k original = Z := restrict_lift passes.2.1
    have isOriginal : G.IsMSeparator X Y I R original := equivalent.mp (reconstruct ▸ passes)
    refine ⟨isOriginal, ?_⟩
    intro W feasible subset u present
    have liftedSubset : ∀ v, liftObservedSet k W v = true → Z v = true :=
      reconstruct ▸ lift_implies subset
    have selected := minimal (liftObservedSet k W) (equivalent.mpr feasible) liftedSubset (obs k u) present
    simpa using selected

/-- Enumerate the latent roots and use the explicit-DAG search. -/
def findMinimalADMGSeparator (G : MixedGraph n) (X Y I R : Fin n → Bool) : Option (Fin n → Bool) :=
  G.findMinimalMSeparatorViaLatents G.bidirectedPairs.get X Y I R

theorem find_minimal_admg_separator_correct (G : MixedGraph n) (X Y I R : Fin n → Bool)
    (directedBidirected : ∀ u v, G.edge u false v false = false)
    (disjoint : ∀ v, X v = true → Y v = false)
    (requiredAllowed : ∀ v, I v = true → R v = true)
    (allowedLeft : ∀ v, R v = true → X v = false)
    (allowedRight : ∀ v, R v = true → Y v = false) :
    match G.findMinimalADMGSeparator X Y I R with
    | none => ¬ ∃ Z, G.IsMSeparator X Y I R Z
    | some Z => G.IsMinimalMSeparator X Y I R Z :=
  G.find_minimal_m_separator_via_latents_correct G.bidirectedPairs.get X Y I R
    G.bidirected_pairs_represent directedBidirected disjoint requiredAllowed allowedLeft allowedRight

end

end OpenCausalScience.MixedGraph
