module
public import OpenCausalScience.Papers.PerkovicEtAl2018.MixedBackDoor

/-! # Proper-path blocking and back-door deletion

Perković et al. (2018), Theorem 7, for the fully oriented graph case.
The marked path representation distinguishes a directed edge from a parallel
bidirected edge. Visibility is a supplied predicate, with amenability stated
for proper directed treatment-to-outcome paths. Source: https://jmlr.org/papers/v18/16-319.html.
-/

namespace OpenCausalScience.Papers.PerkovicEtAl2018.ProperPathBlocking

open OpenCausalScience.Papers.PerkovicEtAl2018.MixedBackDoor

@[expose] public section

variable {n : Nat}

/-- The descendants of the heads of all first arrows of proper causal paths. -/
def Forbidden (graph : MixedGraph n) (treatment outcome : Fin n → Bool) (v : Fin n) : Prop :=
  ∃ a b, FirstVisibleArrow graph treatment outcome (fun _ _ => true) a b ∧
    graph.AncestorOf (· == v) b

/-- `through` occurs on a directed suffix after the first arrow. -/
inductive ThroughVertex (graph : MixedGraph n) (treatment : Fin n → Bool) (through : Fin n) :
    Fin n → Fin n → Prop
  | initial {y} : DirectedSuffix graph treatment through y → ThroughVertex graph treatment through through y
  | later {u v y} : treatment u = false → graph.edge u false v true = true →
      ThroughVertex graph treatment through v y → ThroughVertex graph treatment through u y

/-- Definition 3 in a fully oriented graph, taking descendants of every
non-treatment vertex on every proper directed path. -/
def ForbiddenOnPaths (graph : MixedGraph n) (treatment outcome : Fin n → Bool) (v : Fin n) : Prop :=
  ∃ a b c y, treatment a = true ∧ graph.edge a false b true = true ∧ outcome y = true ∧
    ThroughVertex graph treatment c b y ∧ graph.AncestorOf (· == v) c

private theorem ThroughVertex.directed_suffix {graph : MixedGraph n} {treatment : Fin n → Bool}
    {c u y : Fin n} (visit : ThroughVertex graph treatment c u y) : DirectedSuffix graph treatment u y := by
  induction visit with
  | initial suffix => exact suffix
  | later outside edge _ ih => exact .step outside edge ih

private theorem ThroughVertex.prepend_to_ancestor {graph : MixedGraph n} {treatment conditioning : Fin n → Bool}
    {c u y : Fin n} (visit : ThroughVertex graph treatment c u y)
    (ancestor : graph.AncestorOf conditioning c) : graph.AncestorOf conditioning u := by
  induction visit with
  | initial _ => exact ancestor
  | later _ edge _ ih => exact .parent edge ih

theorem forbidden_iff_forbidden_on_paths (graph : MixedGraph n) (treatment outcome : Fin n → Bool)
    (v : Fin n) : Forbidden graph treatment outcome v ↔ ForbiddenOnPaths graph treatment outcome v := by
  constructor
  · rintro ⟨a, b, ⟨edge, starts, _, y, ends, suffix⟩, reaches⟩
    exact ⟨a, b, b, y, starts, edge, ends, .initial suffix, reaches⟩
  · rintro ⟨a, b, c, y, starts, edge, ends, visits, reaches⟩
    exact ⟨a, b, ⟨edge, starts, rfl, y, ends, visits.directed_suffix⟩, visits.prepend_to_ancestor reaches⟩

def AvoidsForbidden (graph : MixedGraph n) (treatment outcome conditioning : Fin n → Bool) : Prop :=
  ∀ v, Forbidden graph treatment outcome v → conditioning v = false

def Amenable (graph : MixedGraph n) (treatment outcome : Fin n → Bool)
    (visible : Fin n → Fin n → Bool) : Prop :=
  ∀ u v, FirstVisibleArrow graph treatment outcome (fun _ _ => true) u v → visible u v = true

/-- A marked active suffix with no treatment vertex. The last index records
whether its edges all point forward. The list omits the initial vertex. -/
inductive ProperSuffix (graph : MixedGraph n) (treatment conditioning : Fin n → Bool) :
    MixedGraph.Arrival n → List (Fin n) → MixedGraph.Arrival n → Bool → Prop
  | done (s) : treatment s.1 = false → ProperSuffix graph treatment conditioning s [] s true
  | step {s t last visited outgoing directed} : treatment s.1 = false →
      graph.edge s.1 outgoing t.1 t.2 = true → graph.openTurn conditioning s outgoing →
      ProperSuffix graph treatment conditioning t visited last directed →
      ProperSuffix graph treatment conditioning s (t.1 :: visited) last (!outgoing && t.2 && directed)

def ProperOpenPath (graph : MixedGraph n) (treatment outcome conditioning : Fin n → Bool)
    (directed : Bool) : Prop :=
  ∃ source outgoing first visited last directedSuffix,
    treatment source = true ∧ graph.edge source outgoing first.1 first.2 = true ∧
    ProperSuffix graph treatment conditioning first visited last directedSuffix ∧ outcome last.1 = true ∧
    (source :: first.1 :: visited).Nodup ∧ (!outgoing && first.2 && directedSuffix) = directed

private theorem prepend_ancestor {graph : MixedGraph n} {treatment outcome : Fin n → Bool}
    {u v : Fin n} (forbidden : Forbidden graph treatment outcome u)
    (edge : graph.edge u false v true = true) : Forbidden graph treatment outcome v := by
  obtain ⟨a, b, first, reaches⟩ := forbidden
  refine ⟨a, b, first, ?_⟩
  clear first
  induction reaches with
  | @conditioned w atTarget =>
    have same : w = u := by simpa using atTarget
    subst w
    exact .parent edge (.conditioned (by simp))
  | parent arrow _ ih => exact .parent arrow ih

private theorem forbidden_of_cut {graph : MixedGraph n} {treatment outcome : Fin n → Bool}
    {visible : Fin n → Fin n → Bool} {u v : Fin n}
    (first : FirstVisibleArrow graph treatment outcome visible u v) :
    Forbidden graph treatment outcome v := by
  obtain ⟨edge, source, _, suffix⟩ := first
  exact ⟨u, v, ⟨edge, source, rfl, suffix⟩, .conditioned (by simp)⟩

private theorem forbidden_not_ancestor {graph : MixedGraph n} {treatment outcome conditioning : Fin n → Bool}
    (avoids : AvoidsForbidden graph treatment outcome conditioning) {v : Fin n}
    (ancestor : graph.AncestorOf conditioning v) : ¬ Forbidden graph treatment outcome v := by
  induction ancestor with
  | conditioned inSet =>
    intro forbidden
    simp [avoids _ forbidden] at inSet
  | parent edge _ ih => exact fun forbidden => ih (prepend_ancestor forbidden edge)

private theorem ancestor_survives {graph : MixedGraph n} {treatment outcome conditioning : Fin n → Bool}
    (visible : Fin n → Fin n → Bool) (avoids : AvoidsForbidden graph treatment outcome conditioning)
    {v : Fin n} (ancestor : graph.AncestorOf conditioning v) :
    (properBackDoor graph treatment outcome visible).AncestorOf conditioning v := by
  induction ancestor with
  | conditioned inSet => exact .conditioned inSet
  | @parent u w edge tail ih =>
    apply MixedGraph.AncestorOf.parent _ ih
    cases survives : (properBackDoor graph treatment outcome visible).edge u false w true with
    | true => rfl
    | false =>
      have removed := (proper_backdoor_deletes_iff graph treatment outcome visible u w edge).mp survives
      exact (forbidden_not_ancestor avoids tail (forbidden_of_cut removed)).elim

private theorem ancestor_lifts {graph : MixedGraph n} {treatment outcome conditioning : Fin n → Bool}
    {visible : Fin n → Fin n → Bool} {v : Fin n}
    (ancestor : (properBackDoor graph treatment outcome visible).AncestorOf conditioning v) :
    graph.AncestorOf conditioning v := by
  induction ancestor with
  | conditioned inSet => exact .conditioned inSet
  | parent edge _ ih => exact .parent (Bool.and_eq_true_iff.mp edge).1 ih

private theorem ProperSuffix.source_outside {graph : MixedGraph n} {treatment conditioning : Fin n → Bool}
    {source last visited directed} (path : ProperSuffix graph treatment conditioning source visited last directed) :
    treatment source.1 = false := by
  cases path with
  | done _ outside => exact outside
  | step outside _ _ _ => exact outside

private theorem ProperSuffix.to_directed_suffix {graph : MixedGraph n} {treatment conditioning : Fin n → Bool}
    {source last visited directed} (path : ProperSuffix graph treatment conditioning source visited last directed)
    (isDirected : directed = true) : DirectedSuffix graph treatment source.1 last.1 := by
  induction path with
  | done _ outside => exact .done outside
  | @step s t _ _ outgoing _ outside edge _ _ ih =>
    obtain ⟨first, rest⟩ := Bool.and_eq_true_iff.mp isDirected
    obtain ⟨tail, head⟩ := Bool.and_eq_true_iff.mp first
    have outZero : outgoing = false := by simpa using tail
    rw [outZero, head] at edge
    exact .step outside edge (ih rest)

private theorem ProperSuffix.map {graph target : MixedGraph n} {treatment conditioning : Fin n → Bool}
    {source last visited directed} (path : ProperSuffix graph treatment conditioning source visited last directed)
    (retains : ∀ {u v a b}, treatment u = false → treatment v = false →
      graph.edge u a v b = true → target.edge u a v b = true)
    (turns : ∀ s a, graph.openTurn conditioning s a → target.openTurn conditioning s a) :
    ProperSuffix target treatment conditioning source visited last directed := by
  induction path with
  | done s outside => exact .done s outside
  | step outside edge turn suffix ih =>
    exact .step outside (retains outside suffix.source_outside edge) (turns _ _ turn) ih

private theorem ProperSuffix.directed_from_forbidden {graph : MixedGraph n}
    {treatment outcome conditioning : Fin n → Bool} {source last visited directed}
    (path : ProperSuffix graph treatment conditioning source visited last directed)
    (avoids : AvoidsForbidden graph treatment outcome conditioning)
    (forbidden : Forbidden graph treatment outcome source.1) (head : source.2 = true)
    (arrival : ∃ u mark, graph.edge source.1 true u mark = true) : directed = true := by
  induction path with
  | done => rfl
  | @step s t _ _ outgoing _ _ edge turn _ ih =>
    have noCollider : ¬ graph.AncestorOf conditioning s.1 :=
      fun ancestor => forbidden_not_ancestor avoids ancestor forbidden
    have outZero : outgoing = false := by
      cases out : outgoing with
      | false => rfl
      | true => exact (noCollider (by simpa [MixedGraph.openTurn, head, out] using turn)).elim
    have nextHead : t.2 = true := by
      cases arrow : t.2 with
      | true => rfl
      | false =>
        have undirected : graph.edge s.1 false t.1 false = true := by
          simpa [outZero, arrow] using edge
        obtain ⟨u, mark, incident⟩ := arrival
        simp [graph.no_arrow_of_undirected undirected] at incident
    have forward : graph.edge s.1 false t.1 true = true := by simpa [outZero, nextHead] using edge
    have nextArrival : graph.edge t.1 true s.1 false = true :=
      (graph.symmetric _ _ _ _).symm.trans forward
    have remaining := ih (prepend_ancestor forbidden forward) nextHead ⟨s.1, false, nextArrival⟩
    simp [outZero, nextHead, remaining]

private theorem edge_survives_between_nontreatments {graph : MixedGraph n}
    {treatment outcome : Fin n → Bool} {visible : Fin n → Fin n → Bool} {u v : Fin n} {a b : Bool}
    (uOutside : treatment u = false) (vOutside : treatment v = false)
    (arrow : graph.edge u a v b = true) :
    (properBackDoor graph treatment outcome visible).edge u a v b = true := by
  classical
  cases a <;> cases b <;>
    simp [properBackDoor, deleteDirected, keepsMarking, arrow, FirstVisibleArrow, uOutside, vOutside]

private theorem turn_survives {graph : MixedGraph n} {treatment outcome conditioning : Fin n → Bool}
    (visible : Fin n → Fin n → Bool) (avoids : AvoidsForbidden graph treatment outcome conditioning)
    (s : MixedGraph.Arrival n) (out : Bool) (turn : graph.openTurn conditioning s out) :
    (properBackDoor graph treatment outcome visible).openTurn conditioning s out := by
  cases both : s.2 && out with
  | false => simpa [MixedGraph.openTurn, both] using turn
  | true =>
    have ancestor : graph.AncestorOf conditioning s.1 := by
      simpa [MixedGraph.openTurn, both] using turn
    simpa [MixedGraph.openTurn, both] using ancestor_survives visible avoids ancestor

private theorem turn_lifts {graph : MixedGraph n} {treatment outcome conditioning : Fin n → Bool}
    (visible : Fin n → Fin n → Bool) (s : MixedGraph.Arrival n) (out : Bool)
    (turn : (properBackDoor graph treatment outcome visible).openTurn conditioning s out) :
    graph.openTurn conditioning s out := by
  cases both : s.2 && out with
  | false => simpa [MixedGraph.openTurn, both] using turn
  | true =>
    have ancestor : (properBackDoor graph treatment outcome visible).AncestorOf conditioning s.1 := by
      simpa [MixedGraph.openTurn, both] using turn
    simpa [MixedGraph.openTurn, both] using ancestor_lifts ancestor

private theorem first_edge_survives {graph : MixedGraph n} {treatment outcome conditioning : Fin n → Bool}
    (visible : Fin n → Fin n → Bool) (avoids : AvoidsForbidden graph treatment outcome conditioning)
    {source : Fin n} {first last : MixedGraph.Arrival n} {visited : List (Fin n)}
    {outgoing directedSuffix : Bool}
    (edge : graph.edge source outgoing first.1 first.2 = true)
    (suffix : ProperSuffix graph treatment conditioning first visited last directedSuffix)
    (noncausal : (!outgoing && first.2 && directedSuffix) = false) :
    (properBackDoor graph treatment outcome visible).edge source outgoing first.1 first.2 = true := by
  classical
  cases out : outgoing <;> cases head : first.2
  · simpa [properBackDoor, deleteDirected, keepsMarking, out, head] using edge
  · have originalArrow : graph.edge source false first.1 true = true := by simpa [out, head] using edge
    have notCut : ¬ FirstVisibleArrow graph treatment outcome visible source first.1 := by
      intro cut
      have arrival : graph.edge first.1 true source false = true :=
        (graph.symmetric _ _ _ _).symm.trans originalArrow
      have remaining := suffix.directed_from_forbidden avoids (forbidden_of_cut cut) head
        ⟨source, false, arrival⟩
      simp [out, head, remaining] at noncausal
    simp [properBackDoor, deleteDirected, keepsMarking, originalArrow, notCut]
  · simpa [properBackDoor, deleteDirected, keepsMarking, out, head, FirstVisibleArrow,
      suffix.source_outside] using edge
  · simpa [properBackDoor, deleteDirected, keepsMarking, out, head] using edge

/-- With forbidden-set avoidance, a proper noncausal active path survives
the deletion and stays active. -/
theorem proper_noncausal_survives (graph : MixedGraph n) (treatment outcome conditioning : Fin n → Bool)
    (visible : Fin n → Fin n → Bool) (avoids : AvoidsForbidden graph treatment outcome conditioning)
    (path : ProperOpenPath graph treatment outcome conditioning false) :
    ProperOpenPath (properBackDoor graph treatment outcome visible) treatment outcome conditioning false := by
  obtain ⟨u, out, first, visited, last, directed, source, edge, suffix, inOutcome, simple, noncausal⟩ := path
  exact ⟨u, out, first, visited, last, directed, source, first_edge_survives visible avoids edge suffix noncausal,
    suffix.map edge_survives_between_nontreatments (turn_survives visible avoids), inOutcome, simple, noncausal⟩

/-- A proper active path in the back-door graph lifts to a proper noncausal
active path in the original graph if the query is amenable. -/
theorem proper_path_in_backdoor_is_noncausal (graph : MixedGraph n)
    (treatment outcome conditioning : Fin n → Bool) (visible : Fin n → Fin n → Bool)
    (amenable : Amenable graph treatment outcome visible) {causal : Bool}
    (path : ProperOpenPath (properBackDoor graph treatment outcome visible) treatment outcome conditioning causal) :
    ProperOpenPath graph treatment outcome conditioning false := by
  obtain ⟨u, out, first, visited, last, directed, source, edge, suffix, inOutcome, simple, classification⟩ := path
  have original : graph.edge u out first.1 first.2 = true := (Bool.and_eq_true_iff.mp edge).1
  have lifted : ProperSuffix graph treatment conditioning first visited last directed :=
    suffix.map (fun _ _ retained => (Bool.and_eq_true_iff.mp retained).1) (turn_lifts visible)
  refine ⟨u, out, first, visited, last, directed, source, original, lifted, inOutcome, simple, ?_⟩
  cases isDirected : (!out && first.2 && directed) with
  | false => rfl
  | true =>
    obtain ⟨firstArrow, allDirected⟩ := Bool.and_eq_true_iff.mp isDirected
    obtain ⟨tail, head⟩ := Bool.and_eq_true_iff.mp firstArrow
    have outZero : out = false := by simpa using tail
    rw [outZero, head] at original edge
    have suffixDirected := lifted.to_directed_suffix allDirected
    have startVisible : visible u first.1 = true :=
      amenable u first.1 ⟨original, source, rfl, last.1, inOutcome, suffixDirected⟩
    have cut : FirstVisibleArrow graph treatment outcome visible u first.1 :=
      ⟨original, source, startVisible, last.1, inOutcome, suffixDirected⟩
    have erased := (proper_backdoor_deletes_iff graph treatment outcome visible u first.1 original).mpr cut
    simp [erased] at edge

private theorem ProperSuffix.to_active_walk {graph : MixedGraph n} {treatment conditioning : Fin n → Bool}
    {source last visited directed} (path : ProperSuffix graph treatment conditioning source visited last directed) :
    graph.ActiveWalk conditioning source visited last := by
  induction path with
  | done s _ => exact .nil s
  | step _ edge turn _ ih => exact .cons ⟨_, edge, turn⟩ ih

private theorem proper_subpath {graph : MixedGraph n} {treatment outcome conditioning : Fin n → Bool}
    {source last visited} (walk : graph.ActiveWalk conditioning source visited last)
    (simple : (source.1 :: visited).Nodup) (inOutcome : outcome last.1 = true)
    (lastOutside : treatment last.1 = false) :
    (∃ directed, ProperSuffix graph treatment conditioning source visited last directed) ∨
      ∃ directed, ProperOpenPath graph treatment outcome conditioning directed := by
  induction walk with
  | nil s => exact .inl ⟨true, .done s lastOutside⟩
  | @cons s next last visited move _ ih =>
    obtain ⟨out, edge, turn⟩ := move
    rcases ih (List.nodup_cons.mp simple).2 inOutcome lastOutside with ⟨directed, suffix⟩ | shortened
    · cases start : treatment s.1 with
      | false => exact .inl ⟨_, .step start edge turn suffix⟩
      | true => exact .inr ⟨_, s.1, out, next, visited, last, directed, start, edge,
          suffix, inOutcome, simple, rfl⟩
    · exact .inr shortened

private theorem proper_path_of_path_connected {graph : MixedGraph n}
    {treatment outcome conditioning : Fin n → Bool}
    (disjoint : ∀ v, outcome v = true → treatment v = false)
    (path : graph.PathConnected treatment outcome conditioning) :
    ∃ directed, ProperOpenPath graph treatment outcome conditioning directed := by
  obtain ⟨source, out, first, visited, last, starts, edge, walk, ends, simple⟩ := path
  rcases proper_subpath walk (List.nodup_cons.mp simple).2 ends (disjoint last.1 ends) with
    ⟨directed, suffix⟩ | shortened
  · exact ⟨_, source, out, first, visited, last, directed, starts, edge, suffix, ends, simple, rfl⟩
  · exact shortened

/-- The blocking versus m-separation equivalence of Theorem 7 on fully
oriented graphs. Any active path in the back-door graph can start again at
its last treatment vertex to become proper. Under amenability it cannot be
causal. Conversely every proper noncausal active path survives when the
conditioning set avoids the forbidden descendants. -/
theorem proper_noncausal_path_iff_backdoor_connection (graph : MixedGraph n)
    (treatment outcome conditioning : Fin n → Bool) (visible : Fin n → Fin n → Bool)
    (disjoint : ∀ v, outcome v = true → treatment v = false)
    (amenable : Amenable graph treatment outcome visible)
    (avoids : AvoidsForbidden graph treatment outcome conditioning) :
    ProperOpenPath graph treatment outcome conditioning false ↔
      (properBackDoor graph treatment outcome visible).PathConnected treatment outcome conditioning := by
  constructor
  · intro path
    obtain ⟨source, out, first, visited, last, _, starts, edge, suffix, ends, simple, _⟩ :=
      proper_noncausal_survives graph treatment outcome conditioning visible avoids path
    exact ⟨source, out, first, visited, last, starts, edge, suffix.to_active_walk, ends, simple⟩
  · intro path
    obtain ⟨_, proper⟩ := proper_path_of_path_connected disjoint path
    exact proper_path_in_backdoor_is_noncausal graph treatment outcome conditioning visible amenable proper

end

end OpenCausalScience.Papers.PerkovicEtAl2018.ProperPathBlocking
