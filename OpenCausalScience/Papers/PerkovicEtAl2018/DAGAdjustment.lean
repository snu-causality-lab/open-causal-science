module
public import OpenCausalScience.Papers.KimEtAl2026.BayesBallCorrectness
public import OpenCausalScience.Papers.JeongEtAl2022.Lemma4

/-! # Forbidden vertices and the proper back-door graph for DAGs

[Perković et al. (2018)](https://jmlr.org/papers/v18/16-319.html),
Definitions 3 and 6. The paper takes the descendants of every non-treatment
vertex on every proper causal path. The CGA DAG algorithm finds the first
arrows of such paths by reachability outside the treatment set, and takes
descendants of their heads in the original graph. Lean proves that these
computations give the paper's forbidden set and delete exactly its proper
back-door edges. The depth-first traversal in Python, mixed graph cases,
and the probability statement of the adjustment criterion are separate.
-/

namespace OpenCausalScience.Papers.PerkovicEtAl2018.DAGAdjustment

open OpenCausalScience.FrontDoorPathBlocking (withoutVertices)
open OpenCausalScience.Papers.KimEtAl2026.BayesBallCorrectness (hasDirectedWalk hasDirectedWalk_iff)

@[expose] public section

variable {n : Nat}

/-- Descendancy includes the vertex itself. -/
def Descendant (graph : DAG n) (source target : Fin n) : Prop :=
  source = target ∨ graph.DirectedWalk source target

private theorem walk_prepend (graph : DAG n) {a b c : Fin n}
    (edge : graph.edge a b = true) (walk : graph.DirectedWalk b c) :
    graph.DirectedWalk a c := by
  induction walk with
  | single next => exact .extend (.single edge) next
  | extend _ next ih => exact .extend ih next

private theorem descendant_trans (graph : DAG n) {a b c : Fin n}
    (ab : Descendant graph a b) (bc : Descendant graph b c) : Descendant graph a c := by
  rcases ab with rfl | ab
  · exact bc
  rcases bc with rfl | bc
  · exact .inr ab
  apply Or.inr
  induction bc with
  | single edge => exact .extend ab edge
  | extend _ edge ih => exact .extend ih edge

/-- Directed path after the first arrow out of the treatment set.
All its vertices lie outside the treatment set. The list stores the
vertices following the source, including the target for a nonempty path.
A DAG's increasing ranks make every directed sequence vertex-simple. -/
inductive Suffix (graph : DAG n) (treatment : Fin n → Bool) :
    Fin n → List (Fin n) → Fin n → Prop
  | singleton {v} : treatment v = false → Suffix graph treatment v [] v
  | step {u v w vs} : treatment u = false → graph.edge u v = true →
      Suffix graph treatment v vs w → Suffix graph treatment u (v :: vs) w

private theorem Suffix.source_outside {graph : DAG n} {treatment : Fin n → Bool}
    {source target : Fin n} {vertices : List (Fin n)}
    (path : Suffix graph treatment source vertices target) : treatment source = false := by
  cases path with
  | singleton outside => exact outside
  | step outside _ _ => exact outside

private theorem Suffix.append_edge {graph : DAG n} {treatment : Fin n → Bool}
    {source middle target : Fin n} {vertices : List (Fin n)}
    (path : Suffix graph treatment source vertices middle)
    (edge : graph.edge middle target = true) (outside : treatment target = false) :
    Suffix graph treatment source (vertices ++ [target]) target := by
  induction path with
  | singleton outsideSource => exact .step outsideSource edge (.singleton outside)
  | step outsideSource first _ ih => exact .step outsideSource first (ih edge)

private theorem Suffix.source_descendant {graph : DAG n} {treatment : Fin n → Bool}
    {source target : Fin n} {vertices : List (Fin n)}
    (path : Suffix graph treatment source vertices target) {v : Fin n}
    (onPath : v ∈ source :: vertices) : Descendant graph source v := by
  induction path with
  | singleton _ => exact .inl (List.mem_singleton.mp onPath).symm
  | step _ edge _ ih =>
    rcases List.mem_cons.mp onPath with rfl | tail
    · exact .inl rfl
    · exact descendant_trans graph (.inr (.single edge)) (ih tail)

/-- Every encoded suffix is a simple path in a DAG. -/
theorem Suffix.nodup {graph : DAG n} {treatment : Fin n → Bool}
    {source target : Fin n} {vertices : List (Fin n)}
    (path : Suffix graph treatment source vertices target) :
    (source :: vertices).Nodup := by
  induction path with
  | singleton _ => simp
  | @step u v w vs outside edge tail ih =>
    refine List.nodup_cons.mpr ⟨?_, ih⟩
    intro repeated
    have rank := graph.edge_increases u v edge
    rcases tail.source_descendant repeated with same | walk
    · rw [same] at rank
      exact Nat.lt_irrefl _ rank
    · exact Nat.lt_asymm rank (graph.rank_lt_of_directedWalk walk)

private theorem Suffix.to_deleted {graph : DAG n} {treatment : Fin n → Bool}
    {source target : Fin n} {vertices : List (Fin n)}
    (path : Suffix graph treatment source vertices target) :
    Descendant (withoutVertices graph treatment) source target := by
  induction path with
  | singleton _ => exact .inl rfl
  | @step u v w vs outside edge tail ih =>
    have kept : (withoutVertices graph treatment).edge u v = true := by
      simp [withoutVertices, edge, outside, tail.source_outside]
    rcases ih with same | walk
    · exact .inr (same ▸ DAG.DirectedWalk.single kept)
    · exact .inr (walk_prepend _ kept walk)

private theorem suffix_of_deleted_walk {graph : DAG n} {treatment : Fin n → Bool}
    {source target : Fin n}
    (walk : (withoutVertices graph treatment).DirectedWalk source target) :
    ∃ vertices, Suffix graph treatment source vertices target := by
  have unpack {u v : Fin n} (edge : (withoutVertices graph treatment).edge u v = true) :
      graph.edge u v = true ∧ treatment u = false ∧ treatment v = false := by
    simpa [withoutVertices, Bool.and_eq_true_iff] using edge
  induction walk with
  | single edge =>
    obtain ⟨edge, u, v⟩ := unpack edge
    exact ⟨_, .step u edge (.singleton v)⟩
  | extend _ edge ih =>
    obtain ⟨vertices, path⟩ := ih
    obtain ⟨edge, _, v⟩ := unpack edge
    exact ⟨_, path.append_edge edge v⟩

def reaches (graph : DAG n) (source target : Fin n) : Bool :=
  (source == target) || hasDirectedWalk graph source target

theorem reaches_iff (graph : DAG n) (source target : Fin n) :
    reaches graph source target = true ↔ Descendant graph source target := by
  simp [reaches, Descendant, hasDirectedWalk_iff]

/-- CGA tests reachability to an outcome after blocking all treatments
following the first arrow. -/
def firstArrow (graph : DAG n) (treatment outcome : Fin n → Bool) (a b : Fin n) : Bool :=
  treatment a && graph.edge a b && !treatment b &&
    (List.finRange n).any (fun y => outcome y && reaches (withoutVertices graph treatment) b y)

theorem first_arrow_iff (graph : DAG n) (treatment outcome : Fin n → Bool) (a b : Fin n) :
    firstArrow graph treatment outcome a b = true ↔
      treatment a = true ∧ graph.edge a b = true ∧
      ∃ vertices y, outcome y = true ∧ Suffix graph treatment b vertices y := by
  simp only [firstArrow, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true,
    List.mem_finRange, true_and, reaches_iff]
  constructor
  · rintro ⟨⟨⟨aIn, edge⟩, bOut⟩, y, yIn, rfl | walk⟩
    · exact ⟨aIn, edge, [], b, yIn, .singleton bOut⟩
    · obtain ⟨vertices, path⟩ := suffix_of_deleted_walk walk
      exact ⟨aIn, edge, vertices, y, yIn, path⟩
  · rintro ⟨aIn, edge, vertices, y, yIn, path⟩
    exact ⟨⟨⟨aIn, edge⟩, path.source_outside⟩, y, yIn, path.to_deleted⟩

/-- Definition 3 for DAGs. Use every non-treatment vertex on each proper
causal path, then take all descendants in the original DAG. -/
def Forbidden (graph : DAG n) (treatment outcome : Fin n → Bool) (z : Fin n) : Prop :=
  ∃ a b vertices y v, treatment a = true ∧ graph.edge a b = true ∧ outcome y = true ∧
    Suffix graph treatment b vertices y ∧ v ∈ b :: vertices ∧ Descendant graph v z

/-- CGA uses only the heads of relevant first arrows as the seeds for
descendant reachability in the original DAG. -/
def forbiddenFromFirst (graph : DAG n) (treatment outcome : Fin n → Bool) (z : Fin n) : Bool :=
  (List.finRange n).any (fun b =>
    (List.finRange n).any (fun a => firstArrow graph treatment outcome a b) &&
      reaches graph b z)

theorem forbidden_from_first_iff (graph : DAG n) (treatment outcome : Fin n → Bool) (z : Fin n) :
    forbiddenFromFirst graph treatment outcome z = true ↔ Forbidden graph treatment outcome z := by
  simp only [forbiddenFromFirst, List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true,
    first_arrow_iff, reaches_iff, Forbidden]
  constructor
  · rintro ⟨b, ⟨a, aIn, edge, vertices, y, yIn, path⟩, reach⟩
    exact ⟨a, b, vertices, y, b, aIn, edge, yIn, path, List.mem_cons_self, reach⟩
  · rintro ⟨a, b, vertices, y, v, aIn, edge, yIn, path, onPath, reach⟩
    exact ⟨b, ⟨a, aIn, edge, vertices, y, yIn, path⟩,
      descendant_trans graph (path.source_descendant onPath) reach⟩

/-- Definition 6 for DAGs, using the executable first-arrow predicate. -/
def properBackDoor (graph : DAG n) (treatment outcome : Fin n → Bool) : DAG n where
  edge a b := graph.edge a b && !firstArrow graph treatment outcome a b
  rank := graph.rank
  edge_increases a b edge := graph.edge_increases a b (Bool.and_eq_true_iff.mp edge).1

theorem proper_backdoor_removes_iff (graph : DAG n) (treatment outcome : Fin n → Bool)
    (a b : Fin n) (edge : graph.edge a b = true) :
    (properBackDoor graph treatment outcome).edge a b = false ↔
      treatment a = true ∧ ∃ vertices y, outcome y = true ∧ Suffix graph treatment b vertices y := by
  simp [properBackDoor, edge, first_arrow_iff]

end

end OpenCausalScience.Papers.PerkovicEtAl2018.DAGAdjustment
