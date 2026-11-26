module
public import OpenCausalScience.Graph.Moralization
public import OpenCausalScience.Papers.PerkovicEtAl2018.DAGAdjustment

/-! # The adjustment efficiency graph

[Smucler, Sapienza and Rotnitzky (2022)](https://doi.org/10.1093/biomet/asab018),
[arXiv:2004.10521v3](https://arxiv.org/pdf/2004.10521v3), Definition 6
and Lemma 3. A walk in the projected graph expands its shortcut edges into
walks through ignored vertices. A walk in the original graph contracts each
such segment. When the conditioning set contains the policy covariates,
the extra edges incident to those covariates do not contribute to a walk
avoiding the conditioning set.
-/

namespace OpenCausalScience.Papers.SmuclerEtAl2022.EfficiencyGraph

open OpenCausalScience.Moralization (Ancestor Query)
open OpenCausalScience.Papers.PerkovicEtAl2018.DAGAdjustment (Forbidden firstArrow properBackDoor)
open OpenCausalScience.Papers.KimEtAl2026.BayesBallCorrectness (Conditioning)

@[expose] public section

/-- Walk with every vertex, including its endpoints, belonging to `allowed`. -/
inductive Walk {α : Type} (edge : α → α → Prop) (allowed : α → Prop) :
    α → α → Prop
  | nil {u} : allowed u → Walk edge allowed u u
  | cons {u v w} : allowed u → edge u v → Walk edge allowed v w → Walk edge allowed u w

private theorem Walk.source {α : Type} {edge : α → α → Prop} {allowed : α → Prop}
    {u v : α} (walk : Walk edge allowed u v) : allowed u := by
  cases walk with
  | nil here => exact here
  | cons here _ _ => exact here

private theorem Walk.append {α : Type} {edge : α → α → Prop} {allowed : α → Prop}
    {u v w : α} (initial : Walk edge allowed u v) (suffix : Walk edge allowed v w) :
    Walk edge allowed u w := by
  induction initial with
  | nil _ => exact suffix
  | cons here step _ ih => exact .cons here step (ih suffix)

/-- A nonempty walk with every interior vertex ignored. -/
inductive Shortcut {α : Type} (edge : α → α → Prop) (ignored : α → Prop) :
    α → α → Prop
  | edge {u v} : edge u v → Shortcut edge ignored u v
  | cons {u v w} : edge u v → ignored v → Shortcut edge ignored v w → Shortcut edge ignored u w

private theorem Shortcut.snoc {α : Type} {edge : α → α → Prop} {ignored : α → Prop}
    {u v w : α} (path : Shortcut edge ignored u v) (skip : ignored v) (last : edge v w) :
    Shortcut edge ignored u w := by
  induction path with
  | edge first => exact .cons first skip (.edge last)
  | cons first middle _ ih => exact .cons first middle (ih skip last)

private theorem Shortcut.expand {α : Type} {edge : α → α → Prop} {ignored allowed : α → Prop}
    {u v : α} (path : Shortcut edge ignored u v) (left : allowed u) (right : allowed v)
    (inside : ∀ w, ignored w → allowed w) : Walk edge allowed u v := by
  induction path with
  | edge step => exact .cons left step (.nil right)
  | cons step skip _ ih => exact .cons left step (ih (inside _ skip) right)

variable {α : Type} {edge : α → α → Prop} {retained policy W : α → Prop} {a y u v : α}

/-- The policy edges join each retained policy variable to both query endpoints. -/
def policyEdge (policy : α → Prop) (a y u v : α) : Prop :=
  ((u = a ∨ u = y) ∧ policy v) ∨ ((v = a ∨ v = y) ∧ policy u)

/-- Project the original graph to the retained vertices and add the policy edges. -/
def projectedEdge (edge : α → α → Prop) (retained policy : α → Prop) (a y u v : α) : Prop :=
  retained u ∧ retained v ∧ u ≠ v ∧
    (Shortcut edge (fun x => ¬ retained x) u v ∨ policyEdge policy a y u v)

private theorem expand {u v : α}
    (walk : Walk (projectedEdge edge retained policy a y) (fun x => retained x ∧ ¬ W x) u v)
    (policyIn : ∀ x, policy x → W x) (conditionRetained : ∀ x, W x → retained x) :
    Walk edge (fun x => ¬ W x) u v := by
  induction walk with
  | nil here => exact .nil here.2
  | cons here step rest ih =>
    rcases step.2.2.2 with short | extra
    · exact (short.expand here.2 rest.source.2 (fun x hidden hx => hidden (conditionRetained x hx))).append ih
    · rcases extra with fromEndpoint | toEndpoint
      · exact (rest.source.2 (policyIn _ fromEndpoint.2)).elim
      · exact (here.2 (policyIn _ toEndpoint.2)).elim

private theorem compress_suffix {s t : α} (walk : Walk edge (fun x => ¬ W x) s t)
    (targetKept : retained t) :
    ∀ {p}, retained p → ¬ W p → Shortcut edge (fun x => ¬ retained x) p s →
      Walk (projectedEdge edge retained policy a y) (fun x => retained x ∧ ¬ W x) p t := by
  classical
  induction walk with
  | @nil s hs =>
    intro p hp hwp shortcut
    by_cases same : p = s
    · subst p
      exact .nil ⟨targetKept, hs⟩
    · exact .cons ⟨hp, hwp⟩ ⟨hp, targetKept, same, .inl shortcut⟩ (.nil ⟨targetKept, hs⟩)
  | @cons s next t hs step rest ih =>
    intro p hp hwp shortcut
    by_cases kept : retained s
    · have tail := ih targetKept kept hs (.edge step)
      by_cases same : p = s
      · subst p
        exact tail
      · exact .cons ⟨hp, hwp⟩ ⟨hp, kept, same, .inl shortcut⟩ tail
    · exact ih targetKept hp hwp (shortcut.snoc kept step)

private theorem compress (walk : Walk edge (fun x => ¬ W x) u v)
    (sourceKept : retained u) (targetKept : retained v) :
    Walk (projectedEdge edge retained policy a y) (fun x => retained x ∧ ¬ W x) u v := by
  cases walk with
  | nil here => exact .nil ⟨sourceKept, here⟩
  | cons here step rest => exact compress_suffix rest targetKept sourceKept here (.edge step)

/-- Lemma 3, for any underlying edge relation. Walk and path separation
coincide because deleting cycles from a walk keeps its vertices allowed. -/
theorem separation_iff_projected_separation
    (sourceKept : retained u) (targetKept : retained v)
    (policyIn : ∀ x, policy x → W x) (conditionRetained : ∀ x, W x → retained x) :
    (¬ Walk edge (fun x => ¬ W x) u v) ↔
      ¬ Walk (projectedEdge edge retained policy a y) (fun x => retained x ∧ ¬ W x) u v :=
  not_congr ⟨fun walk => compress walk sourceKept targetKept,
    fun walk => expand walk policyIn conditionRetained⟩

variable {n : Nat}

/-- The vertex set of H₀ in Definition 6. Ancestors are taken in the original DAG. -/
def ancestralVertices (G : DAG n) (a y : Fin n) (policy : Fin n → Prop) (u : Fin n) : Prop :=
  ∃ v, (v = a ∨ v = y ∨ policy v) ∧ Ancestor G u v

def backDoor (G : DAG n) (a y : Fin n) : DAG n :=
  properBackDoor G (fun x => x == a) (fun x => x == y)

/-- The edge relation of H₀, the moralized proper back-door graph on the
ancestors of treatment, outcome and policy covariates. -/
def h0Edge (G : DAG n) (a y : Fin n) (policy : Fin n → Prop) (u v : Fin n) : Prop :=
  ancestralVertices G a y policy u ∧ ancestralVertices G a y policy v ∧ u ≠ v ∧
    let pbd := backDoor G a y
    pbd.edge u v = true ∨ pbd.edge v u = true ∨
      ∃ c, ancestralVertices G a y policy c ∧ pbd.edge u c = true ∧ pbd.edge v c = true

/-- The observed, eligible ancestral covariates, together with the endpoints.
The paper's forbidden set also includes the treatment itself. -/
def retainedVertices (G : DAG n) (a y : Fin n) (policy observed : Fin n → Prop) (u : Fin n) : Prop :=
  ancestralVertices G a y policy u ∧
    (u = a ∨ u = y ∨ (observed u ∧ ¬ Forbidden G (fun x => x == a) (fun x => x == y) u))

def h1Edge (G : DAG n) (a y : Fin n) (policy observed : Fin n → Prop) :
    Fin n → Fin n → Prop :=
  projectedEdge (h0Edge G a y policy) (retainedVertices G a y policy observed) policy a y

/-- Lemma 3 for the graphs of Definition 6. A non-retained interior vertex
of a shortcut necessarily belongs to H₀, since each H₀ edge has ancestral endpoints. -/
theorem h0_separation_iff_h1_separation
    {G : DAG n} {a y u v : Fin n} {policy observed W : Fin n → Prop}
    (sourceKept : retainedVertices G a y policy observed u)
    (targetKept : retainedVertices G a y policy observed v)
    (policyIn : ∀ x, policy x → W x)
    (conditionRetained : ∀ x, W x → retainedVertices G a y policy observed x) :
    (¬ Walk (h0Edge G a y policy) (fun x => ¬ W x) u v) ↔
      ¬ Walk (h1Edge G a y policy observed)
        (fun x => retainedVertices G a y policy observed x ∧ ¬ W x) u v :=
  separation_iff_projected_separation sourceKept targetKept policyIn conditionRetained

/-- H₁ vertex cut between the treatment and outcome. -/
def VertexCut (G : DAG n) (a y : Fin n) (policy observed W : Fin n → Prop) : Prop :=
  ¬ W a ∧ ¬ W y ∧ (∀ x, W x → retainedVertices G a y policy observed x) ∧
    ¬ Walk (h1Edge G a y policy observed)
      (fun x => retainedVertices G a y policy observed x ∧ ¬ W x) a y

/-- The graphical cut correspondence: H₁ cuts are precisely H₀ separators
among eligible ancestral covariates that include the policy variables. -/
theorem vertex_cut_iff_eligible_h0_separator
    {G : DAG n} {a y : Fin n} {policy observed W : Fin n → Prop}
    (policyCovariates : ∀ x, policy x →
      x ≠ a ∧ x ≠ y ∧ retainedVertices G a y policy observed x) :
    VertexCut G a y policy observed W ↔
      ¬ W a ∧ ¬ W y ∧ (∀ x, W x → retainedVertices G a y policy observed x) ∧
      (∀ x, policy x → W x) ∧ ¬ Walk (h0Edge G a y policy) (fun x => ¬ W x) a y := by
  have aKept : retainedVertices G a y policy observed a :=
    ⟨⟨a, .inl rfl, .inl rfl⟩, .inl rfl⟩
  have yKept : retainedVertices G a y policy observed y :=
    ⟨⟨y, .inr (.inl rfl), .inl rfl⟩, .inr (.inl rfl)⟩
  constructor
  · rintro ⟨ha, hy, eligible, separated⟩
    have includesPolicy : ∀ x, policy x → W x := by
      intro x hx
      classical
      apply Classical.byContradiction
      intro absent
      obtain ⟨xa, xy, xKept⟩ := policyCovariates x hx
      have first : h1Edge G a y policy observed a x :=
        ⟨aKept, xKept, Ne.symm xa, .inr (.inl ⟨.inl rfl, hx⟩)⟩
      have second : h1Edge G a y policy observed x y :=
        ⟨xKept, yKept, xy, .inr (.inr ⟨.inr rfl, hx⟩)⟩
      exact separated (.cons ⟨aKept, ha⟩ first
        (.cons ⟨xKept, absent⟩ second (.nil ⟨yKept, hy⟩)))
    exact ⟨ha, hy, eligible, includesPolicy,
      (h0_separation_iff_h1_separation aKept yKept includesPolicy eligible).mpr separated⟩
  · rintro ⟨ha, hy, eligible, includesPolicy, separated⟩
    exact ⟨ha, hy, eligible,
      (h0_separation_iff_h1_separation aKept yKept includesPolicy eligible).mp separated⟩

variable {G : DAG n} {a y : Fin n} {L W : Fin n → Prop}

private theorem back_door_edge_imp {u v : Fin n} (edge : (backDoor G a y).edge u v = true) :
    G.edge u v = true :=
  (Bool.and_eq_true_iff.mp edge).1

private theorem back_door_ancestor_imp {u v : Fin n} (path : Ancestor (backDoor G a y) u v) :
    Ancestor G u v := by
  rcases path with rfl | path
  · exact .inl rfl
  apply Or.inr
  induction path with
  | single edge => exact .single (back_door_edge_imp edge)
  | extend _ edge ih => exact .extend ih (back_door_edge_imp edge)

private theorem edge_retained_or_source {u v : Fin n} (edge : G.edge u v = true) :
    (backDoor G a y).edge u v = true ∨ u = a := by
  by_cases same : u = a
  · exact .inr same
  · exact .inl (by simp [backDoor, properBackDoor, firstArrow, edge, same])

private theorem back_door_ancestor_or_treatment {u v : Fin n}
    (path : Ancestor G u v) :
    Ancestor (backDoor G a y) u v ∨ Ancestor (backDoor G a y) u a := by
  rcases path with rfl | path
  · exact .inl (.inl rfl)
  induction path with
  | single edge =>
    rcases edge_retained_or_source (a := a) (y := y) edge with kept | same
    · exact .inl (.inr (.single kept))
    · exact .inr (.inl same)
  | extend _ edge ih =>
    rcases ih with towardVertex | towardTreatment
    · rcases edge_retained_or_source (a := a) (y := y) edge with kept | same
      · rcases towardVertex with rfl | path
        · exact .inl (.inr (.single kept))
        · exact .inl (.inr (.extend path kept))
      · exact .inr (same ▸ towardVertex)
    · exact .inr towardTreatment

private theorem ancestor_trans {u v w : Fin n} (first : Ancestor G u v)
    (last : Ancestor G v w) : Ancestor G u w := by
  rcases first with rfl | first
  · exact last
  rcases last with rfl | last
  · exact .inr first
  apply Or.inr
  induction last with
  | single arrow => exact .extend first arrow
  | extend _ arrow ih => exact .extend ih arrow

noncomputable def backDoorQuery (G : DAG n) (a y : Fin n) (W : Fin n → Prop) :
    Query (backDoor G a y) := by
  classical
  exact ⟨fun v => v == a, fun v => v == y, Conditioning.ofPredicate _ (fun v => decide (W v))⟩

private theorem back_door_query_outside (v : Fin n) :
    (backDoorQuery G a y W).condition.member v = false ↔ ¬ W v := by
  classical
  simp [backDoorQuery, Conditioning.ofPredicate]

private theorem back_door_query_relevant (v : Fin n)
    (includesPolicy : ∀ w, L w → W w)
    (conditionAncestral : ∀ w, W w → ancestralVertices G a y L w) :
    (backDoorQuery G a y W).relevant v ↔ ancestralVertices G a y L v := by
  classical
  rw [Query.relevant_iff]
  simp only [backDoorQuery, Conditioning.ofPredicate, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨w, (ha | hy | hw), path⟩
    · exact ⟨w, .inl ha, back_door_ancestor_imp path⟩
    · exact ⟨w, .inr (.inl hy), back_door_ancestor_imp path⟩
    · obtain ⟨z, seed, suffix⟩ := conditionAncestral w hw
      exact ⟨z, seed, ancestor_trans (back_door_ancestor_imp path) suffix⟩
  · rintro ⟨w, seed, path⟩
    rcases back_door_ancestor_or_treatment (a := a) (y := y) path with direct | treatment
    · exact ⟨w, seed.imp id (Or.imp id (includesPolicy w)), direct⟩
    · exact ⟨a, .inl rfl, treatment⟩

private theorem back_door_walk_iff {u v : Fin n}
    (sourceOutside : ¬ W u) (includesPolicy : ∀ w, L w → W w)
    (conditionAncestral : ∀ w, W w → ancestralVertices G a y L w) :
    (backDoorQuery G a y W).MoralWalk u v ↔ Walk (h0Edge G a y L) (fun x => ¬ W x) u v := by
  have relevant (w : Fin n) := back_door_query_relevant w includesPolicy conditionAncestral
  constructor
  · intro path
    induction path with
    | nil _ => exact .nil sourceOutside
    | @cons u v _ first _ ih =>
      have edge : h0Edge G a y L u v := by
        refine ⟨(relevant _).mp first.sourceRelevant, (relevant _).mp first.targetRelevant,
          first.distinct, ?_⟩
        rcases first.connection with forward | backward | ⟨c, hc, fwd, bwd⟩
        · exact .inl forward
        · exact .inr (.inl backward)
        · exact .inr (.inr ⟨c, (relevant _).mp hc, fwd, bwd⟩)
      exact .cons sourceOutside edge (ih ((back_door_query_outside _).mp first.targetOutside))
  · intro path
    induction path with
    | nil _ => exact .nil _
    | cons current first rest ih =>
      obtain ⟨hu, hv, different, edge⟩ := first
      refine .cons ⟨(relevant _).mpr hu, (relevant _).mpr hv,
        (back_door_query_outside _).mpr current,
        (back_door_query_outside _).mpr rest.source, different, ?_⟩ (ih rest.source)
      rcases edge with forward | backward | ⟨c, hc, fwd, bwd⟩
      · exact .inl forward
      · exact .inr (.inl backward)
      · exact .inr (.inr ⟨c, (relevant _).mpr hc, fwd, bwd⟩)

/-- The d-separation condition in the graphical adjustment criterion. -/
def BackDoorSeparated (G : DAG n) (a y : Fin n) (W : Fin n → Prop) : Prop :=
  ¬ (backDoorQuery G a y W).DConnection

private theorem back_door_separated_iff (leftOutside : ¬ W a) (rightOutside : ¬ W y)
    (includesPolicy : ∀ w, L w → W w)
    (conditionAncestral : ∀ w, W w → ancestralVertices G a y L w) :
    BackDoorSeparated G a y W ↔ ¬ Walk (h0Edge G a y L) (fun x => ¬ W x) a y := by
  have moral := (backDoorQuery G a y W).dSeparation_iff_no_moralConnection
    (by simpa [backDoorQuery] using (back_door_query_outside a).mpr leftOutside)
    (by simpa [backDoorQuery] using (back_door_query_outside y).mpr rightOutside)
  refine moral.trans (not_congr ⟨?_, ?_⟩)
  · rintro ⟨u, v, hu, hv, path⟩
    have left : u = a := eq_of_beq hu
    have right : v = y := eq_of_beq hv
    subst u v
    exact (back_door_walk_iff leftOutside includesPolicy conditionAncestral).mp path
  · intro path
    exact ⟨a, y, by simp [backDoorQuery], by simp [backDoorQuery],
      (back_door_walk_iff leftOutside includesPolicy conditionAncestral).mpr path⟩

/-- The graphical part of Lemma 6(1–2). Cuts in H₁ correspond to
conditioning sets that contain the policy covariates, lie among observed
eligible ancestors, and d-separate treatment and outcome in the proper
back-door graph. The statistical equivalence used by the paper is separate. -/
theorem vertex_cut_iff_ancestral_graphical_adjustment
    {observed : Fin n → Prop}
    (policyCovariates : ∀ x, L x →
      x ≠ a ∧ x ≠ y ∧ retainedVertices G a y L observed x) :
    VertexCut G a y L observed W ↔
      (∀ x, L x → W x) ∧
      (∀ x, W x → ancestralVertices G a y L x ∧ observed x ∧ x ≠ a ∧ x ≠ y ∧
        ¬ Forbidden G (fun x => x == a) (fun x => x == y) x) ∧
      BackDoorSeparated G a y W := by
  rw [vertex_cut_iff_eligible_h0_separator policyCovariates]
  constructor
  · rintro ⟨ha, hy, kept, includes, separated⟩
    refine ⟨includes, ?_, (back_door_separated_iff ha hy includes (fun x h => (kept x h).1)).mpr separated⟩
    intro x hx
    have xa : x ≠ a := fun eq => ha (eq ▸ hx)
    have xy : x ≠ y := fun eq => hy (eq ▸ hx)
    obtain ⟨ancestral, choices⟩ := kept x hx
    obtain ⟨observable, allowed⟩ := (choices.resolve_left xa).resolve_left xy
    exact ⟨ancestral, observable, xa, xy, allowed⟩
  · rintro ⟨includes, allowed, separated⟩
    have ha : ¬ W a := fun h => (allowed a h).2.2.1 rfl
    have hy : ¬ W y := fun h => (allowed y h).2.2.2.1 rfl
    refine ⟨ha, hy, ?_, includes,
      (back_door_separated_iff ha hy includes (fun x h => (allowed x h).1)).mp separated⟩
    intro x hx
    obtain ⟨ancestral, observable, _, _, allowed⟩ := allowed x hx
    exact ⟨ancestral, .inr (.inr ⟨observable, allowed⟩)⟩

end

end OpenCausalScience.Papers.SmuclerEtAl2022.EfficiencyGraph
