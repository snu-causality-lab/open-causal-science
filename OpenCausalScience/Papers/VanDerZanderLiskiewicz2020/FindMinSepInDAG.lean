module
public import OpenCausalScience.Graph.Moralization
public import OpenCausalScience.Graph.SeparatorBoundary

/-! # Finding a minimal d-separator in a DAG

[Van der Zander and Liśkiewicz (2020), §3](https://proceedings.mlr.press/v115/van-der-zander20a.html).
The algorithm starts with the allowed ancestors of the query endpoints
and required vertices. It retains the required vertices and the blockers
reachable from the left, then repeats the pruning from the right. The
proof uses the ancestral moral graph to compare reachability and to
witness the necessity of every optional vertex of the result.
-/

namespace OpenCausalScience.Papers.VanDerZanderLiskiewicz2020.FindMinSepInDAG

open OpenCausalScience.Moralization
open OpenCausalScience.Papers.KimEtAl2026.BayesBall (Direction State)
open OpenCausalScience.Papers.KimEtAl2026.BayesBallCorrectness
  (Conditioning Move allStates explore explore_closed explore_covers explore_sound
    hasDirectedWalk hasDirectedWalk_iff)

@[expose] public section

export OpenCausalScience.SeparatorBoundary (Reach keepReached Separated)

namespace Reach

export OpenCausalScience.SeparatorBoundary.Reach (seed step rec recOn casesOn)

end Reach

open OpenCausalScience.SeparatorBoundary (separating_prune necessary_blocker)

variable {n : Nat}

def ancestral (G : DAG n) (X Y I : Fin n → Prop) (v : Fin n) : Prop :=
  ∃ w, (X w ∨ Y w ∨ I w) ∧ Ancestor G v w

/-- Undirected adjacency in the DAG-induced moral graph on `A`. -/
def moralEdge (G : DAG n) (A : Fin n → Prop) (u v : Fin n) : Prop :=
  A u ∧ A v ∧ u ≠ v ∧ (G.edge u v = true ∨ G.edge v u = true ∨
    ∃ c, A c ∧ G.edge u c = true ∧ G.edge v c = true)

private theorem moral_symmetric (G : DAG n) (A : Fin n → Prop) (u v : Fin n)
    (edge : moralEdge G A u v) : moralEdge G A v u := by
  obtain ⟨hu, hv, different, forward | backward | ⟨c, hc, left, right⟩⟩ := edge
  · exact ⟨hv, hu, Ne.symm different, .inr (.inl forward)⟩
  · exact ⟨hv, hu, Ne.symm different, .inl backward⟩
  · exact ⟨hv, hu, Ne.symm different, .inr (.inr ⟨c, hc, right, left⟩)⟩

private theorem distinct_of_edge {G : DAG n} {u v : Fin n} (edge : G.edge u v = true) :
    u ≠ v := by
  intro same
  subst v
  exact Nat.lt_irrefl _ (G.edge_increases _ _ edge)

variable {G : DAG n} {A X Y I Z R : Fin n → Prop}

/-- Figure 3 for DAGs. Enter the next vertex in the ancestral set,
and traverse a blocked vertex only as a collider. -/
def Pass (G : DAG n) (A Z : Fin n → Prop) (s t : State (Fin n)) : Prop :=
  A t.1 ∧ Move G s t ∧ ((s.2 = .down ∧ t.2 = .up) ∨ ¬ Z s.1)

/-- Arrival-state relation of the paper's `Reachable` routine in a DAG. -/
inductive ReachState (G : DAG n) (A X Z : Fin n → Prop) : State (Fin n) → Prop
  | seed {u} : A u → X u → ReachState G A X Z (u, .up)
  | step {s t} : ReachState G A X Z s → Pass G A Z s t → ReachState G A X Z t

def DagReach (G : DAG n) (A X Z : Fin n → Prop) (v : Fin n) : Prop :=
  ∃ arrival, ReachState G A X Z (v, arrival)

private theorem ReachState.relevant {s : State (Fin n)} (reach : ReachState G A X Z s) : A s.1 := by
  cases reach with
  | seed hu _ => exact hu
  | step _ move => exact move.1

private theorem ReachState.to_moral {s : State (Fin n)} (reach : ReachState G A X Z s) :
    Reach (moralEdge G A) X Z s.1 ∧
      (s.2 = .down → ∃ u, A u ∧ ¬ Z u ∧ G.edge u s.1 = true ∧ Reach (moralEdge G A) X Z u) := by
  induction reach with
  | seed _ hx => exact ⟨.seed hx, by simp⟩
  | @step s t prior move ih =>
    have relevant := prior.relevant
    cases dir : t.2 with
    | up =>
      have arrow : G.edge t.1 s.1 = true := by simpa [Move, dir] using move.2.1
      refine ⟨?_, by simp⟩
      rcases move.2.2 with ⟨down, _⟩ | outside
      · obtain ⟨u, hu, outside, first, reaches⟩ := ih.2 down
        classical
        by_cases same : u = t.1
        · exact same ▸ reaches
        · exact .step reaches outside
            ⟨hu, move.1, same, .inr (.inr ⟨s.1, relevant, first, arrow⟩)⟩
      · exact .step ih.1 outside ⟨relevant, move.1, (distinct_of_edge arrow).symm, .inr (.inl arrow)⟩
    | down =>
      have arrow : G.edge s.1 t.1 = true := by simpa [Move, dir] using move.2.1
      have outside : ¬ Z s.1 := by simpa [dir] using move.2.2
      exact ⟨.step ih.1 outside ⟨relevant, move.1, distinct_of_edge arrow, .inl arrow⟩,
        fun _ => ⟨s.1, relevant, outside, arrow, ih.1⟩⟩

/-- Figure 3 reaches exactly the vertices reached in the moral graph when
blocked vertices may be reached but may not be traversed. -/
theorem dag_reach_iff_moral_reach (seedRelevant : ∀ u, X u → A u) (v : Fin n) :
    DagReach G A X Z v ↔ Reach (moralEdge G A) X Z v := by
  constructor
  · rintro ⟨_, reach⟩
    exact reach.to_moral.1
  · intro reach
    induction reach with
    | @seed u hx => exact ⟨.up, .seed (seedRelevant u hx) hx⟩
    | @step u v _ outside edge ih =>
      obtain ⟨arrival, previous⟩ := ih
      obtain ⟨_, hv, _, forward | backward | ⟨c, hc, first, second⟩⟩ := edge
      · exact ⟨.down, .step previous ⟨hv, forward, .inr outside⟩⟩
      · exact ⟨.up, .step previous ⟨hv, backward, .inr outside⟩⟩
      · have intermediate : ReachState G A X Z (c, .down) :=
          .step previous ⟨hc, first, .inr outside⟩
        exact ⟨.up, .step intermediate ⟨hv, second, .inl ⟨rfl, rfl⟩⟩⟩

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

private theorem ancestral_mono (required : ∀ v, I v → Z v) (v : Fin n)
    (ancestor : ancestral G X Y I v) : ancestral G X Y Z v := by
  obtain ⟨w, (hx | hy | hi), path⟩ := ancestor
  · exact ⟨w, .inl hx, path⟩
  · exact ⟨w, .inr (.inl hy), path⟩
  · exact ⟨w, .inr (.inr (required w hi)), path⟩

private theorem ancestral_eq (required : ∀ v, I v → Z v)
    (within : ∀ v, Z v → ancestral G X Y I v) :
    ancestral G X Y Z = ancestral G X Y I := by
  funext v
  apply propext
  refine ⟨?_, ancestral_mono required v⟩
  rintro ⟨w, (hx | hy | hz), path⟩
  · exact ⟨w, .inl hx, path⟩
  · exact ⟨w, .inr (.inl hy), path⟩
  · obtain ⟨z, seed, suffix⟩ := within w hz
    exact ⟨z, seed, ancestor_trans path suffix⟩

noncomputable def query (G : DAG n) (X Y Z : Fin n → Prop) : Query G := by
  classical
  exact ⟨fun x => decide (X x), fun x => decide (Y x), Conditioning.ofPredicate G (fun x => decide (Z x))⟩

private theorem query_left (v : Fin n) : (query G X Y Z).left v = true ↔ X v := by
  classical
  simp [query]

private theorem query_right (v : Fin n) : (query G X Y Z).right v = true ↔ Y v := by
  classical
  simp [query]

private theorem query_outside (v : Fin n) :
    (query G X Y Z).condition.member v = false ↔ ¬ Z v := by
  classical
  simp [query, Conditioning.ofPredicate]

private theorem query_ancestral (v : Fin n) :
    (query G X Y Z).relevant v ↔ ancestral G X Y Z v := by
  classical
  rw [Query.relevant_iff]
  simp [query, Conditioning.ofPredicate, ancestral]

private theorem query_moralWalk_snoc {Q : Query G} {u v w : Fin n}
    (before : Q.MoralWalk u v) (last : Q.MoralEdge v w) : Q.MoralWalk u w := by
  induction before with
  | nil _ => exact .cons last (.nil _)
  | cons first _ ih => exact .cons first (ih last)

private theorem query_route_to_reach {u v : Fin n} (walk : (query G X Y Z).MoralWalk u v)
    (initial : Reach (moralEdge G (ancestral G X Y Z)) X Z u) :
    Reach (moralEdge G (ancestral G X Y Z)) X Z v := by
  induction walk with
  | nil _ => exact initial
  | @cons s t _ h _ ih =>
    have next : moralEdge G (ancestral G X Y Z) s t := by
      refine ⟨(query_ancestral _).mp h.sourceRelevant, (query_ancestral _).mp h.targetRelevant,
        h.distinct, ?_⟩
      rcases h.connection with fwd | bwd | ⟨c, hc, fwd, bwd⟩
      · exact .inl fwd
      · exact .inr (.inl bwd)
      · exact .inr (.inr ⟨c, (query_ancestral _).mp hc, fwd, bwd⟩)
    exact ih (.step initial ((query_outside _).mp h.sourceOutside) next)

private theorem query_reach_to_route {v : Fin n}
    (reach : Reach (moralEdge G (ancestral G X Y Z)) X Z v) (outside : ¬ Z v) :
    ∃ source, X source ∧ (query G X Y Z).MoralWalk source v := by
  induction reach with
  | seed hx => exact ⟨_, hx, .nil _⟩
  | step _ openVertex edge ih =>
    obtain ⟨source, hx, path⟩ := ih openVertex
    obtain ⟨hu, hv, hne, adj⟩ := edge
    refine ⟨source, hx, query_moralWalk_snoc path
      ⟨(query_ancestral _).mpr hu, (query_ancestral _).mpr hv,
        (query_outside _).mpr openVertex, (query_outside _).mpr outside, hne, ?_⟩⟩
    rcases adj with fwd | bwd | ⟨c, hc, fwd, bwd⟩
    · exact .inl fwd
    · exact .inr (.inl bwd)
    · exact .inr (.inr ⟨c, (query_ancestral _).mpr hc, fwd, bwd⟩)

/-- D-separation of the two endpoint sets as defined in the DAG foundation. -/
def DSeparated (G : DAG n) (X Y Z : Fin n → Prop) : Prop :=
  ¬ (query G X Y Z).DConnection

private theorem dSeparated_iff_separated (leftOutside : ∀ v, X v → ¬ Z v)
    (rightOutside : ∀ v, Y v → ¬ Z v) :
    DSeparated G X Y Z ↔ Separated (moralEdge G (ancestral G X Y Z)) X Y Z := by
  have moral := (query G X Y Z).dSeparation_iff_no_moralConnection
    (fun v h => (query_outside v).mpr (leftOutside v ((query_left v).mp h)))
    (fun v h => (query_outside v).mpr (rightOutside v ((query_right v).mp h)))
  refine moral.trans ⟨?_, ?_⟩
  · intro separated v hy reach
    obtain ⟨source, hx, walk⟩ := query_reach_to_route reach (rightOutside v hy)
    exact separated ⟨source, v, (query_left _).mpr hx, (query_right _).mpr hy, walk⟩
  · rintro separated ⟨u, v, hx, hy, walk⟩
    exact separated v ((query_right _).mp hy)
      (query_route_to_reach walk (.seed ((query_left _).mp hx)))

private theorem moral_edge_mono {A B : Fin n → Prop} (sub : ∀ v, A v → B v)
    (u v : Fin n) (h : moralEdge G A u v) : moralEdge G B u v := by
  obtain ⟨hu, hv, different, forward | backward | ⟨c, hc, first, last⟩⟩ := h
  · exact ⟨sub u hu, sub v hv, different, .inl forward⟩
  · exact ⟨sub u hu, sub v hv, different, .inr (.inl backward)⟩
  · exact ⟨sub u hu, sub v hv, different, .inr (.inr ⟨c, sub c hc, first, last⟩)⟩

private theorem clamp_reach {v : Fin n} (required : ∀ x, I x → Z x)
    (reach : Reach (moralEdge G (ancestral G X Y I)) X
      (fun x => Z x ∧ ancestral G X Y I x) v) :
    Reach (moralEdge G (ancestral G X Y Z)) X Z v := by
  induction reach with
  | seed hx => exact .seed hx
  | step _ openVertex next ih =>
    exact .step ih (fun hz => openVertex ⟨hz, next.1⟩)
      (moral_edge_mono (ancestral_mono required) _ _ next)

/-- The required vertices are included and the remaining vertices are allowed by R. -/
def IsSeparator (G : DAG n) (X Y I R Z : Fin n → Prop) : Prop :=
  (∀ v, I v → Z v) ∧ (∀ v, Z v → R v) ∧ DSeparated G X Y Z

/-- Inclusion minimality among separators containing the required vertices. -/
def IsMinimalSeparator (G : DAG n) (X Y I R Z : Fin n → Prop) : Prop :=
  IsSeparator G X Y I R Z ∧
    ∀ W, IsSeparator G X Y I R W → (∀ v, W v → Z v) → ∀ v, Z v → W v

def initial (G : DAG n) (X Y I R : Fin n → Prop) (v : Fin n) : Prop :=
  R v ∧ ancestral G X Y I v ∧ ¬ X v ∧ ¬ Y v

def keepDagReached (G : DAG n) (A X I Z : Fin n → Prop) (v : Fin n) : Prop :=
  (Z v ∧ DagReach G A X Z v) ∨ I v

private theorem keep_dag_eq_keep_moral (seeds : ∀ v, X v → A v) :
    keepDagReached G A X I Z = keepReached (moralEdge G A) X I Z := by
  funext v
  apply propext
  simp only [keepDagReached, keepReached, dag_reach_iff_moral_reach seeds v]

/-- The set-valued procedure in §3. Reachability uses only the DAG edges
and the Figure 3 transition, with the final vertex permitted to be blocked. -/
noncomputable def findMinSepInDAG (G : DAG n) (X Y I R : Fin n → Prop) :
    Option (Fin n → Prop) := by
  classical
  let A := ancestral G X Y I
  let Z₀ := initial G X Y I R
  exact if ∃ v, Y v ∧ DagReach G A X Z₀ v then none
    else some (keepDagReached G A Y I (keepDagReached G A X I Z₀))

/-- If the DAG procedure returns a set, it is an inclusion-minimal
d-separator satisfying the required and allowed vertex restrictions. If
it returns no set, no separator meeting those restrictions exists. -/
theorem find_min_sep_in_dag_correct
    (requiredAllowed : ∀ v, I v → R v)
    (allowedLeft : ∀ v, R v → ¬ X v)
    (allowedRight : ∀ v, R v → ¬ Y v) :
    match findMinSepInDAG G X Y I R with
    | none => ¬ ∃ Z, IsSeparator G X Y I R Z
    | some Z => IsMinimalSeparator G X Y I R Z := by
  classical
  let A := ancestral G X Y I
  let Z₀ := initial G X Y I R
  let edge := moralEdge G A
  have seedsLeft : ∀ v, X v → A v := fun v h => ⟨v, .inl h, .inl rfl⟩
  have seedsRight : ∀ v, Y v → A v := fun v h => ⟨v, .inr (.inl h), .inl rfl⟩
  have requiredInitial : ∀ v, I v → Z₀ v := fun v h =>
    ⟨requiredAllowed v h, ⟨v, .inr (.inr h), .inl rfl⟩,
      allowedLeft v (requiredAllowed v h), allowedRight v (requiredAllowed v h)⟩
  have seedsOutsideLeft : ∀ v, X v → ¬ Z₀ v := fun _ hx h => h.2.2.1 hx
  have seedsOutsideRight : ∀ v, Y v → ¬ Z₀ v := fun _ hy h => h.2.2.2 hy
  by_cases connected : ∃ v, Y v ∧ DagReach G (ancestral G X Y I) X (initial G X Y I R) v
  · simp only [findMinSepInDAG, ite_eq_left connected]
    rintro ⟨Z, required, allowed, separated⟩
    obtain ⟨v, hv, route⟩ := connected
    have baseline := (dag_reach_iff_moral_reach seedsLeft v).mp route
    have clamped : Reach edge X (fun x => Z x ∧ A x) v := by
      exact baseline.map (fun _ h => .seed h) (fun _ _ h => h)
        (fun x h => ⟨allowed x h.1, h.2, allowedLeft x (allowed x h.1), allowedRight x (allowed x h.1)⟩)
    exact (dSeparated_iff_separated (fun x hx hz => allowedLeft x (allowed x hz) hx)
      (fun x hy hz => allowedRight x (allowed x hz) hy)).mp separated v hv (clamp_reach required clamped)
  · simp only [findMinSepInDAG, ite_eq_right connected]
    have baselineSep : Separated edge X Y Z₀ := fun v h route =>
      connected ⟨v, h, (dag_reach_iff_moral_reach seedsLeft v).mpr route⟩
    rw [keep_dag_eq_keep_moral seedsLeft, keep_dag_eq_keep_moral seedsRight]
    let result := keepReached edge Y I (keepReached edge X I Z₀)
    have ⟨separated, required, within, necessary⟩ :=
      separating_prune (moral_symmetric G A) requiredInitial seedsOutsideLeft seedsOutsideRight baselineSep
    have resultWithin : ∀ v, result v → A v := fun v h => (within v h).2.1
    have resultAllowed : ∀ v, result v → R v := fun v h => (within v h).1
    have transfer {W : Fin n → Prop} (rw : ∀ v, I v → W v) (aw : ∀ v, W v → R v)
        (zw : ∀ v, W v → A v) : DSeparated G X Y W ↔ Separated edge X Y W := by
      simpa only [edge, A, ancestral_eq rw zw] using
        (dSeparated_iff_separated (G := G) (fun v hx hw => allowedLeft v (aw v hw) hx)
          (fun v hy hw => allowedRight v (aw v hw) hy))
    refine ⟨⟨required, resultAllowed, (transfer required resultAllowed resultWithin).mpr separated⟩, ?_⟩
    rintro W ⟨requiredW, allowedW, separatedW⟩ subset v chosen
    by_cases mandatory : I v
    · exact requiredW v mandatory
    by_cases present : W v
    · exact present
    · obtain ⟨left, right⟩ := necessary v chosen mandatory
      exact (necessary_blocker (moral_symmetric G A) left right subset present
        ((transfer requiredW allowedW (fun w h => resultWithin w (subset w h))).mp separatedW)).elim

def nextStates (G : DAG n) (A Z : Fin n → Bool) (before : State (Fin n)) :
    List (State (Fin n)) :=
  (allStates n).filter fun after =>
    let edge := match after.2 with
      | .up => G.edge after.1 before.1
      | .down => G.edge before.1 after.1
    A after.1 && edge && ((before.2 == .down && after.2 == .up) || !Z before.1)

private theorem mem_all_states (state : State (Fin n)) : state ∈ allStates n := by
  rcases state with ⟨v, _ | _⟩ <;> simp [allStates]

private theorem mem_next_states_iff (G : DAG n) (A Z : Fin n → Bool) (s t : State (Fin n)) :
    t ∈ nextStates G A Z s ↔ Pass G (fun v => A v = true) (fun v => Z v = true) s t := by
  rcases s with ⟨u, _ | _⟩ <;> rcases t with ⟨v, _ | _⟩ <;>
    simp [nextStates, Pass, Move, mem_all_states, and_assoc]

def visitedStates (G : DAG n) (A X Z : Fin n → Bool) : List (State (Fin n)) :=
  explore (nextStates G A Z) (allStates n)
    (((List.finRange n).filter fun v => A v && X v).map (·, .up))

private theorem mem_visited_states_iff (G : DAG n) (A X Z : Fin n → Bool)
    (state : State (Fin n)) :
    state ∈ visitedStates G A X Z ↔
      ReachState G (fun v => A v = true) (fun v => X v = true) (fun v => Z v = true) state := by
  constructor
  · intro found
    refine explore_sound (P := ReachState G (fun v => A v = true)
      (fun v => X v = true) (fun v => Z v = true)) ?_ ?_ found
    · intro s t reached step
      exact .step reached ((mem_next_states_iff G A Z s t).mp step)
    · intro s start
      obtain ⟨v, candidate, rfl⟩ := List.mem_map.mp start
      obtain ⟨hv, hx⟩ := Bool.and_eq_true_iff.mp (List.mem_filter.mp candidate).2
      exact .seed hv hx
  · intro reach
    induction reach with
    | seed hv hx =>
      exact explore_covers (mem_all_states _)
        (List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨List.mem_finRange _, Bool.and_eq_true_iff.mpr ⟨hv, hx⟩⟩, rfl⟩)
    | step _ pass ih =>
      exact explore_closed ih ((mem_next_states_iff G A Z _ _).mpr pass) (mem_all_states _)

def reachable (G : DAG n) (A X Z : Fin n → Bool) : Fin n → Bool :=
  let visited := visitedStates G A X Z
  fun v => visited.any fun s => s.1 == v

/-- The computed vertex set is exactly the Figure 3 arrival-state reachability
relation, including arrivals that cannot continue through a blocked vertex. -/
theorem reachable_iff (G : DAG n) (A X Z : Fin n → Bool) (v : Fin n) :
    reachable G A X Z v = true ↔
      DagReach G (fun v => A v = true) (fun v => X v = true) (fun v => Z v = true) v := by
  rw [reachable, List.any_eq_true]
  constructor
  · rintro ⟨⟨w, arrival⟩, found, same⟩
    change (w == v) = true at same
    have eq : w = v := eq_of_beq same
    subst w
    exact ⟨arrival, (mem_visited_states_iff G A X Z _).mp found⟩
  · rintro ⟨arrival, p⟩
    exact ⟨(v, arrival), (mem_visited_states_iff G A X Z _).mpr p, by simp⟩

def ancestralBool (G : DAG n) (X Y I : Fin n → Bool) (u : Fin n) : Bool :=
  (List.finRange n).any fun v => (X v || Y v || I v) && ((u == v) || hasDirectedWalk G u v)

private theorem ancestral_bool_iff (G : DAG n) (X Y I : Fin n → Bool) (v : Fin n) :
    ancestralBool G X Y I v = true ↔
      ancestral G (fun v => X v = true) (fun v => Y v = true) (fun v => I v = true) v := by
  simp [ancestralBool, ancestral, Ancestor, List.any_eq_true, hasDirectedWalk_iff, or_assoc]

def keepReachedBool (I Z reached : Fin n → Bool) (v : Fin n) : Bool :=
  (Z v && reached v) || I v

private theorem keep_reached_bool_iff (G : DAG n) (A X I Z : Fin n → Bool) (v : Fin n) :
    keepReachedBool I Z (reachable G A X Z) v = true ↔ keepDagReached G
      (fun v => A v = true) (fun v => X v = true) (fun v => I v = true) (fun v => Z v = true) v := by
  simp [keepReachedBool, keepDagReached, reachable_iff]

/-- Finite implementation of the DAG procedure with Boolean set membership.
The list worklist is used for correctness, with no linear-time bound asserted. -/
def findMinSep (G : DAG n) (X Y I R : Fin n → Bool) : Option (Fin n → Bool) :=
  let A := ancestralBool G X Y I
  let Z₀ := fun u => R u && A u && !X u && !Y u
  let fromLeft := reachable G A X Z₀
  if (List.finRange n).any (fun v => Y v && fromLeft v) then none
  else
    let Zₓ := keepReachedBool I Z₀ fromLeft
    let fromRight := reachable G A Y Zₓ
    some (keepReachedBool I Zₓ fromRight)

/-- The executable procedure returns exactly the option and set described in §3. -/
theorem find_min_sep_refines_spec (G : DAG n) (X Y I R : Fin n → Bool) :
    (findMinSep G X Y I R).map (fun z v => z v = true) =
      findMinSepInDAG G (fun v => X v = true) (fun v => Y v = true)
        (fun v => I v = true) (fun v => R v = true) := by
  classical
  unfold findMinSep findMinSepInDAG
  dsimp only
  have scope : (fun v => ancestralBool G X Y I v = true) =
      ancestral G (fun v => X v = true) (fun v => Y v = true) (fun v => I v = true) :=
    funext fun v => propext (ancestral_bool_iff G X Y I v)
  have z₀ : (fun v => (R v && ancestralBool G X Y I v && !X v && !Y v) = true) =
      initial G (fun v => X v = true) (fun v => Y v = true)
        (fun v => I v = true) (fun v => R v = true) := by
    funext v
    apply propext
    simp [initial, ancestral_bool_iff, and_assoc]
  have test : (List.finRange n).any
      (fun v => Y v && reachable G (ancestralBool G X Y I) X
        (fun v => R v && ancestralBool G X Y I v && !X v && !Y v) v) = true ↔
      ∃ v, Y v = true ∧ DagReach G
        (ancestral G (fun v => X v = true) (fun v => Y v = true) (fun v => I v = true))
        (fun v => X v = true)
        (initial G (fun v => X v = true) (fun v => Y v = true)
          (fun v => I v = true) (fun v => R v = true)) v := by
    rw [← scope, ← z₀]
    simp [List.any_eq_true, reachable_iff]
  split
  next yes => rw [ite_eq_left (test.mp yes)]; rfl
  next no =>
    rw [ite_eq_right (fun h => no (test.mpr h))]
    simp only [Option.map_some, Option.some.injEq]
    have keep (S Z : Fin n → Bool) :
        (fun v => keepReachedBool I Z (reachable G (ancestralBool G X Y I) S Z) v = true) =
        keepDagReached G
          (ancestral G (fun v => X v = true) (fun v => Y v = true) (fun v => I v = true))
          (fun v => S v = true) (fun v => I v = true) (fun v => Z v = true) := by
      exact (funext fun v => propext (keep_reached_bool_iff G _ S I Z v)).trans
        (by rw [scope])
    rw [keep, keep, z₀]

/-- The finite implementation succeeds exactly when a permitted d-separator
exists, returning a separator inclusion-minimal relative to `I`. -/
theorem find_min_sep_correct (G : DAG n) (X Y I R : Fin n → Bool)
    (requiredAllowed : ∀ v, I v = true → R v = true)
    (allowedLeft : ∀ v, R v = true → X v ≠ true)
    (allowedRight : ∀ v, R v = true → Y v ≠ true) :
    match findMinSep G X Y I R with
    | none => ¬ ∃ Z, IsSeparator G (fun v => X v = true) (fun v => Y v = true)
        (fun v => I v = true) (fun v => R v = true) Z
    | some Z => IsMinimalSeparator G (fun v => X v = true) (fun v => Y v = true)
        (fun v => I v = true) (fun v => R v = true) (fun v => Z v = true) := by
  have correct := find_min_sep_in_dag_correct (G := G) requiredAllowed allowedLeft allowedRight
  rw [← find_min_sep_refines_spec G X Y I R] at correct
  cases h : findMinSep G X Y I R with
  | none => simpa only [h, Option.map_none] using correct
  | some Z => simpa only [h, Option.map_some] using correct

end

end OpenCausalScience.Papers.VanDerZanderLiskiewicz2020.FindMinSepInDAG
