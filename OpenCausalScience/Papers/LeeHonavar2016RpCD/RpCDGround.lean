module
public import OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

@[expose] public section

namespace RpCD.Ground

open OpenCausalScience
open OpenCausalScience.Papers.KimEtAl2026.BayesBallCorrectness
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

/-- A query is based at `target`, and follows a path to `source`. -/
structure Dependency (A P : Type) where
  source : A
  target : A
  path : P
  deriving DecidableEq

structure Schema (A P S : Type) where
  size : S → Nat
  attributeOf : (s : S) → Fin (size s) → A
  realizes : (s : S) → Dependency A P → Fin (size s) → Fin (size s) → Bool
  types : ∀ s q x z, realizes s q x z = true →
    attributeOf s x = q.target ∧ attributeOf s z = q.source

structure Model (A P : Type) where
  dependencies : List (Dependency A P)
  rank : A → Nat
  acyclic : ∀ d ∈ dependencies, rank d.source < rank d.target

variable {A P S : Type}

def groundEdge (B : Schema A P S) (M : Model A P) (s : S)
    (u v : Fin (B.size s)) : Bool :=
  M.dependencies.any fun q => B.realizes s q v u

theorem groundEdge_rank (B : Schema A P S) (M : Model A P) (s : S)
    (u v : Fin (B.size s)) (edge : groundEdge B M s u v = true) :
    M.rank (B.attributeOf s u) < M.rank (B.attributeOf s v) := by
  obtain ⟨q, member, hit⟩ := List.any_eq_true.mp edge
  obtain ⟨target, source⟩ := B.types s q v u hit
  simpa [target, source] using M.acyclic q member

def graph (B : Schema A P S) (M : Model A P) (s : S) : DAG (B.size s) where
  edge := groundEdge B M s
  rank := fun v => M.rank (B.attributeOf s v)
  edge_increases := groundEdge_rank B M s

def condition (B : Schema A P S) (s : S) (x : Fin (B.size s))
    (selected : List (Dependency A P)) (z : Fin (B.size s)) : Bool :=
  selected.any fun q => B.realizes s q x z

/-- A conditioned endpoint does not contribute to a ground CI violation. -/
def RelCI (B : Schema A P S) (M : Model A P) (q : Dependency A P)
    (selected : List (Dependency A P)) : Prop :=
  ∀ s x z, B.realizes s q x z = true →
    ¬ DConnected (Conditioning.ofPredicate (graph B M s) (condition B s x selected)) x z

def parents [DecidableEq A] (M : Model A P) (x : A) : List (Dependency A P) :=
  M.dependencies.filter fun q => q.target == x

theorem condition_parents [DecidableEq A] (B : Schema A P S) (M : Model A P)
    (s : S) (x z : Fin (B.size s)) :
    condition B s x (parents M (B.attributeOf s x)) z = (graph B M s).edge z x := by
  apply Bool.eq_iff_iff.mpr
  simp only [condition, parents, graph, groundEdge, List.any_eq_true, List.mem_filter]
  constructor
  · rintro ⟨q, ⟨member, _⟩, hit⟩
    exact ⟨q, member, hit⟩
  · rintro ⟨q, member, hit⟩
    exact ⟨q, ⟨member, by simp [(B.types s q x z hit).1]⟩, hit⟩

theorem parents_separate_of_distinct [DecidableEq A] (B : Schema A P S) (M : Model A P)
    {q : Dependency A P} (different : ∀ s x z, B.realizes s q x z = true → x ≠ z)
    (noDescendant : M.rank q.source ≤ M.rank q.target) :
    RelCI B M q (parents M q.target) := by
  intro s x z hit connection
  let G := graph B M s
  obtain ⟨target, source⟩ := B.types s q x z hit
  have identifies : condition B s x (parents M q.target) = (fun v => G.edge v x) := by
    funext v
    rw [← target, condition_parents]
  rw [identifies] at connection
  change DConnected (parentCondition G x) x z at connection
  have distinct := different s x z hit
  have notParent : G.edge z x ≠ true := by
    have outside : G.edge z x = false := connection.2.1
    simp [outside]
  have notDesc : ¬ G.DirectedWalk x z := by
    intro desc
    have later := G.rank_lt_of_directedWalk desc
    change M.rank (B.attributeOf s x) < M.rank (B.attributeOf s z) at later
    exact Nat.not_lt_of_ge noDescendant (by simpa [target, source] using later)
  exact parents_dSeparate distinct notParent notDesc connection

theorem parents_separate [DecidableEq A] (B : Schema A P S) (M : Model A P)
    {q : Dependency A P} (different : q.target ≠ q.source)
    (noDescendant : M.rank q.source ≤ M.rank q.target) :
    RelCI B M q (parents M q.target) :=
  parents_separate_of_distinct B M
    (fun s x z hit same => by
      obtain ⟨target, source⟩ := B.types s q x z hit
      exact different (target.symm.trans ((congrArg (B.attributeOf s) same).trans source)))
    noDescendant

/-- A dependency realized by an isolated path defeats every separator
omitting that path and consisting of other candidates. -/
theorem adjacent_not_separated (B : Schema A P S) (M : Model A P)
    {q d : Dependency A P} (trueDependency : d ∈ M.dependencies)
    {s : S} {x z : Fin (B.size s)} (query : B.realizes s q x z = true)
    (generated : B.realizes s d x z = true ∨ B.realizes s d z x = true)
    (selected : List (Dependency A P))
    (excludesBase : ∀ p ∈ selected, B.realizes s p x x = false)
    (excludesOther : ∀ p ∈ selected, B.realizes s p x z = false) :
    ¬ RelCI B M q selected := by
  intro separated
  apply separated s x z query
  apply adjacent_dConnected
  · rcases generated with incoming | outgoing
    · exact .inr (List.any_eq_true.mpr ⟨d, trueDependency, incoming⟩)
    · exact .inl (List.any_eq_true.mpr ⟨d, trueDependency, outgoing⟩)
  · exact Bool.eq_false_iff.mpr fun inside => by
      obtain ⟨p, member, realized⟩ := List.any_eq_true.mp inside
      simp [excludesBase p member] at realized
  · exact Bool.eq_false_iff.mpr fun inside => by
      obtain ⟨p, member, realized⟩ := List.any_eq_true.mp inside
      simp [excludesOther p member] at realized

structure CUT (B : Schema A P S) (M : Model A P) (q : Dependency A P) where
  skeleton : S
  base : Fin (B.size skeleton)
  middle : Fin (B.size skeleton)
  other : Fin (B.size skeleton)
  query : B.realizes skeleton q base other = true
  distinct : base ≠ other
  first : Adjacent (graph B M skeleton) base middle
  second : Adjacent (graph B M skeleton) other middle
  unshielded : ¬ Adjacent (graph B M skeleton) base other

/-- The separator checks actual middle membership in the same CUT witness. -/
theorem cut_collider_iff (B : Schema A P S) (M : Model A P)
    {q : Dependency A P} (w : CUT B M q) {selected : List (Dependency A P)}
    (xOutside : condition B w.skeleton w.base selected w.base = false)
    (zOutside : condition B w.skeleton w.base selected w.other = false)
    (separates : RelCI B M q selected) :
    condition B w.skeleton w.base selected w.middle = false ↔
      HeadToHead (graph B M w.skeleton) w.base w.middle w.other :=
  middle_omitted_iff_headToHead_of_separating _ w.first w.second w.distinct
    xOutside zOutside (separates _ _ _ w.query)

/-- Instantiating a surviving adjacency cannot select the opposite endpoint
of a CUT, even when its declared endpoint class equals the base class. -/
theorem cut_collider_by_neighbors (B : Schema A P S) (M : Model A P)
    {q : Dependency A P} (w : CUT B M q) {selected : List (Dependency A P)}
    (neighbors : ∀ p ∈ selected, ∀ z, B.realizes w.skeleton p w.base z = true →
      Adjacent (graph B M w.skeleton) w.base z)
    (separates : RelCI B M q selected) :
    condition B w.skeleton w.base selected w.middle = false ↔
      HeadToHead (graph B M w.skeleton) w.base w.middle w.other := by
  apply cut_collider_iff B M w ?_ ?_ separates
  all_goals
    apply Bool.eq_false_iff.mpr
    intro hit
    obtain ⟨p, member, realized⟩ := List.any_eq_true.mp hit
  · rcases neighbors p member w.base realized with self | self <;>
      exact (graph B M w.skeleton).no_directed_cycle w.base (.single self)
  · exact w.unshielded (neighbors p member w.other realized)

end RpCD.Ground

end
