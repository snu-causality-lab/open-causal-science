module
public import OpenCausalScience.Graph.DAG

/-! # Grow–shrink trees

Andrews et al. (NeurIPS 2023), Section 3. An eager reference tree caches
ranked improving branches and the shrink result at each node. The
comparison uses the same fixed score and tie order for an uncached run.
-/

namespace OpenCausalScience.Papers.AndrewsEtAl2023.GrowShrinkTree

@[expose] public section

variable {n : Nat}

abbrev LocalScore (n : Nat) := List (Fin n) → Rat

/-- Order higher-scoring candidates first and break ties by the vertex label. -/
def preferred (weight : Fin n → Rat) (a b : Fin n) : Prop :=
  weight b ≤ weight a ∧ (weight a = weight b → a.val ≤ b.val)

instance (weight : Fin n → Rat) (a b : Fin n) : Decidable (preferred weight a b) :=
  inferInstanceAs (Decidable (_ ∧ (_ → _)))

private theorem preferred_trans (weight : Fin n → Rat) (a b c : Fin n)
    (ab : preferred weight a b) (bc : preferred weight b c) : preferred weight a c := by
  refine ⟨Rat.le_trans bc.1 ab.1, ?_⟩
  intro equal
  have aBelowB : weight a ≤ weight b := by rw [equal]; exact bc.1
  have eqAB := Rat.le_antisymm aBelowB ab.1
  exact Nat.le_trans (ab.2 eqAB) (bc.2 (eqAB.symm.trans equal))

private theorem preferred_total (weight : Fin n → Rat) (a b : Fin n) :
    preferred weight a b ∨ preferred weight b a := by
  by_cases same : weight a = weight b
  · rcases Nat.le_total a.val b.val with aFirst | bFirst
    · exact Or.inl ⟨same.symm ▸ Rat.le_refl, fun _ => aFirst⟩
    · exact Or.inr ⟨same ▸ Rat.le_refl, fun _ => bFirst⟩
  · rcases (Rat.le_total : weight b ≤ weight a ∨ weight a ≤ weight b) with aHigher | bHigher
    · exact Or.inl ⟨aHigher, fun equal => False.elim (same equal)⟩
    · exact Or.inr ⟨bHigher, fun equal => False.elim (same equal.symm)⟩

private theorem preferred_antisymm (weight : Fin n → Rat) (a b : Fin n)
    (ab : preferred weight a b) (ba : preferred weight b a) : a = b := by
  have scoreEq := Rat.le_antisymm ba.1 ab.1
  exact Fin.ext (Nat.le_antisymm (ab.2 scoreEq) (ba.2 scoreEq.symm))

/-- Rank exactly the strict improvements over the incumbent. -/
def rankedImprovements (weight : Fin n → Rat) (baseline : Rat) (pool : List (Fin n)) :
    List (Fin n) :=
  (pool.filter (fun v => decide (baseline < weight v))).mergeSort
    (fun a b => decide (preferred weight a b))

theorem mem_ranked_improvements {weight : Fin n → Rat} {baseline : Rat}
    {pool : List (Fin n)} {v : Fin n} :
    v ∈ rankedImprovements weight baseline pool ↔ v ∈ pool ∧ baseline < weight v := by
  unfold rankedImprovements
  rw [(List.mergeSort_perm _ _).mem_iff, List.mem_filter]
  simp

private theorem mem_of_head_some {xs : List (Fin n)} {v : Fin n} (head : xs.head? = some v) :
    v ∈ xs := by
  obtain ⟨tail, rfl⟩ := List.head?_eq_some_iff.mp head
  exact List.mem_cons_self

theorem ranked_improvements_filter (weight : Fin n → Rat) (baseline : Rat)
    (pool : List (Fin n)) (eligible : Fin n → Bool) :
    (rankedImprovements weight baseline pool).filter eligible =
      rankedImprovements weight baseline (pool.filter eligible) := by
  let positive := fun v => decide (baseline < weight v)
  let precedes := fun a b => decide (preferred weight a b)
  have sorted (ys : List (Fin n)) :
      (ys.mergeSort precedes).Pairwise (fun a b => precedes a b = true) :=
    List.pairwise_mergeSort
      (fun a b c ab bc => decide_eq_true (preferred_trans weight a b c
        (of_decide_eq_true ab) (of_decide_eq_true bc)))
      (fun a b => by
        rcases preferred_total weight a b with first | second
        · simp [first]
        · simp [second])
      ys
  have samePool : (pool.filter positive).filter eligible = (pool.filter eligible).filter positive := by
    simp only [List.filter_filter, Bool.and_comm]
  have sameOrder : ((pool.filter positive).mergeSort precedes).filter eligible |>.Perm
      (((pool.filter eligible).filter positive).mergeSort precedes) := by
    have left := (List.mergeSort_perm (pool.filter positive) precedes).filter eligible
    rw [samePool] at left
    exact left.trans (List.mergeSort_perm _ _).symm
  exact List.Perm.eq_of_pairwise
    (fun a b _ _ ab ba => preferred_antisymm weight a b (of_decide_eq_true ab) (of_decide_eq_true ba))
    ((sorted (pool.filter positive)).filter eligible)
    (sorted ((pool.filter eligible).filter positive)) sameOrder

/-- The grow ranking depends on the current parents and the whole remaining pool. -/
def growBranches (score : LocalScore n) (pool parents : List (Fin n)) : List (Fin n) :=
  rankedImprovements (fun v => score (v :: parents)) (score parents) pool

/-- Recompute the grow choice using only the eligible predecessors. -/
def uncachedNext (score : LocalScore n) (eligible : Fin n → Bool) (pool parents : List (Fin n)) :
    Option (Fin n) :=
  (growBranches score (pool.filter eligible) parents).head?

theorem cached_next_eq_uncached_next (score : LocalScore n) (eligible : Fin n → Bool)
    (pool parents : List (Fin n)) :
    (growBranches score pool parents).find? eligible = uncachedNext score eligible pool parents := by
  rw [← List.head?_filter, growBranches, ranked_improvements_filter]
  rfl

private theorem uncached_next_mem {score : LocalScore n} {eligible : Fin n → Bool}
    {pool parents : List (Fin n)} {v : Fin n}
    (found : uncachedNext score eligible pool parents = some v) :
    v ∈ pool ∧ eligible v = true := by
  have appears := mem_of_head_some found
  exact List.mem_filter.mp (mem_ranked_improvements.mp appears).1

def nextRemoval (score : LocalScore n) (parents : List (Fin n)) : Option (Fin n) :=
  (rankedImprovements (fun v => score (parents.erase v)) (score parents) parents).head?

/-- Greedy removal with a strict score increase, as in Algorithm 2. -/
def shrink (score : LocalScore n) : Nat → List (Fin n) → List (Fin n)
  | 0, parents => parents
  | budget + 1, parents =>
      match nextRemoval score parents with
      | none => parents
      | some v => shrink score budget (parents.erase v)

theorem shrink_properties (score : LocalScore n) (budget : Nat) (parents : List (Fin n))
    (enough : parents.length ≤ budget) :
    let selected := shrink score budget parents
    selected ⊆ parents ∧ score parents ≤ score selected ∧
      ∀ v ∈ selected, score (selected.erase v) ≤ score selected := by
  induction budget generalizing parents with
  | zero =>
      cases parents with
      | nil => simp [shrink, List.Subset.refl]
      | cons v tail => simp at enough
  | succ budget ih =>
      cases found : nextRemoval score parents with
      | none =>
          have empty : rankedImprovements (fun v => score (parents.erase v)) (score parents) parents = [] := by
            simpa only [nextRemoval, List.head?_eq_none_iff] using found
          simp only [shrink, found]
          refine ⟨List.Subset.refl _, Rat.le_refl, ?_⟩
          intro v present
          exact Rat.not_lt.mp fun improves => by
            have inRanking : v ∈ rankedImprovements
                (fun v => score (parents.erase v)) (score parents) parents :=
              mem_ranked_improvements.mpr ⟨present, improves⟩
            rw [empty] at inRanking
            exact List.not_mem_nil inRanking
      | some v =>
          have ⟨present, gain⟩ := mem_ranked_improvements.mp (mem_of_head_some found)
          have smaller : (parents.erase v).length ≤ budget := by
            rw [List.length_erase_of_mem present]
            omega
          obtain ⟨subset, higher, optimum⟩ := ih (parents.erase v) smaller
          simp only [shrink, found]
          exact ⟨subset.trans List.erase_subset, Rat.le_trans (Rat.le_of_lt gain) higher, optimum⟩

structure Result (n : Nat) where
  parents : List (Fin n)
  score : Rat
deriving DecidableEq

def finish (score : LocalScore n) (parents : List (Fin n)) : Result n :=
  let selected := shrink score parents.length parents
  ⟨selected, score selected⟩

inductive Tree (n : Nat) where
  | node (result : Result n) (branches : List (Fin n × Tree n))

/-- Eager finite reference for the nodes that Section 3 builds on demand. -/
def build (score : LocalScore n) : Nat → List (Fin n) → List (Fin n) → Tree n
  | 0, _, parents => .node (finish score parents) []
  | budget + 1, pool, parents =>
      .node (finish score parents)
        ((growBranches score pool parents).map (fun v => (v, build score budget (pool.erase v) (v :: parents))))

/-- Look up the first eligible branch, returning the cached shrink result if none is available. -/
def trace (eligible : Fin n → Bool) : Nat → Tree n → Result n
  | 0, .node result _ => result
  | budget + 1, .node result branches =>
      match branches.find? (fun branch => eligible branch.1) with
      | none => result
      | some branch => trace eligible budget branch.2

/-- Algorithms 1–2 without a tree, with one vertex removed from the remaining pool per grow step. -/
def uncached (score : LocalScore n) (eligible : Fin n → Bool) :
    Nat → List (Fin n) → List (Fin n) → Result n
  | 0, _, parents => finish score parents
  | budget + 1, pool, parents =>
      match uncachedNext score eligible pool parents with
      | none => finish score parents
      | some v => uncached score eligible budget (pool.erase v) (v :: parents)

theorem trace_build_eq_uncached (score : LocalScore n) (eligible : Fin n → Bool)
    (budget : Nat) (pool parents : List (Fin n)) :
    trace eligible budget (build score budget pool parents) = uncached score eligible budget pool parents := by
  induction budget generalizing pool parents with
  | zero => rfl
  | succ budget ih =>
      simp only [build, trace, List.find?_map, Function.comp_def, cached_next_eq_uncached_next, uncached]
      cases uncachedNext score eligible pool parents with
      | none => rfl
      | some v => exact ih (pool.erase v) (v :: parents)

/-- The uncached grow–shrink algorithm, with no external budget. -/
def growShrink (score : LocalScore n) (eligible : Fin n → Bool) (pool parents : List (Fin n)) :
    Result n :=
  match _found : uncachedNext score eligible pool parents with
  | none => finish score parents
  | some v => growShrink score eligible (pool.erase v) (v :: parents)
termination_by pool.length
decreasing_by
  have present := (uncached_next_mem _found).1
  rw [List.length_erase_of_mem present]
  exact Nat.sub_lt (List.length_pos_of_mem present) (by decide)

theorem uncached_eq_grow_shrink (score : LocalScore n) (eligible : Fin n → Bool) (budget : Nat)
    (pool parents : List (Fin n)) (enough : pool.length ≤ budget) :
    uncached score eligible budget pool parents = growShrink score eligible pool parents := by
  induction budget generalizing pool parents with
  | zero =>
      cases pool with
      | nil =>
          have none : uncachedNext score eligible [] parents = none := by
            simp [uncachedNext, growBranches, rankedImprovements]
          rw [growShrink, none]
          rfl
      | cons v rest => simp at enough
  | succ budget ih =>
      rw [growShrink]
      cases found : uncachedNext score eligible pool parents with
      | none => simp only [uncached, found]
      | some v =>
          simp only [uncached, found]
          apply ih
          rw [List.length_erase_of_mem (uncached_next_mem found).1]
          omega

theorem tree_query_eq_grow_shrink (score : LocalScore n) (eligible : Fin n → Bool)
    (pool : List (Fin n)) :
    trace eligible pool.length (build score pool.length pool []) =
      growShrink score eligible pool [] :=
  (trace_build_eq_uncached score eligible pool.length pool []).trans
    (uncached_eq_grow_shrink score eligible pool.length pool [] (Nat.le_refl _))

theorem grow_shrink_respects_prefix (score : LocalScore n) (eligible : Fin n → Bool)
    (pool parents : List (Fin n)) (initial : ∀ v ∈ parents, eligible v = true) :
    ∀ v ∈ (growShrink score eligible pool parents).parents, eligible v = true := by
  rw [growShrink]
  cases found : uncachedNext score eligible pool parents with
  | none =>
      intro v present
      exact initial v ((shrink_properties score parents.length parents (Nat.le_refl _)).1 present)
  | some w =>
      apply grow_shrink_respects_prefix
      intro v present
      rcases List.mem_cons.mp present with rfl | earlier
      · exact (uncached_next_mem found).2
      · exact initial v earlier
termination_by pool.length
decreasing_by
  have present := (uncached_next_mem found).1
  rw [List.length_erase_of_mem present]
  exact Nat.sub_lt (List.length_pos_of_mem present) (by decide)


/-- A full rank input can be the position map of a permutation. -/
def precedesVertex (position : Fin n → Nat) (child parent : Fin n) : Bool :=
  decide (position parent < position child)

def projectVertex (scores : Fin n → LocalScore n) (position : Fin n → Nat) (child : Fin n) :
    Result n :=
  let pool := (List.finRange n).erase child
  trace (precedesVertex position child) pool.length (build (scores child) pool.length pool [])

theorem project_vertex_eq_uncached (scores : Fin n → LocalScore n) (position : Fin n → Nat)
    (child : Fin n) :
    projectVertex scores position child =
      growShrink (scores child) (precedesVertex position child) ((List.finRange n).erase child) [] :=
  tree_query_eq_grow_shrink (scores child) (precedesVertex position child) _

/-- Algorithm 3 constructs a DAG because every chosen parent is a predecessor. -/
def project (scores : Fin n → LocalScore n) (position : Fin n → Nat) : DAG n where
  edge := fun parent child => decide (parent ∈ (projectVertex scores position child).parents)
  rank := position
  edge_increases := by
    intro parent child included
    have present := of_decide_eq_true included
    rw [project_vertex_eq_uncached] at present
    have predecessor := grow_shrink_respects_prefix (scores child) (precedesVertex position child)
      ((List.finRange n).erase child) [] (by simp) parent present
    exact of_decide_eq_true predecessor

end
end OpenCausalScience.Papers.AndrewsEtAl2023.GrowShrinkTree
