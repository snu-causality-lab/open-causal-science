module
public import OpenCausalScience.Discovery.DAGGraphoid
public import OpenCausalScience.Discovery.OrderedMarkov
public import OpenCausalScience.Papers.AndrewsEtAl2023.OrderSearch

/-! # Population grow–shrink projection

The finite oracle argument in [Lam, Andrews and Ramsey (2022), Appendix E](https://proceedings.mlr.press/v180/lam22a/lam22a-supp.pdf#page=14),
used in the projection premise of [Andrews et al. (2023), Proposition 2](https://proceedings.neurips.cc/paper_files/paper/2023/file/c9cde817d04811ba28e44071bd9f76a5-Paper-Conference.pdf#page=6).
The score's strict local signs are hypotheses. -/

namespace OpenCausalScience.Papers.AndrewsEtAl2023.PopulationProjection

open OpenCausalScience.Probability.CI
open OpenCausalScience.Discovery
open GrowShrinkTree

@[expose] public section

variable {n : Nat}

/-- List representation of a finite variable set. -/
def maskOfList (xs : List (Fin n)) : Mask n := fun v => decide (v ∈ xs)

/-- Composition is the additional CI axiom used by the grow phase. -/
def Composition (J : Relation n) : Prop :=
  ∀ ⦃X Y W Z : Mask n⦄, Disjoint4 X Y W Z → J X Y Z → J X W Z → J X (union Y W) Z

/-- The strict gains and losses that follow from local consistency of a
score for the target. Reordering the parents does not affect the score. -/
structure LocallyConsistent (J : Relation n) (child : Fin n) (score : LocalScore n) : Prop where
  set_score {P Q : List (Fin n)} : maskOfList P = maskOfList Q → score P = score Q
  gain {v : Fin n} {P : List (Fin n)} : v ≠ child → v ∉ P → child ∉ P →
    ¬ J (single child) (single v) (maskOfList P) → score P < score (v :: P)
  loss {v : Fin n} {P : List (Fin n)} : v ≠ child → v ∉ P → child ∉ P →
    J (single child) (single v) (maskOfList P) → score (v :: P) < score P

/-- An inclusion-minimal blanket. -/
def Boundary (J : Relation n) (child : Fin n) (A P : Mask n) : Prop :=
  IsBlanket J child A P ∧ ∀ Q, Subset Q P → IsBlanket J child A Q → Q = P

private theorem mask_eq {A B : Mask n}
    (same : ∀ v, A v = true ↔ B v = true) : A = B := by
  funext v
  exact Bool.eq_iff_iff.mpr (same v)

private theorem maskOfList_cons (v : Fin n) (xs : List (Fin n)) :
    maskOfList (v :: xs) = union (single v) (maskOfList xs) := by
  apply mask_eq
  intro w
  simp [maskOfList, union, single]

private theorem maskOfList_nil : maskOfList ([] : List (Fin n)) = empty := rfl

private theorem maskOfList_subset {xs ys : List (Fin n)} (contained : xs ⊆ ys) :
    Subset (maskOfList xs) (maskOfList ys) :=
  fun _ mem => decide_eq_true (contained (of_decide_eq_true mem))

private theorem maskOfList_perm {xs ys : List (Fin n)} (p : xs.Perm ys) :
    maskOfList xs = maskOfList ys := by
  apply mask_eq
  intro w
  simpa only [maskOfList, decide_eq_true_eq] using p.mem_iff (a := w)

private theorem disjoint_single {x : Fin n} {A : Mask n} (outside : A x = false) :
    Disjoint (single x) A := by
  intro y eq
  have same : y = x := by simpa [single] using eq
  subst y
  exact outside

private theorem union_comm (A B : Mask n) : union A B = union B A := by
  funext x
  exact Bool.or_comm _ _

private theorem diff_mask_of_partition {A P R : Mask n}
    (cover : A = union P R) (apart : Disjoint P R) : diff A P = R := by
  subst A
  funext v
  cases hp : P v <;> cases hr : R v <;> simp [union, diff, hp, hr]
  have := apart v hp
  simp [hr] at this

/-- A finite set of singleton CI statements combines by repeated composition. -/
private theorem compose_list {J : Relation n} (sg : Semigraphoid J) (compose : Composition J)
    (X P : Mask n) (rest : List (Fin n)) (unique : rest.Nodup) (xz : Disjoint X P)
    (outside : ∀ v ∈ rest, X v = false ∧ P v = false)
    (independent : ∀ v ∈ rest, J X (single v) P) : J X (maskOfList rest) P := by
  induction rest with
  | nil => simpa only [maskOfList_nil] using sg.empty_right X P
  | cons v rest ih =>
    have ⟨new, uniqueTail⟩ := List.nodup_cons.mp unique
    have vOutside := outside v List.mem_cons_self
    have xRest : Disjoint X (maskOfList rest) := by
      intro w inX
      apply Bool.eq_false_iff.mpr
      intro inRest
      have noX := (outside w (List.mem_cons_of_mem _ (of_decide_eq_true inRest))).1
      simp [inX] at noX
    rw [maskOfList_cons]
    refine compose ⟨⟨(disjoint_single vOutside.1).symm, xRest,
      disjoint_single (by simp [maskOfList, new])⟩,
      xz, disjoint_single vOutside.2, ?_⟩
      (independent v List.mem_cons_self)
      (ih uniqueTail (fun x hx => outside x (List.mem_cons_of_mem _ hx))
        (fun x hx => independent x (List.mem_cons_of_mem _ hx)))
    intro w present
    exact (outside w (List.mem_cons_of_mem _ (of_decide_eq_true present))).2

/-- Composition extends singleton CI to an entire finite set of variables. -/
theorem composition_of_singletons {J : Relation n} (sg : Semigraphoid J) (compose : Composition J)
    {X Y Z : Mask n} (disjoint : Disjoint3 X Y Z)
    (independent : ∀ v, Y v = true → J X (single v) Z) : J X Y Z := by
  let rest := (List.finRange n).filter Y
  have same : Y = maskOfList rest := by
    apply mask_eq
    intro w
    simp [rest, maskOfList]
  rw [same]
  apply compose_list sg compose X Z rest ((List.nodup_finRange n).filter _) disjoint.2.1
  · intro w mem
    have selected := (List.mem_filter.mp mem).2
    exact ⟨disjoint.1.symm w selected, disjoint.2.2 w selected⟩
  · intro w mem
    exact independent w (List.mem_filter.mp mem).2

/-- If no eligible variable can improve the score, the current parents
screen the target from all remaining eligible variables (Lemma E.4). -/
theorem grow_stop_blanket {J : Relation n} (sg : Semigraphoid J) (compose : Composition J)
    {child : Fin n} {score : LocalScore n} (localScore : LocallyConsistent J child score)
    {A : Mask n} (eligible : Mask n) (pool parents : List (Fin n))
    (apart : ∀ v ∈ pool, v ∉ parents)
    (cover : A = union (maskOfList parents) (maskOfList (pool.filter eligible)))
    (childOutside : A child = false) (stopped : uncachedNext score eligible pool parents = none) :
    IsBlanket J child A (maskOfList parents) := by
  have parentsIn : Subset (maskOfList parents) A := by
    intro v hv
    simp [cover, union, hv]
  have childNotParents : child ∉ parents := by
    intro present
    have included := parentsIn child (decide_eq_true present)
    simp [childOutside] at included
  have apartMasks : Disjoint (maskOfList parents) (maskOfList (pool.filter eligible)) := by
    intro v hv
    apply Bool.eq_false_iff.mpr
    intro hv'
    exact apart v (List.mem_filter.mp (of_decide_eq_true hv')).1 (of_decide_eq_true hv)
  have rankEmpty : growBranches score (pool.filter eligible) parents = [] :=
    List.head?_eq_none_iff.mp stopped
  have independent (v : Fin n) (present : v ∈ pool.filter eligible) :
      J (single child) (single v) (maskOfList parents) := by
    apply Classical.byContradiction
    intro dep
    have ne : v ≠ child := by
      intro eq
      subst v
      simp [cover, union, maskOfList, present] at childOutside
    have gain := localScore.gain ne (apart v (List.mem_filter.mp present).1) childNotParents dep
    have ranked : v ∈ growBranches score (pool.filter eligible) parents :=
      mem_ranked_improvements.mpr ⟨present, gain⟩
    simp [rankEmpty] at ranked
  refine ⟨parentsIn, ?_⟩
  rw [diff_mask_of_partition cover apartMasks]
  apply composition_of_singletons sg compose
  · have childNotRest : child ∉ pool.filter eligible := by
      intro childPresent
      simp [cover, union, maskOfList, childPresent] at childOutside
    exact ⟨disjoint_single (by simp [maskOfList, childNotRest]),
      disjoint_single (by simp [maskOfList, childNotParents]), apartMasks.symm⟩
  · intro w mem
    exact independent w (of_decide_eq_true mem)


private theorem selected_set_split {P : List (Fin n)} {v : Fin n} (has : v ∈ P) :
    maskOfList P = union (single v) (maskOfList (P.erase v)) :=
  (maskOfList_perm (List.perm_cons_erase has)).trans (maskOfList_cons _ _)

private theorem selected_erase_nodup {P : List (Fin n)} {v : Fin n} (has : v ∈ P)
    (unique : P.Nodup) : v ∉ P.erase v ∧ (P.erase v).Nodup :=
  List.nodup_cons.mp ((List.perm_cons_erase has).nodup_iff.mp unique)

private theorem delete_disjoint {child v : Fin n} {A P : Mask n}
    (contained : Subset (union (single v) P) A) (childOutside : A child = false)
    (vOutside : P v = false) :
    Disjoint4 (single child) (single v) (diff A (union (single v) P)) P := by
  have av := contained v (by simp [single, union])
  have different : child ≠ v := by
    intro eq
    subst child
    simp [av] at childOutside
  have r : Disjoint (diff A (union (single v) P)) (union (single v) P) :=
    disjoint_diff_right _ _
  have childNotP : P child = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have included := contained child (Bool.or_eq_true_iff.mpr (.inr h))
    simp [childOutside] at included
  exact ⟨⟨disjoint_single (by simp [single, different]),
      disjoint_single (by simp [diff, childOutside]),
      (r.restrict_right (subset_union_left _ _)).symm⟩,
    disjoint_single childNotP, disjoint_single vOutside, r.restrict_right (subset_union_right _ _)⟩

private theorem union_single_and_remainder {v : Fin n} {A P : Mask n} (has : A v = true)
    (absent : P v = false) : union (single v) (diff A (union (single v) P)) = diff A P := by
  funext u
  by_cases eq : u = v
  · subst u
    simp [single, union, diff, has, absent]
  · have different : (u == v) = false := Bool.eq_false_iff.mpr (fun h => eq (beq_iff_eq.mp h))
    simp only [single, union, diff, different, Bool.false_or]

private theorem union_parent_and_remainder {v : Fin n} {A P : Mask n}
    (contained : Subset P A) (absent : P v = false) :
    union P (diff A (union (single v) P)) = diff A (single v) := by
  funext u
  by_cases eq : u = v
  · subst u
    simp [union, single, diff, absent]
  · have different : (u == v) = false := Bool.eq_false_iff.mpr (fun h => eq (beq_iff_eq.mp h))
    cases pu : P u
    · simp only [union, single, diff, pu, different, Bool.false_or, Bool.not_false, Bool.and_true]
    · simp only [union, single, diff, pu, different, Bool.false_or, Bool.not_false,
        Bool.true_or, Bool.and_true, contained u pu]

private theorem blanket_delete {J : Relation n} (sg : Semigraphoid J) {child v : Fin n}
    {A P : Mask n} (childOutside : A child = false) (vOutside : P v = false)
    (blanket : IsBlanket J child A (union (single v) P))
    (toDelete : J (single child) (single v) P) : IsBlanket J child A P := by
  have contained : Subset P A := (subset_union_right _ _).trans blanket.1
  refine ⟨contained, ?_⟩
  have has : A v = true := blanket.1 v (by simp [union, single])
  have contracted := sg.contraction (delete_disjoint blanket.1 childOutside vOutside) toDelete
    (by rw [union_comm P (single v)]; exact blanket.2)
  rwa [union_single_and_remainder has vOutside] at contracted

/-- Every strict improving deletion maintains the conditional independence
of the removed variables given those retained (Lemma E.5). -/
theorem shrink_preserves_blanket {J : Relation n} (sg : Semigraphoid J) {child : Fin n}
    {score : LocalScore n} (localScore : LocallyConsistent J child score)
    {A : Mask n} (childOutside : A child = false) (budget : Nat) (parents : List (Fin n))
    (unique : parents.Nodup) (starting : IsBlanket J child A (maskOfList parents)) :
    IsBlanket J child A (maskOfList (shrink score budget parents)) := by
  induction budget generalizing parents with
  | zero => exact starting
  | succ budget ih =>
    rw [shrink]
    cases selected : nextRemoval score parents with
    | none => exact starting
    | some v =>
      obtain ⟨tail, equals⟩ := List.head?_eq_some_iff.mp selected
      have inRank : v ∈ rankedImprovements (fun w => score (parents.erase w)) (score parents) parents := by
        rw [show rankedImprovements (fun w => score (parents.erase w)) (score parents) parents = v :: tail from equals]
        exact List.mem_cons_self
      have ⟨inParents, better⟩ := mem_ranked_improvements.mp inRank
      have ⟨absent, uniqueRest⟩ := selected_erase_nodup inParents unique
      have ne : v ≠ child := by
        intro eq
        subst v
        have included := starting.1 child (decide_eq_true inParents)
        simp [childOutside] at included
      have childNotRest : child ∉ parents.erase v := by
        intro h
        exact ne (by
          have included := starting.1 child (decide_eq_true (List.erase_subset h))
          simp [childOutside] at included)
      have retained : score (v :: parents.erase v) = score parents :=
        localScore.set_score (maskOfList_perm (List.perm_cons_erase inParents).symm)
      have independent : J (single child) (single v) (maskOfList (parents.erase v)) := by
        apply Classical.byContradiction
        intro dep
        have added := localScore.gain ne absent childNotRest dep
        rw [retained] at added
        exact (Rat.not_lt.mpr (Rat.le_of_lt better)) added
      apply ih _ uniqueRest
      apply blanket_delete sg childOutside (by simp [maskOfList, absent]) _ independent
      simpa only [← selected_set_split inParents] using starting

/-- If a blanket contains an arrow's endpoint and that endpoint is independent
of the target given all remaining available variables, it can be deleted. -/
private theorem redundant_in_blanket {J : Relation n} (g : Graphoid J) {child v : Fin n}
    {A P : Mask n} (childOutside : A child = false) (vOutside : P v = false)
    (blanket : IsBlanket J child A (union (single v) P))
    (ci : J (single child) (single v) (diff A (single v))) : J (single child) (single v) P := by
  have disjoint := delete_disjoint blanket.1 childOutside vOutside
  have contained : Subset P A := (subset_union_right _ _).trans blanket.1
  have left : J (single child) (single v) (union P (diff A (union (single v) P))) := by
    rwa [union_parent_and_remainder contained vOutside]
  have combined := g.intersection disjoint left (by rw [union_comm P (single v)]; exact blanket.2)
  exact g.toSemigraphoid.decomposition disjoint combined

private theorem independent_outside_blanket {J : Relation n} (sg : Semigraphoid J)
    {child v : Fin n} {A P : Mask n} (childOutside : A child = false)
    (available : A v = true) (outside : P v = false)
    (blanket : IsBlanket J child A P) : J (single child) (single v) (diff A (single v)) := by
  have larger : Subset (union (single v) P) A := by
    intro a inUnion
    rcases Bool.or_eq_true_iff.mp inUnion with atV | inP
    · have same : a = v := by simpa [single] using atV
      simpa [same] using available
    · exact blanket.1 a inP
  have four := delete_disjoint larger childOutside outside
  have all : J (single child) (union (single v) (diff A (union (single v) P))) P := by
    rw [union_single_and_remainder available outside]
    exact blanket.2
  have := sg.weak_union four all
  rwa [union_parent_and_remainder blanket.1 outside] at this

/-- The terminal remove-test characterizes the blanket by the (RU) singleton
queries, without an assumed Markov-boundary witness. -/
theorem terminal_blanket_membership {J : Relation n} (g : Graphoid J) {child : Fin n}
    {score : LocalScore n} (localScore : LocallyConsistent J child score)
    {A : Mask n} (childOutside : A child = false) (parents : List (Fin n))
    (unique : parents.Nodup) (blanket : IsBlanket J child A (maskOfList parents))
    (terminal : ∀ v ∈ parents, score (parents.erase v) ≤ score parents)
    {v : Fin n} (available : A v = true) :
    v ∈ parents ↔ ¬ J (single child) (single v) (diff A (single v)) := by
  constructor
  · intro present ci
    have absent := (selected_erase_nodup present unique).1
    have larger : IsBlanket J child A (union (single v) (maskOfList (parents.erase v))) := by
      rwa [← selected_set_split present]
    have removed := redundant_in_blanket g childOutside (by simp [maskOfList, absent]) larger ci
    have retained : score (v :: parents.erase v) = score parents :=
      localScore.set_score (maskOfList_perm (List.perm_cons_erase present).symm)
    have ne : v ≠ child := by
      intro eq
      subst v
      simp [childOutside] at available
    have childNotRest : child ∉ parents.erase v := by
      intro h
      have included := blanket.1 child (decide_eq_true (List.erase_subset h))
      simp [childOutside] at included
    have loss := localScore.loss ne absent childNotRest removed
    rw [retained] at loss
    exact (Rat.not_lt.mpr (terminal v present)) loss
  · intro dep
    apply Classical.byContradiction
    intro absent
    exact dep (independent_outside_blanket g.toSemigraphoid childOutside available
      (by simp [maskOfList, absent]) blanket)

private theorem terminal_blanket_least {J : Relation n} (g : Graphoid J) {child : Fin n}
    {score : LocalScore n} (localScore : LocallyConsistent J child score)
    {A : Mask n} (childOutside : A child = false) (parents : List (Fin n))
    (unique : parents.Nodup) (blanket : IsBlanket J child A (maskOfList parents))
    (terminal : ∀ v ∈ parents, score (parents.erase v) ≤ score parents) {Q : Mask n}
    (other : IsBlanket J child A Q) : Subset (maskOfList parents) Q := by
  intro v present
  have available := blanket.1 v present
  have dep := (terminal_blanket_membership g localScore childOutside parents unique blanket terminal available).mp
    (of_decide_eq_true present)
  cases h : Q v with
  | false => exact (dep (independent_outside_blanket g.toSemigraphoid childOutside available h other)).elim
  | true => rfl


private theorem shrink_nodup (score : LocalScore n) (budget : Nat) {parents : List (Fin n)}
    (unique : parents.Nodup) : (shrink score budget parents).Nodup := by
  induction budget generalizing parents with
  | zero => exact unique
  | succ budget ih =>
    rw [shrink]
    cases nextRemoval score parents with
    | none => exact unique
    | some v => exact ih (unique.erase v)

/-- Shrinking any blanket returns the least blanket for the target among the
same available vertices. Starting from the full set specializes this to E.5. -/
theorem shrink_recovers_boundary {J : Relation n} (g : Graphoid J) {child : Fin n}
    {score : LocalScore n} (localScore : LocallyConsistent J child score)
    {A : Mask n} (childOutside : A child = false) (parents : List (Fin n))
    (unique : parents.Nodup) (starting : IsBlanket J child A (maskOfList parents)) :
    let selected := shrink score parents.length parents
    Boundary J child A (maskOfList selected) ∧
      ∀ Q, IsBlanket J child A Q → Subset (maskOfList selected) Q := by
  let selected := shrink score parents.length parents
  have blanket : IsBlanket J child A (maskOfList selected) :=
    shrink_preserves_blanket g.toSemigraphoid localScore childOutside _ _ unique starting
  have selectedUnique := shrink_nodup score parents.length unique
  have terminal := (shrink_properties score parents.length parents (Nat.le_refl _)).2.2
  have least {Q : Mask n} (other : IsBlanket J child A Q) :=
    terminal_blanket_least g localScore childOutside selected selectedUnique blanket terminal other
  exact ⟨⟨blanket, fun _ under other => mask_eq fun u => ⟨under u, least other u⟩⟩,
    fun _ other => least other⟩

/-- The full available set is already a blanket, so the shrink-only
algorithm of Lemma E.5 needs no composition assumption. -/
theorem shrink_full_recovers_boundary {J : Relation n} (g : Graphoid J) {child : Fin n}
    {score : LocalScore n} (localScore : LocallyConsistent J child score)
    (available : List (Fin n)) (unique : available.Nodup) (childOutside : child ∉ available) :
    let A := maskOfList available
    let P := maskOfList (shrink score available.length available)
    Boundary J child A P ∧ ∀ Q, IsBlanket J child A Q → Subset P Q := by
  let A := maskOfList available
  have noneLeft : diff A A = empty := by
    funext v
    cases hv : A v <;> simp [diff, empty, hv]
  apply shrink_recovers_boundary g localScore (by simp [maskOfList, childOutside]) available unique
  refine ⟨subset_refl A, ?_⟩
  change J (single child) (diff A A) A
  rw [noneLeft]
  exact g.empty_right (single child) A

/-- The actual reference grow–shrink project returns a blanket and a terminal
parent list. Its grow phase decreases the remaining pool by one each time. -/
theorem grow_shrink_blanket {J : Relation n} (sg : Semigraphoid J) (compose : Composition J)
    {child : Fin n} {score : LocalScore n} (localScore : LocallyConsistent J child score)
    {A : Mask n} (eligible : Mask n) (pool parents : List (Fin n))
    (uniquePool : pool.Nodup) (uniqueParents : parents.Nodup) (apart : ∀ v ∈ pool, v ∉ parents)
    (cover : A = union (maskOfList parents) (maskOfList (pool.filter eligible)))
    (childOutside : A child = false) :
    let selected := (growShrink score eligible pool parents).parents
    selected.Nodup ∧ IsBlanket J child A (maskOfList selected) ∧
      ∀ v ∈ selected, score (selected.erase v) ≤ score selected := by
  rw [growShrink]
  cases found : uncachedNext score eligible pool parents with
  | none =>
    have growing := grow_stop_blanket sg compose localScore eligible pool parents
      apart cover childOutside found
    exact ⟨shrink_nodup score parents.length uniqueParents,
      shrink_preserves_blanket sg localScore childOutside _ _ uniqueParents growing,
      (shrink_properties score parents.length parents (Nat.le_refl _)).2.2⟩
  | some v =>
    obtain ⟨rest, head⟩ := List.head?_eq_some_iff.mp found
    have candidate : v ∈ growBranches score (pool.filter eligible) parents := by
      rw [show growBranches score (pool.filter eligible) parents = v :: rest from head]
      exact List.mem_cons_self
    have ⟨vInPool, vEligible⟩ := List.mem_filter.mp (mem_ranked_improvements.mp candidate).1
    have ⟨notInNextPool, uniqueNextPool⟩ := selected_erase_nodup vInPool uniquePool
    have uniqueNextParents : (v :: parents).Nodup := List.nodup_cons.mpr ⟨apart v vInPool, uniqueParents⟩
    have newApart : ∀ x ∈ pool.erase v, x ∉ v :: parents := by
      intro x xInRemaining inParents
      rcases List.mem_cons.mp inParents with rfl | stays
      · exact notInNextPool xInRemaining
      · exact apart x (List.erase_subset xInRemaining) stays
    have newCover : A = union (maskOfList (v :: parents)) (maskOfList ((pool.erase v).filter eligible)) := by
      rw [cover]
      apply mask_eq
      intro w
      have poolSplit : w ∈ pool ↔ w = v ∨ w ∈ pool.erase v := by
        simpa only [List.mem_cons] using (List.perm_cons_erase vInPool).mem_iff (a := w)
      simp only [union, Bool.or_eq_true_iff, maskOfList, decide_eq_true_eq, List.mem_filter, List.mem_cons]
      rw [poolSplit]
      by_cases same : w = v
      · subst w
        simp [vEligible]
      · simp [same]
    exact grow_shrink_blanket sg compose localScore eligible (pool.erase v) (v :: parents)
      uniqueNextPool uniqueNextParents newApart newCover childOutside
termination_by pool.length
decreasing_by
  rw [List.length_erase_of_mem vInPool]
  exact Nat.sub_lt (List.length_pos_of_mem vInPool) (by decide)

private theorem project_vertex_properties {J : Relation n} (sg : Semigraphoid J) (compose : Composition J)
    {scores : Fin n → LocalScore n} (position : Fin n → Nat) (child : Fin n)
    (localScore : LocallyConsistent J child (scores child)) :
    let selected := (projectVertex scores position child).parents
    selected.Nodup ∧ IsBlanket J child (predecessors position child) (maskOfList selected) ∧
      ∀ v ∈ selected, scores child (selected.erase v) ≤ scores child selected := by
  rw [project_vertex_eq_uncached]
  apply grow_shrink_blanket sg compose localScore (precedesVertex position child)
    ((List.finRange n).erase child) [] ((List.nodup_finRange n).erase child) List.nodup_nil (by simp)
  · apply mask_eq
    intro v
    rw [maskOfList_nil]
    simp only [union, empty, Bool.false_or, maskOfList, decide_eq_true_eq,
      List.mem_filter, precedesVertex, predecessors]
    refine ⟨fun before => ⟨?_, before⟩, fun h => h.2⟩
    have ne : v ≠ child := fun same => (Nat.ne_of_lt before) (congrArg position same)
    exact List.mem_erase_of_ne ne |>.mpr (List.mem_finRange _)
  · simp [predecessors]

/-- The cached projection's parent set is the least Markov blanket in the
prefix. Composition and the strict local signs suffice for the proof (E.6). -/
theorem project_vertex_recovers_boundary {J : Relation n} (g : Graphoid J) (compose : Composition J)
    {scores : Fin n → LocalScore n} (position : Fin n → Nat) (child : Fin n)
    (localScore : LocallyConsistent J child (scores child)) :
    let P := maskOfList (projectVertex scores position child).parents
    Boundary J child (predecessors position child) P ∧
      ∀ Q, IsBlanket J child (predecessors position child) Q → Subset P Q := by
  obtain ⟨unique, blanket, terminal⟩ := project_vertex_properties g.toSemigraphoid compose
    position child localScore
  have least {Q : Mask n} (other : IsBlanket J child (predecessors position child) Q) :=
    terminal_blanket_least g localScore (by simp [predecessors]) _ unique blanket terminal other
  exact ⟨⟨blanket, fun _ under other => mask_eq fun u => ⟨under u, least other u⟩⟩,
    fun _ other => least other⟩

/-- With consistent local scores, BOSS's parent assignments agree with the
CI-oracle order projection at every order. -/
theorem project_edges_eq_orderDAG {J : Relation n} (g : Graphoid J) (compose : Composition J)
    {scores : Fin n → LocalScore n} (localScore : ∀ child, LocallyConsistent J child (scores child))
    {independent : CIOracle n} (agrees : MatchesOracle J independent) (position : Fin n → Nat) :
    (project scores position).edge = (orderDAG position independent).edge := by
  funext u v
  apply Bool.eq_iff_iff.mpr
  rw [orderDAG_edge_iff]
  by_cases before : position u < position v
  · have different : v ≠ u := fun same => (Nat.ne_of_lt before) (congrArg position same.symm)
    have atV : predecessorsExcept position u v v = false := by simp [predecessorsExcept]
    have atU : predecessorsExcept position u v u = false := by simp [predecessorsExcept]
    have membership := project_vertex_properties g.toSemigraphoid compose position v (localScore v)
    obtain ⟨unique, blanket, terminal⟩ := membership
    have membershipIff := terminal_blanket_membership g (localScore v) (by simp [predecessors])
      (projectVertex scores position v).parents unique blanket terminal
      (v := u) (by simp [predecessors, before])
    have eq : diff (predecessors position v) (single u) = predecessorsExcept position u v := by rfl
    rw [eq, ← (agrees v u _ different atV atU)] at membershipIff
    simpa only [project, decide_eq_true_eq, before, true_and, Bool.eq_false_iff] using membershipIff
  · simp only [before, false_and, iff_false]
    intro h
    exact before ((project scores position).edge_increases u v h)


theorem project_eq_orderDAG {J : Relation n} (g : Graphoid J) (compose : Composition J)
    {scores : Fin n → LocalScore n} (localScore : ∀ child, LocallyConsistent J child (scores child))
    {independent : CIOracle n} (agrees : MatchesOracle J independent) (position : Fin n → Nat) :
    project scores position = orderDAG position independent := by
  have edgeEq := project_edges_eq_orderDAG g compose localScore agrees position
  have rankEq : (project scores position).rank = (orderDAG position independent).rank := rfl
  generalize project scores position = left at edgeEq rankEq ⊢
  generalize orderDAG position independent = right at edgeEq rankEq ⊢
  cases left
  cases right
  cases edgeEq
  cases rankEq
  rfl

/-- Any complete input order yields a subgraph-minimal I-map in the population
score regime, independently of the order-search heuristic. -/
theorem project_sgs_minimal {J : Relation n} (g : Graphoid J) (compose : Composition J)
    {scores : Fin n → LocalScore n} (localScore : ∀ child, LocallyConsistent J child (scores child))
    {independent : CIOracle n} (agrees : MatchesOracle J independent) (position : Fin n → Nat)
    (distinctRanks : ∀ u v, position u = position v → u = v) :
    RaskuttiUhler2018.IsMarkov (project scores position) independent ∧
      ∀ H : DAG n, (∀ u v, H.edge u v = true → (project scores position).edge u v = true) →
        RaskuttiUhler2018.IsMarkov H independent → H.edge = (project scores position).edge := by
  rw [project_eq_orderDAG g compose localScore agrees position]
  exact induced_order_sgs_minimal g agrees position distinctRanks

/-- The starting DAG for the backward phase in Proposition 2 is a
subgraph-minimal I-map when the fitted local scores have their population signs. -/
theorem selected_dag_sgs_minimal {J : Relation n} (g : Graphoid J) (compose : Composition J)
    {scores : Fin n → LocalScore n} (localScore : ∀ child, LocallyConsistent J child (scores child))
    {independent : CIOracle n} (agrees : MatchesOracle J independent) (initial : List (Fin n))
    (complete : ∀ v, v ∈ initial) :
    RaskuttiUhler2018.IsMarkov (OrderSearch.selectedDAG scores initial) independent ∧
      ∀ H : DAG n, (∀ u v, H.edge u v = true → (OrderSearch.selectedDAG scores initial).edge u v = true) →
        RaskuttiUhler2018.IsMarkov H independent →
          H.edge = (OrderSearch.selectedDAG scores initial).edge := by
  let selected := OrderSearch.selectedOrder scores initial
  have permutation := (OrderSearch.selected_order_perm_and_locally_optimal scores initial).1
  change RaskuttiUhler2018.IsMarkov (project scores selected.idxOf) independent ∧ _
  apply project_sgs_minimal g compose localScore agrees
  intro x y equal
  have xBound := List.idxOf_lt_length_iff.mpr (permutation.mem_iff.mpr (complete x))
  have yBound := List.idxOf_lt_length_iff.mpr (permutation.mem_iff.mpr (complete y))
  have same : selected[selected.idxOf x]'xBound = selected[selected.idxOf y]'yBound := by simp only [equal]
  simpa only [List.getElem_idxOf] using same

/-- In the faithful population regime, the order-search DAG is a
subgraph-minimal I-map for the true graph's independence oracle. -/
theorem selected_dag_sgs_minimal_of_faithful {G : DAG n} {J : Relation n}
    (sg : Semigraphoid J) (faithful : DAGFaithful G J) {scores : Fin n → LocalScore n}
    (localScore : ∀ child, LocallyConsistent J child (scores child)) (initial : List (Fin n))
    (complete : ∀ v, v ∈ initial) :
    RaskuttiUhler2018.IsMarkov (OrderSearch.selectedDAG scores initial) (graphOracle G) ∧
      ∀ H : DAG n, (∀ u v, H.edge u v = true → (OrderSearch.selectedDAG scores initial).edge u v = true) →
        RaskuttiUhler2018.IsMarkov H (graphOracle G) → H.edge = (OrderSearch.selectedDAG scores initial).edge :=
  selected_dag_sgs_minimal (faithful_graphoid faithful sg) (faithful_composition faithful) localScore
    (graph_oracle_matches_faithful faithful) initial complete

private theorem uncached_score_eq (score : LocalScore n) (eligible : Mask n)
    (budget : Nat) (pool parents : List (Fin n)) :
    (uncached score eligible budget pool parents).score =
      score (uncached score eligible budget pool parents).parents := by
  induction budget generalizing pool parents with
  | zero => rfl
  | succ budget ih =>
    simp only [uncached]
    cases uncachedNext score eligible pool parents with
    | none => rfl
    | some v => exact ih _ _

private theorem project_vertex_score_eq (scores : Fin n → LocalScore n) (position : Fin n → Nat)
    (child : Fin n) : (projectVertex scores position child).score =
      scores child (projectVertex scores position child).parents := by
  unfold projectVertex
  rw [trace_build_eq_uncached]
  exact uncached_score_eq _ _ _ _ _

/-- Sum of local scores of the parent sets of a DAG. -/
def decomposableScore (scores : Fin n → LocalScore n) (G : DAG n) : Rat :=
  ((List.finRange n).map fun child => scores child ((List.finRange n).filter fun v => G.edge v child)).sum

/-- The grow–shrink order score is the decomposable score of that order's
CI-oracle DAG in the local-score regime (the compositional part of E.7). -/
theorem order_score_eq_induced_score {J : Relation n} (g : Graphoid J) (compose : Composition J)
    {scores : Fin n → LocalScore n} (localScore : ∀ child, LocallyConsistent J child (scores child))
    {independent : CIOracle n} (agrees : MatchesOracle J independent) (order : List (Fin n)) :
    OrderSearch.score scores order = decomposableScore scores (orderDAG order.idxOf independent) := by
  rw [← project_eq_orderDAG g compose localScore agrees order.idxOf]
  unfold OrderSearch.score decomposableScore
  congr 1
  apply List.map_congr_left
  intro child _
  rw [project_vertex_score_eq]
  apply (localScore child).set_score
  apply mask_eq
  intro v
  simp [maskOfList, project]

end

end OpenCausalScience.Papers.AndrewsEtAl2023.PopulationProjection
