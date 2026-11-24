module
public import OpenCausalScience.Papers.JungEtAl2024.SequentialAdjustment
public import OpenCausalScience.Papers.JungEtAl2024.SequentialFormula
public import OpenCausalScience.Papers.KimEtAl2026.BayesBallCorrectness
public import OpenCausalScience.Papers.KwonEtAl2025.AggregateReward

/-!
# Jung, Park, and Lee (2024), stage graphs in the corrected soundness proof

The 2026-10-25 correction proves sufficiency in Theorem 1 by Lemma S.1
(Appendix A.1, pp. 14–15). Fix a stage `i`, let `Gᵢ` be the graph obtained
by intervening on the future treatments `X≥i+1`, and let `H = Hᵢ₋₁`. This
module checks the following steps of that proof.

* Root conditioning. "In `Gᵢ`, future treatment vertices have no incoming
  arrowheads. Adding them to a separating set cannot activate a collider."
  An active simple path given the larger set has no newly conditioned
  noncollider. No collider is a root, and no root is a proper descendant of
  a collider, so the path is already active given the smaller set
  (`dConnected_of_root_augmented`). The executable test used by
  `SequentialAdjustment.satisfiesStage` is sound for path-level separation
  (`dSeparatedBy_of_dSeparated`). Hence the stage separation of Eq. (10)
  still holds given `Hᵢ₋₁ ∪ Zᵢ ∪ X≥i+1`, with distinct endpoints outside
  that set (`stage_separation_given_future`).
* Nondescendant invariance. In a ranked SCM, two plans that agree off the
  replaced vertices give the same value, for the same exogenous draw, at
  every vertex that is not downstream of a replaced vertex
  (`evaluate_eq_of_not_downstream`). The proof is an induction on the rank.
  The statement is pointwise in the plan and the draw, so it also applies
  when the future treatments are set to randomization coordinates of the
  draw. Readouts of the stage head (history, current covariates, current
  treatment and current outcomes) are unchanged by the future plan. This
  supplies the two observational head marginals required by
  `SequentialFormula.StageConditions.step_of_sample`
  (`SCMStage.head_conditionals_aligned`).
* Consistency. Setting the current treatment to the value it takes leaves
  every response unchanged (`evaluate_eq_of_natural_setting`). The stage
  sample built from an SCM therefore has a proved consistency field.

`SCMStage.stage_conditions` assembles one step of the recursion from these
results and keeps the remaining inputs explicit.

* Exchangeability, `StageSample.exchangeable`. The paper obtains it from
  Shpitser et al. (2010, Theorem 4) in `Gᵢ` with `W = Hᵢ₋₁ ∪ X≥i+1`, then
  conditions the randomized future treatments
  (`SequentialFormula.conditional_on_randomization`). The graph inputs
  proved here are the separation with the future treatments added and the
  fact that future treatments are not descendants of `Xᵢ` in `Gᵢ`. The
  counterfactual independence implied by the adjustment criterion is not
  formalized in this package. `satisfiesStage` checks one outcome vertex.
* Tail alignment, `tail_conditional`. The next target must be the
  conditional law of the later outcomes in the `do(x≥i+1)` world given the
  extended history. `evaluate_eq_of_not_downstream` with the replaced
  vertex `Xᵢ₊₁` gives pointwise agreement of the extended history in the
  `do(x≥i+1)` and `do(x≥i+2)` worlds. Encoding `extend` injectively on the
  supported histories and comparing the event masses remain to be done.
* Positivity, the target identity, and the finite covariate list.
* The premise `nondescendant`: the head vertices are neither future
  treatments nor their descendants in `G`. The paper derives it from the
  treatment order, the outcome partition and admissibility. Compatibility
  of the SCM with `G` and the restriction of the plan to future treatments
  are also premises.

Source: https://www.sanghacklee.me/ai-corrected/SAC_AI_corrected_2026-10-25.pdf
-/

namespace OpenCausalScience.Papers.JungEtAl2024.StageGraph

open OpenCausalScience
open OpenCausalScience.Papers.KimEtAl2026.BayesBall
open OpenCausalScience.Papers.KimEtAl2026.BayesBallCorrectness
open OpenCausalScience.Papers.JungEtAl2024.SequentialFormula
open OpenCausalScience.Papers.JungEtAl2024.SequentialAdjustment
  (intervene properBackdoor satisfiesStage)
open OpenCausalScience.Papers.KwonEtAl2025.AggregateReward (SCM Plan)

@[expose] public section

variable {n : Nat}

/-! ## Root conditioning -/

/-- A vertex without incoming arrows. Every future treatment is a root of
the graph intervened on the future treatments. -/
def IsRoot (G : DAG n) (r : Fin n) : Prop := ∀ p, G.edge p r = false

theorem not_directedWalk_to_root {G : DAG n} {r u : Fin n} (root : IsRoot G r) :
    ¬ G.DirectedWalk u r := by
  intro walk
  cases walk with
  | single edge => exact Bool.false_ne_true ((root _).symm.trans edge)
  | extend _ edge => exact Bool.false_ne_true ((root _).symm.trans edge)

/-- Path-level separation of two distinct endpoints outside the conditioning
set, following the d-separation convention of Sec. 2. -/
def DSeparatedBy {G : DAG n} (C : Conditioning G) (source target : Fin n) : Prop :=
  source ≠ target ∧ C.member source = false ∧ C.member target = false ∧
    ¬ DConnected C source target

private theorem member_false_of_augmented {G : DAG n} {C C' : Conditioning G}
    (base : ∀ u, C.member u = true → C'.member u = true) {u : Fin n}
    (outside : C'.member u = false) : C.member u = false := by
  cases h : C.member u with
  | false => rfl
  | true => exact absurd (outside.symm.trans (base u h)) Bool.false_ne_true

/-- A collider has an incoming arrow, so it is not a root. A root is not a
proper descendant of any vertex. Activation therefore comes from the
original conditioning set. -/
private theorem activated_of_root_augmented {G : DAG n} {C C' : Conditioning G}
    (added : ∀ u, C'.member u = true → C.member u = true ∨ IsRoot G u)
    {p u : Fin n} (incoming : G.edge p u = true) (active : C'.activated u = true) :
    C.activated u = true := by
  have split : C'.member u = true ∨ C'.descendantHit u = true := by
    simpa [Conditioning.activated] using active
  rcases split with here | below
  · rcases added u here with old | root
    · simp [Conditioning.activated, old]
    · exact absurd ((root p).symm.trans incoming) Bool.false_ne_true
  · obtain ⟨w, conditioned, walk⟩ := (C'.descendant_spec u).mp below
    rcases added w conditioned with old | root
    · have hit : C.descendantHit u = true := (C.descendant_spec u).mpr ⟨w, old, walk⟩
      simp [Conditioning.activated, hit]
    · exact absurd walk (not_directedWalk_to_root root)

private theorem activeStep_of_root_augmented {G : DAG n} {C C' : Conditioning G}
    (base : ∀ u, C.member u = true → C'.member u = true)
    (added : ∀ u, C'.member u = true → C.member u = true ∨ IsRoot G u)
    {current next : State (Fin n)} (step : ActiveStep C' current next) :
    ActiveStep C current next := by
  refine ⟨step.1, ?_⟩
  have turn := step.2
  unfold OpenTurn at turn ⊢
  by_cases collider : current.2 = .down ∧ next.2 = .up
  · rw [ite_eq_left collider] at turn ⊢
    have incoming : G.edge next.1 current.1 = true := by
      simpa [Move, collider.2] using step.1
    exact activated_of_root_augmented added incoming turn
  · rw [ite_eq_right collider] at turn ⊢
    exact member_false_of_augmented base turn

theorem activeWalk_of_root_augmented {G : DAG n} {C C' : Conditioning G}
    (base : ∀ u, C.member u = true → C'.member u = true)
    (added : ∀ u, C'.member u = true → C.member u = true ∨ IsRoot G u)
    {start final : State (Fin n)} {visited : List (Fin n)}
    (walk : ActiveWalk C' start visited final) : ActiveWalk C start visited final := by
  induction walk with
  | nil state => exact .nil state
  | cons step _ ih => exact .cons (activeStep_of_root_augmented base added step) ih

/-- Corrected Lemma S.1, root conditioning on paths. If every newly
conditioned vertex is a root, an active simple path given the larger set is
an active simple path given the smaller set. -/
theorem dConnected_of_root_augmented {G : DAG n} {C C' : Conditioning G}
    (base : ∀ u, C.member u = true → C'.member u = true)
    (added : ∀ u, C'.member u = true → C.member u = true ∨ IsRoot G u)
    {source target : Fin n} (connected : DConnected C' source target) :
    DConnected C source target := by
  obtain ⟨sourceOutside, targetOutside, visited, arrival, walk, nodup⟩ := connected
  exact ⟨member_false_of_augmented base sourceOutside,
    member_false_of_augmented base targetOutside, visited, arrival,
    activeWalk_of_root_augmented base added walk, nodup⟩

/-- Separation of distinct endpoints survives adding roots outside the
endpoints to the conditioning set. -/
theorem dSeparatedBy_of_root_augmented {G : DAG n} {C C' : Conditioning G}
    (base : ∀ u, C.member u = true → C'.member u = true)
    (added : ∀ u, C'.member u = true → C.member u = true ∨ IsRoot G u)
    {source target : Fin n} (separated : DSeparatedBy C source target)
    (sourceOutside : C'.member source = false) (targetOutside : C'.member target = false) :
    DSeparatedBy C' source target :=
  ⟨separated.1, sourceOutside, targetOutside,
    fun connected => separated.2.2.2 (dConnected_of_root_augmented base added connected)⟩

/-! ## Soundness of the executable separation test -/

private theorem length_le_of_nodup_subset {α : Type} [DecidableEq α] (l : List α) :
    ∀ m : List α, l.Nodup → (∀ a ∈ l, a ∈ m) → l.length ≤ m.length := by
  induction l with
  | nil => exact fun _ _ _ => Nat.zero_le _
  | cons a l ih =>
    intro m nodup inside
    obtain ⟨absent, rest⟩ := List.nodup_cons.mp nodup
    have present : a ∈ m := inside a List.mem_cons_self
    have smaller : l.length ≤ (m.erase a).length :=
      ih (m.erase a) rest fun b member =>
        (List.mem_erase_of_ne fun (same : b = a) => absent (same ▸ member)).mpr
          (inside b (List.mem_cons_of_mem _ member))
    rw [List.length_erase_of_mem present] at smaller
    have positive := List.length_pos_of_mem present
    simp only [List.length_cons]
    omega

private theorem length_lt_of_nodup_cons {u : Fin n} {l : List (Fin n)}
    (nodup : (u :: l).Nodup) : l.length < n := by
  have bound := length_le_of_nodup_subset (u :: l) (List.finRange n) nodup
    fun a _ => List.mem_finRange a
  rw [List.length_finRange] at bound
  simp only [List.length_cons] at bound
  omega

/-- One parent-closure round of `DAG.conditioningAncestors`. -/
private def ancestorStep (G : DAG n) (known : List (Fin n)) : List (Fin n) :=
  (List.finRange n).filter fun u => known.contains u || known.any (G.edge u)

private def ancestorRounds (G : DAG n) (cond : List (Fin n)) (rounds : Nat) : List (Fin n) :=
  (List.range rounds).foldl (fun known _ => ancestorStep G known) cond

private theorem conditioningAncestors_eq_rounds (G : DAG n) (cond : List (Fin n)) :
    G.conditioningAncestors cond = ancestorRounds G cond n := rfl

/-- Iterate a closure round in the order used by `List.foldl`. -/
private def iterateRounds (step : List (Fin n) → List (Fin n)) :
    Nat → List (Fin n) → List (Fin n)
  | 0, known => known
  | rounds + 1, known => iterateRounds step rounds (step known)

private theorem foldl_eq_iterateRounds (step : List (Fin n) → List (Fin n)) (l : List Nat) :
    ∀ known : List (Fin n),
      l.foldl (fun known _ => step known) known = iterateRounds step l.length known := by
  induction l with
  | nil => exact fun _ => rfl
  | cons _ l ih => exact fun known => ih (step known)

private theorem iterateRounds_succ (step : List (Fin n) → List (Fin n)) (rounds : Nat) :
    ∀ known : List (Fin n),
      iterateRounds step (rounds + 1) known = step (iterateRounds step rounds known) := by
  induction rounds with
  | zero => exact fun _ => rfl
  | succ rounds ih => exact fun known => ih (step known)

private theorem ancestorRounds_eq (G : DAG n) (cond : List (Fin n)) (rounds : Nat) :
    ancestorRounds G cond rounds = iterateRounds (ancestorStep G) rounds cond := by
  have unfolded := foldl_eq_iterateRounds (ancestorStep G) (List.range rounds) cond
  rw [List.length_range] at unfolded
  exact unfolded

private theorem ancestorRounds_zero (G : DAG n) (cond : List (Fin n)) :
    ancestorRounds G cond 0 = cond :=
  (ancestorRounds_eq G cond 0).trans rfl

private theorem ancestorRounds_succ (G : DAG n) (cond : List (Fin n)) (rounds : Nat) :
    ancestorRounds G cond (rounds + 1) = ancestorStep G (ancestorRounds G cond rounds) := by
  rw [ancestorRounds_eq, ancestorRounds_eq]
  exact iterateRounds_succ (ancestorStep G) rounds cond

private theorem mem_ancestorStep_of_mem {G : DAG n} {known : List (Fin n)} {u : Fin n}
    (member : u ∈ known) : u ∈ ancestorStep G known :=
  List.mem_filter.mpr ⟨List.mem_finRange u,
    Bool.or_eq_true_iff.mpr (Or.inl (List.contains_iff_mem.mpr member))⟩

private theorem mem_ancestorStep_of_edge {G : DAG n} {known : List (Fin n)} {u w : Fin n}
    (edge : G.edge u w = true) (member : w ∈ known) : u ∈ ancestorStep G known :=
  List.mem_filter.mpr ⟨List.mem_finRange u,
    Bool.or_eq_true_iff.mpr (Or.inr (List.any_eq_true.mpr ⟨w, member, edge⟩))⟩

private theorem ancestorRounds_mono {G : DAG n} {cond : List (Fin n)} {u : Fin n}
    {early : Nat} (member : u ∈ ancestorRounds G cond early) :
    ∀ late, early ≤ late → u ∈ ancestorRounds G cond late := by
  intro late
  induction late with
  | zero =>
    intro le
    rw [Nat.le_zero.mp le] at member
    exact member
  | succ late ih =>
    intro le
    rcases Nat.lt_or_eq_of_le le with lt | same
    · rw [ancestorRounds_succ]
      exact mem_ancestorStep_of_mem (ih (Nat.le_of_lt_succ lt))
    · rw [← same]
      exact member

/-- Vertices of strictly larger rank. The length bounds the number of
closure rounds needed to reach a vertex. -/
private def higherRanked (G : DAG n) (u : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun v => decide (G.rank u < G.rank v)

private theorem higherRanked_nodup_cons (G : DAG n) (u : Fin n) :
    (u :: higherRanked G u).Nodup := by
  apply List.nodup_cons.mpr
  refine ⟨fun member => ?_, List.Sublist.nodup List.filter_sublist (List.nodup_finRange n)⟩
  exact Nat.lt_irrefl _ (of_decide_eq_true (List.mem_filter.mp member).2)

private theorem higherRanked_length_lt (G : DAG n) (u : Fin n) :
    (higherRanked G u).length < n :=
  length_lt_of_nodup_cons (higherRanked_nodup_cons G u)

private theorem higherRanked_length_lt_of_edge (G : DAG n) {u v : Fin n}
    (edge : G.edge u v = true) : (higherRanked G v).length < (higherRanked G u).length := by
  have inside : ∀ a ∈ v :: higherRanked G v, a ∈ higherRanked G u := by
    intro a member
    apply List.mem_filter.mpr
    refine ⟨List.mem_finRange a, decide_eq_true ?_⟩
    rcases List.mem_cons.mp member with same | later
    · rw [same]
      exact G.edge_increases _ _ edge
    · exact Nat.lt_trans (G.edge_increases _ _ edge)
        (of_decide_eq_true (List.mem_filter.mp later).2)
  have bound := length_le_of_nodup_subset _ _ (higherRanked_nodup_cons G v) inside
  simp only [List.length_cons] at bound
  omega

private theorem directedWalk_first_edge {G : DAG n} {u w : Fin n}
    (walk : G.DirectedWalk u w) : ∃ v, G.edge u v = true ∧ (v = w ∨ G.DirectedWalk v w) := by
  induction walk with
  | single edge => exact ⟨_, edge, Or.inl rfl⟩
  | extend _ edge ih =>
    obtain ⟨v, first, rest⟩ := ih
    refine ⟨v, first, Or.inr ?_⟩
    rcases rest with same | walk
    · rw [same]
      exact .single edge
    · exact .extend walk edge

/-- `DAG.conditioningAncestors` contains every conditioned vertex and every
vertex with a directed walk to a conditioned vertex. -/
theorem mem_conditioningAncestors {G : DAG n} (C : Conditioning G) {cond : List (Fin n)}
    (member : ∀ v, C.member v = true → v ∈ cond) {u : Fin n}
    (active : C.activated u = true) : u ∈ G.conditioningAncestors cond := by
  rw [conditioningAncestors_eq_rounds]
  suffices reach : ∀ k (v : Fin n), (higherRanked G v).length = k →
      C.activated v = true → v ∈ ancestorRounds G cond k by
    exact ancestorRounds_mono (reach _ u rfl active) n
      (Nat.le_of_lt (higherRanked_length_lt G u))
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro v size activeHere
    have split : C.member v = true ∨ C.descendantHit v = true := by
      simpa [Conditioning.activated] using activeHere
    rcases split with here | below
    · have base : v ∈ ancestorRounds G cond 0 := by
        rw [ancestorRounds_zero]
        exact member v here
      exact ancestorRounds_mono base k (Nat.zero_le k)
    · obtain ⟨w, conditioned, walk⟩ := (C.descendant_spec v).mp below
      obtain ⟨next, edge, rest⟩ := directedWalk_first_edge walk
      have nextActive : C.activated next = true := by
        rcases rest with same | later
        · rw [same]
          simp [Conditioning.activated, conditioned]
        · have hit : C.descendantHit next = true :=
            (C.descendant_spec next).mpr ⟨w, conditioned, later⟩
          simp [Conditioning.activated, hit]
      have smaller : (higherRanked G next).length < k :=
        Nat.lt_of_lt_of_le (higherRanked_length_lt_of_edge G edge) (Nat.le_of_eq size)
      have step : v ∈ ancestorRounds G cond ((higherRanked G next).length + 1) := by
        rw [ancestorRounds_succ]
        exact mem_ancestorStep_of_edge edge (ih _ smaller next rfl nextActive)
      exact ancestorRounds_mono step k (Nat.succ_le_of_lt smaller)

private theorem no_two_cycle (G : DAG n) {u v : Fin n} (forward : G.edge u v = true)
    (backward : G.edge v u = true) : False :=
  Nat.lt_irrefl _ (Nat.lt_trans (G.edge_increases _ _ forward) (G.edge_increases _ _ backward))

/-- The turn test of `DAG.searchActivePath` at an interior vertex accepts
every active step. In a DAG, the arrival and departure directions of the
walk determine the collider test made by the search. -/
private theorem search_turn {G : DAG n} {C : Conditioning G} {cond activated : List (Fin n)}
    (member : ∀ u, C.member u = cond.contains u)
    (closure : ∀ u, C.activated u = true → activated.contains u = true)
    {prev : Fin n} {start next : State (Fin n)}
    (arrivedDown : start.2 = .down → G.edge prev start.1 = true)
    (arrivedUp : start.2 = .up → G.edge start.1 prev = true)
    (step : ActiveStep C start next) :
    (if G.edge prev start.1 && G.edge next.1 start.1 then activated.contains start.1
      else !(cond.contains start.1)) = true := by
  have turn := step.2
  unfold OpenTurn at turn
  cases test : (G.edge prev start.1 && G.edge next.1 start.1) with
  | true =>
    rw [ite_eq_left (rfl : true = true)]
    obtain ⟨fromPrev, fromNext⟩ := Bool.and_eq_true_iff.mp test
    have down : start.2 = .down := by
      cases direction : start.2 with
      | down => rfl
      | up => exact (no_two_cycle G fromPrev (arrivedUp direction)).elim
    have up : next.2 = .up := by
      cases direction : next.2 with
      | up => rfl
      | down =>
        have outgoing : G.edge start.1 next.1 = true := by
          simpa [Move, direction] using step.1
        exact (no_two_cycle G outgoing fromNext).elim
    rw [ite_eq_left (And.intro down up)] at turn
    exact closure _ turn
  | false =>
    rw [ite_eq_right Bool.false_ne_true]
    by_cases collider : start.2 = .down ∧ next.2 = .up
    · have fromPrev := arrivedDown collider.1
      have fromNext : G.edge next.1 start.1 = true := by
        simpa [Move, collider.2] using step.1
      rw [fromPrev, fromNext] at test
      exact absurd test (by decide)
    · rw [ite_eq_right collider] at turn
      exact congrArg (fun b => !b) ((member _).symm.trans turn)

/-- `DAG.searchActivePath` finds every active walk whose visited vertices
are distinct and still available, provided the fuel exceeds its length. -/
private theorem search_finds_walk {G : DAG n} {C : Conditioning G} {target : Fin n}
    {cond activated : List (Fin n)}
    (member : ∀ u, C.member u = cond.contains u)
    (closure : ∀ u, C.activated u = true → activated.contains u = true)
    {start final : State (Fin n)} {visited : List (Fin n)}
    (walk : ActiveWalk C start visited final) :
    final.1 = target → ∀ (fuel : Nat) (previous : Option (Fin n)) (unvisited : List (Fin n)),
      visited.length < fuel → visited.Nodup → (∀ u ∈ visited, u ∈ unvisited) →
      (∀ prev, previous = some prev →
        (start.2 = .down → G.edge prev start.1 = true) ∧
          (start.2 = .up → G.edge start.1 prev = true)) →
      G.searchActivePath target cond activated fuel previous start.1 unvisited = true := by
  induction walk with
  | nil state =>
    intro reaches fuel _ _ small _ _ _
    cases fuel with
    | zero => exact absurd small (Nat.not_lt_zero _)
    | succ fuel => rw [DAG.searchActivePath, ite_eq_left (beq_iff_eq.mpr reaches)]
  | @cons start next final rest step _ ih =>
    intro reaches fuel previous unvisited small nodup available arrived
    cases fuel with
    | zero => exact absurd small (Nat.not_lt_zero _)
    | succ fuel =>
      by_cases atTarget : start.1 = target
      · rw [DAG.searchActivePath, ite_eq_left (beq_iff_eq.mpr atTarget)]
      · rw [DAG.searchActivePath, ite_eq_right fun found => atTarget (beq_iff_eq.mp found)]
        obtain ⟨absent, distinct⟩ := List.nodup_cons.mp nodup
        have adjacent : (G.edge start.1 next.1 || G.edge next.1 start.1) = true := by
          cases direction : next.2 with
          | up =>
            have edge : G.edge next.1 start.1 = true := by
              simpa [Move, direction] using step.1
            exact Bool.or_eq_true_iff.mpr (Or.inr edge)
          | down =>
            have edge : G.edge start.1 next.1 = true := by
              simpa [Move, direction] using step.1
            exact Bool.or_eq_true_iff.mpr (Or.inl edge)
        have later : G.searchActivePath target cond activated fuel (some start.1) next.1
            (unvisited.filter (· != next.1)) = true := by
          refine ih reaches fuel (some start.1) _ ?_ distinct ?_ ?_
          · simp only [List.length_cons] at small
            omega
          · intro u inRest
            refine List.mem_filter.mpr ⟨available u (List.mem_cons_of_mem _ inRest), ?_⟩
            exact bne_iff_ne.mpr fun (same : u = next.1) => absent (same ▸ inRest)
          · intro _ same
            cases same
            constructor
            · intro direction
              simpa [Move, direction] using step.1
            · intro direction
              simpa [Move, direction] using step.1
        apply List.any_eq_true.mpr
        refine ⟨next.1, available next.1 List.mem_cons_self, ?_⟩
        cases previous with
        | none =>
          exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨adjacent, rfl⟩, later⟩
        | some prev =>
          exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
            ⟨adjacent, search_turn member closure (arrived prev rfl).1 (arrived prev rfl).2 step⟩,
            later⟩

/-- The executable test reports separation only for distinct unconditioned
endpoints, after a search that found no active path. -/
private theorem dSeparated_eq_some_true {G : DAG n} {x y : Fin n} {cond : List (Fin n)}
    (separated : G.dSeparated x y cond = some true) :
    x ≠ y ∧ cond.contains x = false ∧ cond.contains y = false ∧
      G.searchActivePath y cond (G.conditioningAncestors cond) n none x
        ((List.finRange n).filter (· != x)) = false := by
  change (if (x == y || cond.contains x || cond.contains y) = true then none else
    some (!(G.searchActivePath y cond (G.conditioningAncestors cond) n none x
      ((List.finRange n).filter (· != x))))) = some true at separated
  by_cases guard : (x == y || cond.contains x || cond.contains y) = true
  · rw [ite_eq_left guard] at separated
    exact absurd separated (by decide)
  · rw [ite_eq_right guard] at separated
    simp only [Bool.or_eq_true_iff, not_or] at guard
    obtain ⟨⟨different, xOutside⟩, yOutside⟩ := guard
    refine ⟨fun same => different (beq_iff_eq.mpr same), Bool.eq_false_iff.mpr xOutside,
      Bool.eq_false_iff.mpr yOutside, ?_⟩
    cases found : G.searchActivePath y cond (G.conditioningAncestors cond) n none x
        ((List.finRange n).filter (· != x)) with
    | false => rfl
    | true =>
      rw [found] at separated
      exact absurd separated (by decide)

/-- The executable test used by `SequentialAdjustment.satisfiesStage` is
sound for path-level separation. When it reports separation, the endpoints
are distinct and unconditioned, and no active simple path joins them. -/
theorem dSeparatedBy_of_dSeparated {G : DAG n} {x y : Fin n} {cond : List (Fin n)}
    (separated : G.dSeparated x y cond = some true) :
    DSeparatedBy (Conditioning.ofPredicate G cond.contains) x y := by
  obtain ⟨different, xOutside, yOutside, notFound⟩ := dSeparated_eq_some_true separated
  refine ⟨different, xOutside, yOutside, ?_⟩
  rintro ⟨_, _, _, _, walk, nodup⟩
  obtain ⟨absent, distinct⟩ := List.nodup_cons.mp nodup
  have found := search_finds_walk (C := Conditioning.ofPredicate G cond.contains) (target := y)
    (cond := cond) (activated := G.conditioningAncestors cond) (fun _ => rfl)
    (fun _ active => List.contains_iff_mem.mpr
      (mem_conditioningAncestors (Conditioning.ofPredicate G cond.contains)
        (fun _ conditioned => List.contains_iff_mem.mp conditioned) active))
    walk rfl n none ((List.finRange n).filter (· != x)) (length_lt_of_nodup_cons nodup) distinct
    (fun u inVisited => List.mem_filter.mpr
      ⟨List.mem_finRange u, bne_iff_ne.mpr fun (same : u = x) => absent (same ▸ inVisited)⟩)
    (fun _ impossible => by cases impossible)
  exact Bool.false_ne_true (notFound.symm.trans found)

/-! ## The stage graph -/

theorem isRoot_intervene (graph : DAG n) {treatments : List (Fin n)} {r : Fin n}
    (member : r ∈ treatments) : IsRoot (intervene graph treatments) r := by
  intro _
  apply Bool.eq_false_iff.mpr
  intro edge
  have kept := (Bool.and_eq_true_iff.mp edge).2
  rw [List.contains_iff_mem.mpr member] at kept
  exact absurd kept (by decide)

theorem isRoot_properBackdoor {graph : DAG n} {treatment target r : Fin n}
    (root : IsRoot graph r) : IsRoot (properBackdoor graph treatment target) r := by
  intro p
  apply Bool.eq_false_iff.mpr
  intro edge
  exact Bool.false_ne_true ((root p).symm.trans (Bool.and_eq_true_iff.mp edge).1)

/-- Future treatments are not descendants of the current treatment after
the intervention, so they contribute no forbidden vertex at this stage. -/
theorem not_directedWalk_to_future (graph : DAG n) {future : List (Fin n)} {u f : Fin n}
    (member : f ∈ future) : ¬ (intervene graph future).DirectedWalk u f :=
  not_directedWalk_to_root (isRoot_intervene graph member)

private theorem or_eq_false {a b : Bool} (left : a = false) (right : b = false) :
    (a || b) = false := by
  subst left
  subst right
  rfl

/-- Corrected Lemma S.1, root conditioning at one stage. If the stage passes
the separation test of Eq. (10) in the proper sequential back-door graph,
the treatment and the outcome remain separated after the future treatments
are added to `Hᵢ₋₁ ∪ Zᵢ`. The forbidden-set graph is not used. -/
theorem stage_separation_given_future {G forbiddenGraph : DAG n}
    {future history adjustment : List (Fin n)} {treatment target : Fin n}
    (stage : satisfiesStage (properBackdoor (intervene G future) treatment target)
      forbiddenGraph treatment target history adjustment)
    (treatmentNotFuture : treatment ∉ future) (targetNotFuture : target ∉ future) :
    DSeparatedBy (Conditioning.ofPredicate (properBackdoor (intervene G future) treatment target)
      fun u => (history ++ adjustment).contains u || future.contains u) treatment target := by
  have separated := dSeparatedBy_of_dSeparated stage.1
  have outsideFuture {u : Fin n} (absent : u ∉ future) : future.contains u = false :=
    Bool.eq_false_iff.mpr fun contained => absent (List.contains_iff_mem.mp contained)
  refine dSeparatedBy_of_root_augmented ?_ ?_ separated
    (or_eq_false separated.2.1 (outsideFuture treatmentNotFuture))
    (or_eq_false separated.2.2.1 (outsideFuture targetNotFuture))
  · intro _ conditioned
    exact Bool.or_eq_true_iff.mpr (Or.inl conditioned)
  · intro _ conditioned
    rcases Bool.or_eq_true_iff.mp conditioned with old | new
    · exact Or.inl old
    · exact Or.inr (isRoot_properBackdoor (isRoot_intervene G (List.contains_iff_mem.mp new)))

/-! ## Nondescendant invariance in a ranked SCM -/

section Invariance

variable {V Source Value Noise : Type}

/-- Vertices reached from a replaced vertex along parent arrows of the
model, including the replaced vertices. -/
inductive Downstream (model : SCM V Source Value Noise) (replaced : V → Prop) : V → Prop where
  | start {v : V} : replaced v → Downstream model replaced v
  | child {p v : V} : Downstream model replaced p → model.parent p v →
      Downstream model replaced v

/-- Corrected Lemma S.1, invariance under replaced equations. Two plans that
agree off the replaced vertices give the same value, for the same exogenous
draw, at every vertex that is not downstream of a replaced vertex. -/
theorem evaluate_eq_of_not_downstream (model : SCM V Source Value Noise)
    {replaced : V → Prop} {plan other : Plan V Value}
    (agree : ∀ v, ¬ replaced v → plan v = other v) (noise : Source → Noise) (v : V)
    (outside : ¬ Downstream model replaced v) :
    model.evaluate plan noise v = model.evaluate other noise v := by
  induction h : model.rank v using Nat.strongRecOn generalizing v with
  | ind k ih =>
    rw [model.solve plan, model.solve other, agree v fun here => outside (.start here)]
    cases (other v) with
    | some value => rfl
    | none =>
      apply model.respects_inputs
      · intro p edge
        exact ih (model.rank p) (h ▸ model.parent_lower edge) p
          (fun down => outside (.child down edge)) rfl
      · intro _ _
        rfl

/-- Setting a vertex to the value that it already takes for this draw
leaves every value unchanged. This gives the consistency field of the
stage sample. -/
theorem evaluate_eq_of_natural_setting (model : SCM V Source Value Noise)
    {plan setting : Plan V Value} {target : V} {value : Value} (noise : Source → Noise)
    (fixed : setting target = some value) (others : ∀ v, v ≠ target → setting v = plan v)
    (natural : model.evaluate plan noise target = value) (v : V) :
    model.evaluate setting noise v = model.evaluate plan noise v := by
  induction h : model.rank v using Nat.strongRecOn generalizing v with
  | ind k ih =>
    by_cases same : v = target
    · rw [same, model.solve setting, fixed]
      exact natural.symm
    · rw [model.solve setting, model.solve plan, others v same]
      cases (plan v) with
      | some current => rfl
      | none =>
        apply model.respects_inputs
        · intro p edge
          exact ih (model.rank p) (h ▸ model.parent_lower edge) p rfl
        · intro _ _
          rfl

end Invariance

/-- A compatible model has all its parent arrows in the DAG. A vertex that
is neither a future treatment nor a descendant of one in the DAG is not
downstream of the future treatments in the model. -/
theorem not_downstream_of_nondescendant {Source Value Noise : Type}
    {model : SCM (Fin n) Source Value Noise} {G : DAG n}
    (compatible : ∀ p v, model.parent p v → G.edge p v = true)
    {future : List (Fin n)} {v : Fin n}
    (notFuture : v ∉ future) (nondescendant : ∀ f ∈ future, ¬ G.DirectedWalk f v) :
    ¬ Downstream model (· ∈ future) v := by
  have reach {w : Fin n} (down : Downstream model (· ∈ future) w) :
      w ∈ future ∨ ∃ f ∈ future, G.DirectedWalk f w := by
    induction down with
    | start member => exact Or.inl member
    | child _ edge ih =>
      rcases ih with member | ⟨f, member, walk⟩
      · exact Or.inr ⟨_, member, .single (compatible _ _ edge)⟩
      · exact Or.inr ⟨f, member, .extend walk (compatible _ _ edge)⟩
  intro down
  rcases reach down with member | ⟨f, member, walk⟩
  · exact notFuture member
  · exact nondescendant f member walk

/-- A readout of an assignment that depends only on the listed vertices. -/
def ReadsOnly {Value α : Type} (vertices : List (Fin n)) (read : (Fin n → Value) → α) : Prop :=
  ∀ x x', (∀ v ∈ vertices, x v = x' v) → read x = read x'

/-- Corrected Lemma S.1, head invariance for one exogenous draw. A plan that
replaces only future-treatment equations does not change a readout of
vertices that are neither future treatments nor their descendants. -/
theorem readout_eq_of_future_plan {Source Value Noise α : Type}
    {model : SCM (Fin n) Source Value Noise} {G : DAG n}
    (compatible : ∀ p v, model.parent p v → G.edge p v = true)
    {future head : List (Fin n)} {plan : Plan (Fin n) Value}
    (planned : ∀ v, v ∉ future → plan v = none)
    (nondescendant : ∀ v ∈ head, v ∉ future ∧ ∀ f ∈ future, ¬ G.DirectedWalk f v)
    {read : (Fin n → Value) → α} (reads : ReadsOnly head read) (noise : Source → Noise) :
    read (model.evaluate plan noise) = read (model.evaluate (fun _ => none) noise) := by
  apply reads
  intro v member
  obtain ⟨notFuture, notBelow⟩ := nondescendant v member
  exact evaluate_eq_of_not_downstream model (replaced := (· ∈ future)) planned noise v
    (not_downstream_of_nondescendant compatible notFuture notBelow)

/-! ## Observational head marginals -/

private theorem eventMass_congr {Ω : Type} (atoms : List Ω) (weight : Ω → Rat)
    {left right : Ω → Bool} (equal : ∀ a ∈ atoms, left a = right a) :
    eventMass atoms weight left = eventMass atoms weight right := by
  apply congrArg List.sum
  exact List.map_congr_left fun a member => by rw [equal a member]

section Head

variable {Ω H Z Y T : Type} [DecidableEq H] [DecidableEq Z] [DecidableEq Y] [DecidableEq T]

/-- `P(z | h)` from finite head readouts, a factor of the chain-rule form
of Eq. (2). -/
def headCovariate (atoms : List Ω) (weight : Ω → Rat) (history : Ω → H) (covariate : Ω → Z)
    (h : H) (z : Z) : Rat :=
  eventMass atoms weight (fun a => decide (history a = h ∧ covariate a = z)) /
    eventMass atoms weight (fun a => decide (history a = h))

/-- `P(y | h, xᵢ, z)` from finite head readouts. `selected` records that the
current treatment takes its scheduled value. -/
def headOutcome (atoms : List Ω) (weight : Ω → Rat) (history : Ω → H) (covariate : Ω → Z)
    (selected : Ω → Bool) (current : Ω → Y) (h : H) (z : Z) (y : Y) : Rat :=
  eventMass atoms weight (fun a =>
      decide (history a = h ∧ covariate a = z) && selected a && decide (current a = y)) /
    eventMass atoms weight (fun a => decide (history a = h ∧ covariate a = z) && selected a)

/-- If a stage sample and an observational readout agree on the history,
the current covariates, the current treatment and the current outcomes at
every atom, the observational conditionals equal the ratios used in
`SequentialFormula.StageConditions.step_of_sample`. -/
theorem head_conditionals_of_head_eq (q : StageSample Ω H Z Y T)
    (history : Ω → H) (covariate : Ω → Z) (selected : Ω → Bool) (current : Ω → Y)
    (same : ∀ a ∈ q.atoms, q.history a = history a ∧ q.covariate a = covariate a ∧
      q.selected a = selected a ∧ q.currentOutcome a = current a) :
    (∀ h z, headCovariate q.atoms q.weight history covariate h z =
      q.masses.covariate h z / q.masses.history h) ∧
    (∀ h z y, headOutcome q.atoms q.weight history covariate selected current h z y =
      q.masses.currentOutcome h z y / q.masses.treatment h z) := by
  have cell (h : H) (z : Z) (a : Ω) (member : a ∈ q.atoms) :
      decide (history a = h ∧ covariate a = z) = q.inCell h z a := by
    obtain ⟨sameHistory, sameCovariate, -, -⟩ := same a member
    rw [StageSample.inCell, sameHistory, sameCovariate]
  refine ⟨fun h z => ?_, fun h z y => ?_⟩
  · have numerator : eventMass q.atoms q.weight
          (fun a => decide (history a = h ∧ covariate a = z)) = q.masses.covariate h z :=
      eventMass_congr _ _ (cell h z)
    have denominator : eventMass q.atoms q.weight (fun a => decide (history a = h)) =
        q.masses.history h :=
      eventMass_congr _ _ fun a member => by rw [(same a member).1]
    unfold headCovariate
    rw [numerator, denominator]
  · have numerator : eventMass q.atoms q.weight (fun a =>
          decide (history a = h ∧ covariate a = z) && selected a && decide (current a = y)) =
        q.masses.currentOutcome h z y :=
      eventMass_congr _ _ fun a member => by
        rw [cell h z a member, (same a member).2.2.1, (same a member).2.2.2]
    have denominator : eventMass q.atoms q.weight (fun a =>
          decide (history a = h ∧ covariate a = z) && selected a) = q.masses.treatment h z :=
      eventMass_congr _ _ fun a member => by
        rw [cell h z a member, (same a member).2.2.1]
    unfold headOutcome
    rw [numerator, denominator]

end Head

/-! ## The stage sample of a ranked SCM -/

/-- One stage of Lemma S.1 in a ranked SCM on the DAG vertices: a finite
exogenous law, the plan for the future treatments, the current treatment
and its scheduled value, and readouts of the history `Hᵢ₋₁`, the covariate
block `Zᵢ`, the current outcome block `Yᵢ` and the later outcomes. -/
structure SCMStage (n : Nat) (Source Value Noise H Z Y T : Type) where
  model : SCM (Fin n) Source Value Noise
  atoms : List (Source → Noise)
  weight : (Source → Noise) → Rat
  nonnegative : ∀ a ∈ atoms, 0 ≤ weight a
  normalized : (atoms.map weight).sum = 1
  plan : Plan (Fin n) Value
  treatment : Fin n
  value : Value
  readHistory : (Fin n → Value) → H
  readCovariate : (Fin n → Value) → Z
  readCurrent : (Fin n → Value) → Y
  readTail : (Fin n → Value) → T

namespace SCMStage

variable {Source Value Noise H Z Y T : Type}

/-- The joint plan for the current and the future treatments. -/
def jointPlan (s : SCMStage n Source Value Noise H Z Y T) : Plan (Fin n) Value :=
  fun v => if v = s.treatment then some s.value else s.plan v

theorem jointPlan_treatment (s : SCMStage n Source Value Noise H Z Y T) :
    s.jointPlan s.treatment = some s.value := by
  show (if s.treatment = s.treatment then some s.value else s.plan s.treatment) = some s.value
  exact ite_eq_left rfl

theorem jointPlan_other (s : SCMStage n Source Value Noise H Z Y T) (v : Fin n)
    (different : v ≠ s.treatment) : s.jointPlan v = s.plan v := by
  show (if v = s.treatment then some s.value else s.plan v) = s.plan v
  exact ite_eq_right different

/-- Responses with no equation replaced. -/
def observed (s : SCMStage n Source Value Noise H Z Y T) (a : Source → Noise) :
    Fin n → Value :=
  s.model.evaluate (fun _ => none) a

/-- The stage sample in the world where `plan` fixes the future treatments.
The potential outcome also fixes the current treatment. Its consistency
field follows from `evaluate_eq_of_natural_setting`. -/
def sample [DecidableEq Value] (s : SCMStage n Source Value Noise H Z Y T) :
    StageSample (Source → Noise) H Z Y T where
  atoms := s.atoms
  weight := s.weight
  nonnegative := s.nonnegative
  normalized := s.normalized
  history a := s.readHistory (s.model.evaluate s.plan a)
  covariate a := s.readCovariate (s.model.evaluate s.plan a)
  selected a := decide (s.model.evaluate s.plan a s.treatment = s.value)
  currentOutcome a := s.readCurrent (s.model.evaluate s.plan a)
  tailOutcome a := s.readTail (s.model.evaluate s.plan a)
  potentialOutcome a :=
    (s.readCurrent (s.model.evaluate s.jointPlan a), s.readTail (s.model.evaluate s.jointPlan a))
  consistency := by
    intro a _ chosen
    have same : s.model.evaluate s.jointPlan a = s.model.evaluate s.plan a :=
      funext (evaluate_eq_of_natural_setting s.model a s.jointPlan_treatment s.jointPlan_other
        (of_decide_eq_true chosen))
    simp only [same]

/-- The observational `P(z | h)`. No equation is replaced. -/
def observedCovariate [DecidableEq H] [DecidableEq Z]
    (s : SCMStage n Source Value Noise H Z Y T) : H → Z → Rat :=
  headCovariate s.atoms s.weight (fun a => s.readHistory (s.observed a))
    (fun a => s.readCovariate (s.observed a))

/-- The observational `P(y | h, xᵢ, z)`. No equation is replaced. -/
def observedOutcome [DecidableEq H] [DecidableEq Z] [DecidableEq Y] [DecidableEq Value]
    (s : SCMStage n Source Value Noise H Z Y T) : H → Z → Y → Rat :=
  headOutcome s.atoms s.weight (fun a => s.readHistory (s.observed a))
    (fun a => s.readCovariate (s.observed a)) (fun a => decide (s.observed a s.treatment = s.value))
    (fun a => s.readCurrent (s.observed a))

/-- Corrected Lemma S.1, the head of the stage for each exogenous draw. The
plan replaces only future-treatment equations, and the head readouts use
vertices that are neither future treatments nor their descendants in `G`. -/
theorem head_eq_observed [DecidableEq Value] (s : SCMStage n Source Value Noise H Z Y T)
    {G : DAG n} (compatible : ∀ p v, s.model.parent p v → G.edge p v = true)
    {future head : List (Fin n)} (planned : ∀ v, v ∉ future → s.plan v = none)
    (nondescendant : ∀ v ∈ head, v ∉ future ∧ ∀ f ∈ future, ¬ G.DirectedWalk f v)
    (treatmentInHead : s.treatment ∈ head) (historyReads : ReadsOnly head s.readHistory)
    (covariateReads : ReadsOnly head s.readCovariate)
    (currentReads : ReadsOnly head s.readCurrent) (a : Source → Noise) :
    s.sample.history a = s.readHistory (s.observed a) ∧
      s.sample.covariate a = s.readCovariate (s.observed a) ∧
      s.sample.selected a = decide (s.observed a s.treatment = s.value) ∧
      s.sample.currentOutcome a = s.readCurrent (s.observed a) :=
  ⟨readout_eq_of_future_plan compatible planned nondescendant historyReads a,
    readout_eq_of_future_plan compatible planned nondescendant covariateReads a,
    readout_eq_of_future_plan compatible planned nondescendant
      (read := fun x => decide (x s.treatment = s.value))
      (fun x x' agree =>
        show decide (x s.treatment = s.value) = decide (x' s.treatment = s.value) by
          rw [agree s.treatment treatmentInHead]) a,
    readout_eq_of_future_plan compatible planned nondescendant currentReads a⟩

/-- Corrected Lemma S.1, aligned observational head marginals. These are the
covariate and outcome invariance inputs of
`SequentialFormula.StageConditions.step_of_sample`. -/
theorem head_conditionals_aligned [DecidableEq H] [DecidableEq Z] [DecidableEq Y]
    [DecidableEq T] [DecidableEq Value] (s : SCMStage n Source Value Noise H Z Y T)
    {G : DAG n} (compatible : ∀ p v, s.model.parent p v → G.edge p v = true)
    {future head : List (Fin n)} (planned : ∀ v, v ∉ future → s.plan v = none)
    (nondescendant : ∀ v ∈ head, v ∉ future ∧ ∀ f ∈ future, ¬ G.DirectedWalk f v)
    (treatmentInHead : s.treatment ∈ head) (historyReads : ReadsOnly head s.readHistory)
    (covariateReads : ReadsOnly head s.readCovariate)
    (currentReads : ReadsOnly head s.readCurrent) :
    (∀ h z, s.observedCovariate h z =
      s.sample.masses.covariate h z / s.sample.masses.history h) ∧
    (∀ h z y, s.observedOutcome h z y =
      s.sample.masses.currentOutcome h z y / s.sample.masses.treatment h z) :=
  head_conditionals_of_head_eq s.sample (fun a => s.readHistory (s.observed a))
    (fun a => s.readCovariate (s.observed a)) (fun a => decide (s.observed a s.treatment = s.value))
    (fun a => s.readCurrent (s.observed a)) fun a _ =>
      s.head_eq_observed compatible planned nondescendant treatmentInHead historyReads
        covariateReads currentReads a

/-- One step of the corrected sufficiency proof for an SCM. Consistency and
the two observational head marginals are proved here. Exchangeability,
positivity, the target identity, the tail identity and the later stages
remain explicit inputs. -/
theorem stage_conditions [DecidableEq H] [DecidableEq Z] [DecidableEq Y] [DecidableEq T]
    [DecidableEq Value] {H' : Type} (s : SCMStage n Source Value Noise H Z Y T)
    {G : DAG n} (compatible : ∀ p v, s.model.parent p v → G.edge p v = true)
    {future head : List (Fin n)} (planned : ∀ v, v ∉ future → s.plan v = none)
    (nondescendant : ∀ v ∈ head, v ∉ future ∧ ∀ f ∈ future, ¬ G.DirectedWalk f v)
    (treatmentInHead : s.treatment ∈ head) (historyReads : ReadsOnly head s.readHistory)
    (covariateReads : ReadsOnly head s.readCovariate)
    (currentReads : ReadsOnly head s.readCurrent)
    {covariates : List Z} {extend : H → Z → Y → H'} {next : Schedule H' T}
    {target : H → Y × T → Rat} {later : H' → T → Rat}
    (distinct : covariates.Nodup)
    (complete : ∀ a ∈ s.sample.atoms, s.sample.covariate a ∈ covariates)
    (target_conditional : ∀ h y t, target h (y, t) =
      eventMass s.sample.atoms s.sample.weight (fun a =>
        decide (s.sample.history a = h ∧ s.sample.potentialOutcome a = (y, t))) /
          s.sample.masses.history h)
    (treatment_positive : ∀ h z, z ∈ covariates → 0 < s.sample.masses.treatment h z)
    (outcome_positive : ∀ h z y, z ∈ covariates → 0 < s.sample.masses.currentOutcome h z y)
    (exchangeable : ∀ h z y t, z ∈ covariates → s.sample.exchangeable h z y t)
    (tail_conditional : ∀ h z y t, z ∈ covariates →
      later (extend h z y) t =
        s.sample.masses.jointOutcome h z y t / s.sample.masses.currentOutcome h z y)
    (remaining : StageConditions next later) :
    StageConditions (.step covariates extend s.observedCovariate s.observedOutcome next)
      target := by
  obtain ⟨covariateAligned, outcomeAligned⟩ := s.head_conditionals_aligned compatible planned
    nondescendant treatmentInHead historyReads covariateReads currentReads
  exact StageConditions.step_of_sample s.sample distinct complete target_conditional
    treatment_positive outcome_positive exchangeable (fun h z _ => covariateAligned h z)
    (fun h z y _ => outcomeAligned h z y) tail_conditional remaining

end SCMStage

end

end OpenCausalScience.Papers.JungEtAl2024.StageGraph
