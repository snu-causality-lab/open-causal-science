module
public import OpenCausalScience.Papers.KimLee2026DFPC.QueryHistory

/-! # A level-wise early-stopping schedule for Proposition 2

[Kim and Lee, DF-PC revision](https://www.sanghacklee.me/assets/2026-UAI-dfpc-paper-2026-09-14.pdf),
Definition 1, Proposition 2, Algorithm 2 (lines 5–12) and Appendix B, with the
skeleton loop of `PCStable.run` with `early_stopping=True` in the
[published code](https://github.com/snu-causality-lab/DF-PC/commit/b1c320027b7a8be8b31a2b751f51135fcb3e8c34).

`adjacency oracle level` is the skeleton at the start of `level`. Level zero
uses the canonical marginal query of `QueryHistory`. At a positive level each
ordered adjacent pair `(x, y)` scans every `level`-element subset of the
neighborhood `adj(x) \ {y}` frozen at the start of the level, each subset listed
once in `combinations` order, and stops at its first independence. An edge is
removed at the end of the level when either ordered side found an independence.
`schedule` fills every field of `QueryHistory.Schedule` from these definitions.

The published loop also tests both ordered sides at level zero.
`orderedAdjacency` uses that two-sided step at every level. By
`ordered_adjacency_eq`, both constructions give the same skeleton at every level
when the oracle gives `x ⊥ y` and `y ⊥ x` the same answer.
`marginal_symmetric_of_exact` derives this from an exact oracle for a symmetric
independence relation. A test whose answer depends on the argument order can
remove an edge in the published loop that the canonical marginal keeps.

This module does not reproduce the order of the published conditioning sets, the
transcripts, or the counters. Survival at each level does not depend on the
order of a candidate list (`QueryHistory.scan_survives_iff`), but an early-stopping
transcript does.
-/

namespace OpenCausalScience.Papers.KimLee2026DFPC.StableSchedule

open DeductiveCache (Query)
open QueryHistory

@[expose] public section

variable {n : Nat}

/-- All `k`-element sublists, in the order of Python's `itertools.combinations`. -/
def combinations {α : Type} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, a :: rest => (combinations k rest).map (a :: ·) ++ combinations (k + 1) rest

theorem combinations_sublist {α : Type} {k : Nat} {l c : List α}
    (mem : c ∈ combinations k l) : c.Sublist l := by
  induction l generalizing k c with
  | nil =>
    cases k with
    | zero =>
      simp only [combinations, List.mem_singleton] at mem
      subst mem
      exact List.Sublist.slnil
    | succ _ => simp [combinations] at mem
  | cons a rest ih =>
    cases k with
    | zero =>
      simp only [combinations, List.mem_singleton] at mem
      subst mem
      exact List.nil_sublist _
    | succ k =>
      simp only [combinations, List.mem_append, List.mem_map] at mem
      rcases mem with ⟨tail, tailMem, rfl⟩ | later
      · exact List.Sublist.cons_cons a (ih tailMem)
      · exact List.Sublist.cons a (ih later)

theorem combinations_length {α : Type} {k : Nat} {l c : List α}
    (mem : c ∈ combinations k l) : c.length = k := by
  induction l generalizing k c with
  | nil =>
    cases k with
    | zero =>
      simp only [combinations, List.mem_singleton] at mem
      subst mem
      rfl
    | succ _ => simp [combinations] at mem
  | cons a rest ih =>
    cases k with
    | zero =>
      simp only [combinations, List.mem_singleton] at mem
      subst mem
      rfl
    | succ k =>
      simp only [combinations, List.mem_append, List.mem_map] at mem
      rcases mem with ⟨tail, tailMem, rfl⟩ | later
      · simp [ih tailMem]
      · exact ih later

/-- Every duplicate-free `k`-element list drawn from `l` occurs up to permutation. -/
theorem exists_perm_mem_combinations {α : Type} [DecidableEq α] {k : Nat} {l s : List α}
    (nodup : s.Nodup) (size : s.length = k) (within : ∀ u ∈ s, u ∈ l) :
    ∃ c ∈ combinations k l, s.Perm c := by
  induction l generalizing k s with
  | nil =>
    cases s with
    | nil =>
      subst size
      exact ⟨[], by simp [combinations], List.Perm.refl _⟩
    | cons u _ => exact absurd (within u List.mem_cons_self) (by simp)
  | cons a rest ih =>
    cases k with
    | zero =>
      have empty : s = [] := List.eq_nil_of_length_eq_zero size
      subst empty
      exact ⟨[], by simp [combinations], List.Perm.refl _⟩
    | succ k =>
      by_cases present : a ∈ s
      · have restSize : (s.erase a).length = k := by
          have shorter := List.length_erase_of_mem present
          omega
        have restWithin : ∀ u ∈ s.erase a, u ∈ rest := by
          intro u mem
          have different : u ≠ a := by
            rintro rfl
            exact nodup.not_mem_erase mem
          rcases List.mem_cons.mp (within u (List.mem_of_mem_erase mem)) with same | later
          · exact absurd same different
          · exact later
        obtain ⟨c, mem, perm⟩ := ih (nodup.erase a) restSize restWithin
        refine ⟨a :: c, ?_, (List.perm_cons_erase present).trans (perm.cons a)⟩
        simp only [combinations, List.mem_append, List.mem_map]
        exact Or.inl ⟨c, mem, rfl⟩
      · have restWithin : ∀ u ∈ s, u ∈ rest := by
          intro u mem
          rcases List.mem_cons.mp (within u mem) with same | later
          · subst same
            exact absurd mem present
          · exact later
        obtain ⟨c, mem, perm⟩ := ih nodup size restWithin
        refine ⟨c, ?_, perm⟩
        simp only [combinations, List.mem_append]
        exact Or.inr mem

/-- Neighbors of `x` other than `y`, in index order. -/
def pool (adj : Fin n → Fin n → Bool) (x y : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun u => adj x u && decide (u ≠ y)

theorem mem_pool {adj : Fin n → Fin n → Bool} {x y u : Fin n} :
    u ∈ pool adj x y ↔ adj x u = true ∧ u ≠ y := by
  simp [pool]

/-- Conditioning sets for the ordered side `(x, y)` drawn from the frozen `adj`. -/
def candidateSets (adj : Fin n → Fin n → Bool) (level : Nat) (x y : Fin n) :
    List (List (Fin n)) :=
  combinations level (pool adj x y)

theorem candidateSets_zero (adj : Fin n → Fin n → Bool) (x y : Fin n) :
    candidateSets adj 0 x y = [[]] := by
  simp [candidateSets, combinations]

/-- Both ordered sides scan against the same frozen `adj`. The edge is removed
after the level if either side found an independence. -/
def nextAdjacency (oracle : CIOracle n) (adj : Fin n → Fin n → Bool) (level : Nat)
    (x y : Fin n) : Bool :=
  adj x y && (scan oracle x y (candidateSets adj level x y)).1 &&
    (scan oracle y x (candidateSets adj level y x)).1

/-- Level zero recorded once per unordered pair, as in `QueryHistory.marginalHistory`. -/
def marginalAdjacency (oracle : CIOracle n) (x y : Fin n) : Bool :=
  decide (x ≠ y) && !oracle (marginalQuery x y)

/-- The skeleton at the start of each level. -/
def adjacency (oracle : CIOracle n) : Nat → Fin n → Fin n → Bool
  | 0 => fun x y => decide (x ≠ y)
  | level + 1 =>
    if level = 0 then marginalAdjacency oracle
    else nextAdjacency oracle (adjacency oracle level) level

theorem adjacency_zero (oracle : CIOracle n) (x y : Fin n) :
    adjacency oracle 0 x y = decide (x ≠ y) := rfl

theorem adjacency_one (oracle : CIOracle n) :
    adjacency oracle 1 = marginalAdjacency oracle := rfl

theorem adjacency_succ (oracle : CIOracle n) {level : Nat} (positive : 0 < level) :
    adjacency oracle (level + 1) = nextAdjacency oracle (adjacency oracle level) level := by
  rw [adjacency, ite_eq_right (show level ≠ 0 by omega)]

theorem adjacency_of_succ (oracle : CIOracle n) {level : Nat} {x y : Fin n}
    (present : adjacency oracle (level + 1) x y = true) :
    adjacency oracle level x y = true := by
  rcases Nat.eq_zero_or_pos level with zero | positive
  · subst zero
    change marginalAdjacency oracle x y = true at present
    simp only [marginalAdjacency, Bool.and_eq_true] at present
    rw [adjacency_zero]
    exact present.1
  · rw [adjacency_succ oracle positive] at present
    simp only [nextAdjacency, Bool.and_eq_true] at present
    exact present.1.1

theorem adjacency_of_add (oracle : CIOracle n) {earlier : Nat} {x y : Fin n} (gap : Nat)
    (present : adjacency oracle (earlier + gap) x y = true) :
    adjacency oracle earlier x y = true := by
  induction gap with
  | zero => exact present
  | succ gap ih => exact ih (adjacency_of_succ oracle (level := earlier + gap) present)

/-- Edges are only removed. -/
theorem adjacency_mono (oracle : CIOracle n) {earlier later : Nat} {x y : Fin n}
    (le : earlier ≤ later) (present : adjacency oracle later x y = true) :
    adjacency oracle earlier x y = true := by
  have split : later = earlier + (later - earlier) := by omega
  rw [split] at present
  exact adjacency_of_add oracle (later - earlier) present

theorem adjacency_irrefl (oracle : CIOracle n) (level : Nat) (x : Fin n) :
    adjacency oracle level x x = false := by
  cases present : adjacency oracle level x x with
  | false => rfl
  | true =>
    have initial := adjacency_mono oracle (Nat.zero_le level) present
    rw [adjacency_zero] at initial
    exact (of_decide_eq_true initial rfl).elim

theorem marginalQuery_comm {x y : Fin n} (distinct : x ≠ y) :
    marginalQuery x y = marginalQuery y x := by
  by_cases order : x < y
  · have reverse : ¬ y < x := by omega
    rw [marginalQuery, marginalQuery, ite_eq_left order, ite_eq_right reverse]
  · have reverse : y < x := by omega
    rw [marginalQuery, marginalQuery, ite_eq_right order, ite_eq_left reverse]

theorem nextAdjacency_symm (oracle : CIOracle n) {adj : Fin n → Fin n → Bool}
    (symm : ∀ x y, adj x y = adj y x) (level : Nat) (x y : Fin n) :
    nextAdjacency oracle adj level x y = nextAdjacency oracle adj level y x := by
  unfold nextAdjacency
  rw [symm x y]
  generalize adj y x = edge
  generalize (scan oracle x y (candidateSets adj level x y)).1 = forward
  generalize (scan oracle y x (candidateSets adj level y x)).1 = backward
  cases edge <;> cases forward <;> cases backward <;> rfl

theorem adjacency_symm (oracle : CIOracle n) (level : Nat) :
    ∀ x y : Fin n, adjacency oracle level x y = adjacency oracle level y x := by
  induction level with
  | zero =>
    intro x y
    rw [adjacency_zero, adjacency_zero]
    by_cases same : x = y
    · subst same
      rfl
    · rw [decide_eq_true (show x ≠ y from same), decide_eq_true (show y ≠ x from Ne.symm same)]
  | succ level ih =>
    intro x y
    rcases Nat.eq_zero_or_pos level with zero | positive
    · subst zero
      change marginalAdjacency oracle x y = marginalAdjacency oracle y x
      by_cases same : x = y
      · subst same
        rfl
      · unfold marginalAdjacency
        rw [marginalQuery_comm same, decide_eq_true (show x ≠ y from same),
          decide_eq_true (show y ≠ x from Ne.symm same)]
    · rw [adjacency_succ oracle positive]
      exact nextAdjacency_symm oracle ih level x y

theorem marginal_step (oracle : CIOracle n) (x y : Fin n) :
    adjacency oracle 1 x y = true ↔ x ≠ y ∧ oracle (marginalQuery x y) = false := by
  rw [adjacency_one]
  simp [marginalAdjacency]

/-- Candidate completeness, derived from the frozen neighborhoods. -/
theorem coverage_of_survivors (oracle : CIOracle n) {level : Nat} {x y : Fin n}
    {s : List (Fin n)} (nodup : s.Nodup) (size : s.length = level)
    (neighbors : ∀ u ∈ s, u ≠ y ∧ adjacency oracle (level + 1) x u = true) :
    ∃ tested ∈ candidateSets (adjacency oracle level) level x y, s.Perm tested := by
  apply exists_perm_mem_combinations nodup size
  intro u mem
  obtain ⟨distinct, present⟩ := neighbors u mem
  exact mem_pool.mpr ⟨adjacency_of_succ oracle present, distinct⟩

/-- A surviving edge found no independence on the side that supplies the neighbors. -/
theorem survives_of_next (oracle : CIOracle n) {level : Nat} {x y : Fin n}
    (positive : 0 < level) (present : adjacency oracle (level + 1) x y = true) :
    (scan oracle x y (candidateSets (adjacency oracle level) level x y)).1 = true := by
  rw [adjacency_succ oracle positive] at present
  simp only [nextAdjacency, Bool.and_eq_true] at present
  exact present.1.2

/-- Every field of the abstract schedule is derived from the concrete scheduler. -/
def schedule (oracle : CIOracle n) : Schedule oracle where
  adjacent := adjacency oracle
  initialComplete x y := by
    rw [adjacency_zero]
    exact ⟨of_decide_eq_true, decide_eq_true⟩
  symmetric := adjacency_symm oracle
  noLoops := adjacency_irrefl oracle
  decreasing := adjacency_mono oracle
  marginalStep := marginal_step oracle
  candidates level := candidateSets (adjacency oracle level) level
  coverage := fun _ _ nodup size neighbors => coverage_of_survivors oracle nodup size neighbors
  survives := fun positive present => survives_of_next oracle positive present

/-- A scan logs only the queries of its candidate list, with the oracle's answers. -/
theorem scan_logged {oracle : CIOracle n} {x y : Fin n} {q : Query (Fin n)} {answer : Bool}
    {options : List (List (Fin n))} (logged : (q, answer) ∈ (scan oracle x y options).2) :
    ∃ s ∈ options, q = ⟨x, y, s⟩ ∧ answer = oracle ⟨x, y, s⟩ := by
  induction options with
  | nil => simp [scan] at logged
  | cons s tail ih =>
    cases hit : oracle ⟨x, y, s⟩ with
    | true =>
      simp only [scan, hit, ↓reduceIte, List.mem_singleton, Prod.mk.injEq] at logged
      exact ⟨s, List.mem_cons_self, logged.1, logged.2.trans hit.symm⟩
    | false =>
      simp only [scan, hit, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
        Prod.mk.injEq] at logged
      rcases logged with ⟨same, answered⟩ | later
      · exact ⟨s, List.mem_cons_self, same, answered.trans hit.symm⟩
      · obtain ⟨t, mem, same, answered⟩ := ih later
        exact ⟨t, List.mem_cons_of_mem _ mem, same, answered⟩

/-- A scheduled query has distinct endpoints outside a duplicate-free conditioning set. -/
theorem candidate_valid (oracle : CIOracle n) {level : Nat} {x y : Fin n}
    (edge : adjacency oracle level x y = true) {s : List (Fin n)}
    (posed : s ∈ candidateSets (adjacency oracle level) level x y) :
    (⟨x, y, s⟩ : Query (Fin n)).Valid := by
  have inPool : ∀ u ∈ s, u ∈ pool (adjacency oracle level) x y :=
    fun u mem => (combinations_sublist posed).subset mem
  show x ≠ y ∧ x ∉ s ∧ y ∉ s ∧ s.Nodup
  refine ⟨fun same => ?_, fun mem => ?_, fun mem => ?_, ?_⟩
  · subst same
    simp [adjacency_irrefl] at edge
  · have loop := (mem_pool.mp (inPool x mem)).1
    simp [adjacency_irrefl] at loop
  · exact (mem_pool.mp (inPool y mem)).2 rfl
  · exact List.Sublist.nodup ((combinations_sublist posed).trans List.filter_sublist)
      (List.nodup_finRange n)

/-- Proposition 2 for a query posed by the concrete scheduler at a positive level.
Its conditioning set consists of frozen neighbors of `x`, so
`required_history_of_frozen_neighbors` applies without further premises. -/
theorem scheduled_query_required_history (oracle : CIOracle n) {level : Nat}
    (positive : 0 < level) {x y : Fin n} (edge : adjacency oracle level x y = true)
    {s : List (Fin n)} (posed : s ∈ candidateSets (adjacency oracle level) level x y) :
    (schedule oracle).recordsRequired ⟨x, y, s⟩ := by
  have size : s.length = level := combinations_length posed
  have neighbors : ∀ u ∈ s, adjacency oracle level x u = true := fun u mem =>
    (mem_pool.mp ((combinations_sublist posed).subset mem)).1
  subst size
  exact required_history_of_frozen_neighbors (schedule oracle) ⟨x, y, s⟩ positive edge neighbors

/-- Proposition 2 for every query the scheduler performs at a positive level. -/
theorem logged_query_required_history (oracle : CIOracle n) {level : Nat}
    (positive : 0 < level) {q : Query (Fin n)} {answer : Bool}
    (logged : (q, answer) ∈ (schedule oracle).levelHistory level) :
    (schedule oracle).recordsRequired q ∧ q.Valid ∧ answer = oracle q := by
  unfold Schedule.levelHistory at logged
  obtain ⟨x, _, inner⟩ := List.mem_flatMap.mp logged
  obtain ⟨y, edgeMem, scanned⟩ := List.mem_flatMap.mp inner
  have edge : adjacency oracle level x y = true := (List.mem_filter.mp edgeMem).2
  obtain ⟨s, posed, rfl, answered⟩ := scan_logged scanned
  exact ⟨scheduled_query_required_history oracle positive edge posed,
    candidate_valid oracle edge posed, answered⟩

/-- Both ordered marginal tests of a pair return the same answer. -/
def MarginalSymmetric (oracle : CIOracle n) : Prop :=
  ∀ x y : Fin n, x ≠ y → oracle ⟨x, y, []⟩ = oracle ⟨y, x, []⟩

theorem marginal_valid {x y : Fin n} (distinct : x ≠ y) :
    (⟨x, y, []⟩ : Query (Fin n)).Valid :=
  ⟨distinct, by simp, by simp, by simp⟩

/-- An exact oracle for an independence relation that is symmetric on marginal
queries answers both ordered sides identically. -/
theorem marginal_symmetric_of_exact {independent : Query (Fin n) → Prop}
    {oracle : CIOracle n} (exactOracle : DeductiveCache.OracleExact independent oracle)
    (swap : ∀ x y : Fin n, independent ⟨x, y, []⟩ → independent ⟨y, x, []⟩) :
    MarginalSymmetric oracle := by
  intro x y distinct
  have forward := exactOracle ⟨x, y, []⟩ (marginal_valid distinct)
  have backward := exactOracle ⟨y, x, []⟩ (marginal_valid (Ne.symm distinct))
  cases hxy : oracle ⟨x, y, []⟩ <;> cases hyx : oracle ⟨y, x, []⟩
  · rfl
  · exact absurd (forward.mpr (swap y x (backward.mp hyx))) (by simp [hxy])
  · exact absurd (backward.mpr (swap x y (forward.mp hxy))) (by simp [hyx])
  · rfl

theorem oracle_marginalQuery (oracle : CIOracle n) (symmetric : MarginalSymmetric oracle)
    {x y : Fin n} (distinct : x ≠ y) : oracle (marginalQuery x y) = oracle ⟨x, y, []⟩ := by
  by_cases order : x < y
  · rw [marginalQuery, ite_eq_left order]
  · rw [marginalQuery, ite_eq_right order]
    exact (symmetric x y distinct).symm

/-- The canonical marginal history records each ordered marginal answer. -/
theorem ordered_marginal_recorded (oracle : CIOracle n) (symmetric : MarginalSymmetric oracle)
    {x y : Fin n} (distinct : x ≠ y) :
    Records (marginalHistory oracle) ⟨x, y, []⟩ (oracle ⟨x, y, []⟩) := by
  rw [← oracle_marginalQuery oracle symmetric distinct]
  exact marginal_recorded oracle distinct

theorem scan_single (oracle : CIOracle n) (x y : Fin n) (s : List (Fin n)) :
    (scan oracle x y [s]).1 = !oracle ⟨x, y, s⟩ := by
  cases hit : oracle ⟨x, y, s⟩ <;> simp [scan, hit]

/-- The published loop's skeletons, which also scan level zero on both ordered sides. -/
def orderedAdjacency (oracle : CIOracle n) : Nat → Fin n → Fin n → Bool
  | 0 => fun x y => decide (x ≠ y)
  | level + 1 => nextAdjacency oracle (orderedAdjacency oracle level) level

theorem ordered_marginal_step (oracle : CIOracle n) (symmetric : MarginalSymmetric oracle)
    (x y : Fin n) :
    nextAdjacency oracle (fun u v => decide (u ≠ v)) 0 x y = marginalAdjacency oracle x y := by
  simp only [nextAdjacency, marginalAdjacency]
  rw [candidateSets_zero, candidateSets_zero, scan_single, scan_single]
  by_cases same : x = y
  · subst same
    simp
  · rw [oracle_marginalQuery oracle symmetric same, ← symmetric x y same,
      decide_eq_true (show x ≠ y from same)]
    generalize oracle ⟨x, y, []⟩ = answer
    cases answer <;> rfl

/-- Collapsing the two ordered marginal tests leaves every level's skeleton unchanged. -/
theorem ordered_adjacency_eq (oracle : CIOracle n) (symmetric : MarginalSymmetric oracle)
    (level : Nat) : orderedAdjacency oracle level = adjacency oracle level := by
  induction level with
  | zero => rfl
  | succ level ih =>
    rcases Nat.eq_zero_or_pos level with zero | positive
    · subst zero
      funext x y
      exact ordered_marginal_step oracle symmetric x y
    · show nextAdjacency oracle (orderedAdjacency oracle level) level = adjacency oracle (level + 1)
      rw [adjacency_succ oracle positive, ih]

/-- `levelHistory 0` is the two-sided marginal transcript. Each entry is recorded
by the canonical marginal history up to swapped endpoints. -/
theorem ordered_marginal_logged_recorded (oracle : CIOracle n)
    (symmetric : MarginalSymmetric oracle) {q : Query (Fin n)} {answer : Bool}
    (logged : (q, answer) ∈ (schedule oracle).levelHistory 0) :
    Records (marginalHistory oracle) q answer := by
  unfold Schedule.levelHistory at logged
  obtain ⟨x, _, inner⟩ := List.mem_flatMap.mp logged
  obtain ⟨y, edgeMem, scanned⟩ := List.mem_flatMap.mp inner
  have edge : adjacency oracle 0 x y = true := (List.mem_filter.mp edgeMem).2
  rw [adjacency_zero] at edge
  obtain ⟨s, posed, rfl, rfl⟩ := scan_logged scanned
  have empty : s = [] := by
    have listed : s ∈ candidateSets (adjacency oracle 0) 0 x y := posed
    rw [candidateSets_zero] at listed
    simpa using listed
  subst empty
  exact ordered_marginal_recorded oracle symmetric (of_decide_eq_true edge)

theorem filter_length_succ_le {α : Type} {p : α → Bool} {b : α} {l : List α}
    (mem : b ∈ l) (rejected : p b = false) : (l.filter p).length + 1 ≤ l.length := by
  induction l with
  | nil => simp at mem
  | cons c rest ih =>
    have bound : (rest.filter p).length ≤ rest.length := List.filter_sublist.length_le
    rcases List.mem_cons.mp mem with same | later
    · subst same
      simp only [List.filter, rejected, List.length_cons]
      omega
    · have shorter := ih later
      cases keep : p c <;> simp only [List.filter, keep, List.length_cons] <;> omega

theorem filter_length_add_two_le {α : Type} {p : α → Bool} {a b : α} (distinct : a ≠ b)
    {l : List α} (memA : a ∈ l) (memB : b ∈ l) (rejectA : p a = false)
    (rejectB : p b = false) : (l.filter p).length + 2 ≤ l.length := by
  induction l with
  | nil => simp at memA
  | cons c rest ih =>
    by_cases isA : a = c
    · subst isA
      have restB : b ∈ rest := by
        rcases List.mem_cons.mp memB with same | later
        · exact absurd same.symm distinct
        · exact later
      have shorter := filter_length_succ_le restB rejectB
      simp only [List.filter, rejectA, List.length_cons]
      omega
    · by_cases isB : b = c
      · subst isB
        have restA : a ∈ rest := by
          rcases List.mem_cons.mp memA with same | later
          · exact absurd same isA
          · exact later
        have shorter := filter_length_succ_le restA rejectA
        simp only [List.filter, rejectB, List.length_cons]
        omega
      · have restA : a ∈ rest := (List.mem_cons.mp memA).resolve_left isA
        have restB : b ∈ rest := (List.mem_cons.mp memB).resolve_left isB
        have shorter := ih restA restB
        cases keep : p c <;> simp only [List.filter, keep, List.length_cons] <;> omega

theorem pool_length_add_two_le (oracle : CIOracle n) {level : Nat} {x y : Fin n}
    (distinct : x ≠ y) : (pool (adjacency oracle level) x y).length + 2 ≤ n := by
  have bound := filter_length_add_two_le
    (p := fun u => adjacency oracle level x u && decide (u ≠ y)) distinct
    (List.mem_finRange x) (List.mem_finRange y) (by simp [adjacency_irrefl]) (by simp)
  rw [List.length_finRange] at bound
  exact bound

theorem combinations_eq_nil {α : Type} {k : Nat} {l : List α} (short : l.length < k) :
    combinations k l = [] := by
  induction l generalizing k with
  | nil =>
    cases k with
    | zero => simp at short
    | succ _ => simp [combinations]
  | cons a rest ih =>
    cases k with
    | zero => simp at short
    | succ k =>
      simp only [List.length_cons] at short
      simp [combinations, ih (show rest.length < k by omega),
        ih (show rest.length < k + 1 by omega)]

/-- From level `n - 1` on no conditioning set is left for a pair of distinct vertices. -/
theorem candidates_eq_nil (oracle : CIOracle n) {level : Nat} {x y : Fin n}
    (large : n ≤ level + 1) (distinct : x ≠ y) :
    candidateSets (adjacency oracle level) level x y = [] := by
  have bound := pool_length_add_two_le oracle (level := level) distinct
  exact combinations_eq_nil (by omega)

/-- The published loop's last level is `n - 2`. Later levels change nothing. -/
theorem adjacency_stable (oracle : CIOracle n) {level : Nat} (positive : 0 < level)
    (large : n ≤ level + 1) : adjacency oracle (level + 1) = adjacency oracle level := by
  funext x y
  rw [adjacency_succ oracle positive]
  unfold nextAdjacency
  by_cases same : x = y
  · subst same
    simp [adjacency_irrefl]
  · rw [candidates_eq_nil oracle large same, candidates_eq_nil oracle large (Ne.symm same)]
    simp [scan]

/-- No query is performed from level `n - 1` on. -/
theorem levelHistory_large (oracle : CIOracle n) {level : Nat} (large : n ≤ level + 1)
    (q : Query (Fin n)) (answer : Bool) :
    (q, answer) ∉ (schedule oracle).levelHistory level := by
  intro logged
  unfold Schedule.levelHistory at logged
  obtain ⟨x, _, inner⟩ := List.mem_flatMap.mp logged
  obtain ⟨y, edgeMem, scanned⟩ := List.mem_flatMap.mp inner
  have edge : adjacency oracle level x y = true := (List.mem_filter.mp edgeMem).2
  have distinct : x ≠ y := by
    rintro rfl
    simp [adjacency_irrefl] at edge
  obtain ⟨s, posed, _, _⟩ := scan_logged scanned
  have listed : s ∈ candidateSets (adjacency oracle level) level x y := posed
  rw [candidates_eq_nil oracle large distinct] at listed
  simp at listed

end

end OpenCausalScience.Papers.KimLee2026DFPC.StableSchedule
