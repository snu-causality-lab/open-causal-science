module
public import OpenCausalScience.Papers.KimLee2026DFPC.DeductiveCache

/-! # Earlier queries in PC-like skeleton discovery

[Kim and Lee, DF-PC revision](https://www.sanghacklee.me/assets/2026-UAI-dfpc-paper-2026-09-14.pdf),
Proposition 2 and Appendix B. A marginal result is recorded once per
undirected pair. Higher levels run directed-side lists of conditioning
sets and stop at the first independence. The schedule covers all eligible
sets made from neighbors still present at the end of the earlier level.
-/

namespace OpenCausalScience.Papers.KimLee2026DFPC.QueryHistory

open DeductiveCache (Query)

@[expose] public section

variable {n : Nat}

abbrev CIOracle (n : Nat) := Query (Fin n) → Bool
abbrev Log (n : Nat) := List (Query (Fin n) × Bool)

/-- An unoriented CI query identifies swapped endpoints and permutations of
the list representing its conditioning set. -/
def SameCI (a b : Query (Fin n)) : Prop :=
  ((a.left = b.left ∧ a.right = b.right) ∨
    (a.left = b.right ∧ a.right = b.left)) ∧ a.given.Perm b.given

def Records (log : Log n) (q : Query (Fin n)) (independent : Bool) : Prop :=
  ∃ tested, SameCI q tested ∧ (tested, independent) ∈ log

/-- The first output says whether this oriented edge scan found no
independence. The second lists the queries actually performed. -/
def scan (oracle : CIOracle n) (x y : Fin n) : List (List (Fin n)) → Bool × Log n
  | [] => (true, [])
  | s :: tail =>
    let q : Query (Fin n) := ⟨x, y, s⟩
    if oracle q then (false, [(q, true)])
    else
      let later := scan oracle x y tail
      (later.1, (q, false) :: later.2)

theorem scan_survives_iff {oracle : CIOracle n} {x y : Fin n}
    {options : List (List (Fin n))} :
    (scan oracle x y options).1 = true ↔
      ∀ s ∈ options, oracle ⟨x, y, s⟩ = false := by
  induction options with
  | nil => simp [scan]
  | cons s tail ih =>
    cases h : oracle ⟨x, y, s⟩ <;> simp [scan, h, ih]

theorem scan_records_all_of_survives {oracle : CIOracle n} {x y : Fin n}
    {options : List (List (Fin n))} (survives : (scan oracle x y options).1 = true)
    {s : List (Fin n)} (candidate : s ∈ options) :
    (⟨x, y, s⟩, false) ∈ (scan oracle x y options).2 := by
  induction options with
  | nil => simp at candidate
  | cons first tail ih =>
    have dependent := scan_survives_iff.mp survives first List.mem_cons_self
    rw [scan] at survives ⊢
    simp only [dependent, Bool.false_eq_true, ↓reduceIte] at survives ⊢
    rcases List.mem_cons.mp candidate with same | later
    · subst s
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih survives later)

def marginalQuery (x y : Fin n) : Query (Fin n) :=
  if x < y then ⟨x, y, []⟩ else ⟨y, x, []⟩

/-- The complete initial graph yields exactly one query for each distinct
unordered pair at level zero. -/
def marginalHistory (oracle : CIOracle n) : Log n :=
  (List.finRange n).flatMap fun x =>
    ((List.finRange n).filter fun y => decide (x < y)).map fun y =>
      (⟨x, y, []⟩, oracle ⟨x, y, []⟩)

private theorem marginal_mem (oracle : CIOracle n) {x y : Fin n} (order : x < y) :
    (⟨x, y, []⟩, oracle ⟨x, y, []⟩) ∈ marginalHistory oracle := by
  apply List.mem_flatMap.mpr
  refine ⟨x, List.mem_finRange _, List.mem_map.mpr ⟨y, ?_, rfl⟩⟩
  exact List.mem_filter.mpr ⟨List.mem_finRange _, by simp [order]⟩

theorem marginal_recorded (oracle : CIOracle n) {x y : Fin n} (distinct : x ≠ y) :
    Records (marginalHistory oracle) ⟨x, y, []⟩ (oracle (marginalQuery x y)) := by
  refine ⟨marginalQuery x y, ?_, ?_⟩
  by_cases order : x < y
  · simp [SameCI, marginalQuery, order]
  · simp [SameCI, marginalQuery, order]
  by_cases order : x < y
  · simpa [marginalQuery, order] using marginal_mem oracle order
  · have reverse : y < x := by omega
    simpa [marginalQuery, order] using marginal_mem oracle reverse

/-- The graph at the start of each level. Adjacency only decreases.
The candidate list is indexed by the side that supplies the neighbors.
A side skipped by the scheduler has an empty candidate list.
Higher level coverage is required for conditioning sets consisting of
neighbors that remain adjacent even after that level. -/
structure Schedule {n : Nat} (oracle : CIOracle n) where
  adjacent : Nat → Fin n → Fin n → Bool
  initialComplete : ∀ x y, adjacent 0 x y = true ↔ x ≠ y
  symmetric : ∀ level x y, adjacent level x y = adjacent level y x
  noLoops : ∀ level x, adjacent level x x = false
  decreasing : ∀ {earlier later x y}, earlier ≤ later →
    adjacent later x y = true → adjacent earlier x y = true
  marginalStep : ∀ x y, adjacent 1 x y = true ↔
    x ≠ y ∧ oracle (marginalQuery x y) = false
  candidates : Nat → Fin n → Fin n → List (List (Fin n))
  coverage : ∀ {level x y} {s : List (Fin n)}, 0 < level →
    adjacent (level + 1) x y = true → s.Nodup → s.length = level →
    (∀ u ∈ s, u ≠ y ∧ adjacent (level + 1) x u = true) →
    ∃ tested ∈ candidates level x y, s.Perm tested
  survives : ∀ {level x y}, 0 < level → adjacent (level + 1) x y = true →
    (scan oracle x y (candidates level x y)).1 = true

def Schedule.levelHistory {oracle : CIOracle n} (sched : Schedule oracle) (level : Nat) :
    Log n :=
  (List.finRange n).flatMap fun x =>
    ((List.finRange n).filter (sched.adjacent level x)).flatMap fun y =>
      (scan oracle x y (sched.candidates level x y)).2

def Schedule.priorHistory {oracle : CIOracle n} (sched : Schedule oracle) (level : Nat) :
    Log n :=
  (if 0 < level then marginalHistory oracle else []) ++
    ((List.range level).filter fun order => decide (0 < order)).flatMap sched.levelHistory

private theorem marginal_in_prior {oracle : CIOracle n} (sched : Schedule oracle)
    {level : Nat} (positive : 0 < level) {q : Query (Fin n)} {answer : Bool}
    (recorded : Records (marginalHistory oracle) q answer) :
    Records (sched.priorHistory level) q answer := by
  obtain ⟨tested, same, mem⟩ := recorded
  exact ⟨tested, same, List.mem_append_left _ (by simpa [positive] using mem)⟩

private theorem level_in_prior {oracle : CIOracle n} (sched : Schedule oracle)
    {earlier level : Nat} {x y : Fin n} {s : List (Fin n)}
    (positive : 0 < earlier) (before : earlier < level)
    (present : sched.adjacent earlier x y = true)
    (logged : (⟨x, y, s⟩, false) ∈ (scan oracle x y (sched.candidates earlier x y)).2) :
    (⟨x, y, s⟩, false) ∈ sched.priorHistory level := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨earlier, List.mem_filter.mpr ⟨List.mem_range.mpr before, by simp [positive]⟩, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨x, List.mem_finRange _, List.mem_flatMap.mpr ⟨y, ?_, logged⟩⟩
  exact List.mem_filter.mpr ⟨List.mem_finRange _, present⟩

def Schedule.recordsRequired {oracle : CIOracle n} (sched : Schedule oracle)
    (q : Query (Fin n)) : Prop :=
  (∀ ⦃u v : Fin n⦄, u ≠ v →
    Records (sched.priorHistory q.given.length) ⟨u, v, []⟩ (oracle (marginalQuery u v))) ∧
  (∀ ⦃target : Fin n⦄ ⦃s : List (Fin n)⦄,
    target ∈ q.right :: q.given → s.Nodup → s.length < q.given.length →
    (∀ u ∈ s, u ∈ q.right :: q.given ∧ u ≠ target) →
    Records (sched.priorHistory q.given.length) ⟨q.left, target, s⟩ false)

/-- Start-of-level adjacency suffices when the candidate neighborhoods are
frozen, as in PC-stable. In each earlier level the target edge and the edges
to its conditioning vertices survived through the end of that level. -/
theorem required_history_of_frozen_neighbors {oracle : CIOracle n} (sched : Schedule oracle)
    (q : Query (Fin n)) (positive : 0 < q.given.length)
    (edge : sched.adjacent q.given.length q.left q.right = true)
    (neighbors : ∀ u ∈ q.given, sched.adjacent q.given.length q.left u = true) :
    sched.recordsRequired q := by
  constructor
  · intro u v different
    exact marginal_in_prior sched positive (marginal_recorded oracle different)
  · intro target s inNeighborhood nodup earlier subset
    have available : ∀ u ∈ q.right :: q.given,
        sched.adjacent q.given.length q.left u = true := by
      intro u mem
      rcases List.mem_cons.mp mem with same | tail
      · exact same ▸ edge
      · exact neighbors u tail
    have afterLevel : sched.adjacent (s.length + 1) q.left target = true :=
      sched.decreasing (by omega) (available target inNeighborhood)
    by_cases empty : s = []
    · subst s
      have marginal := (sched.marginalStep q.left target).mp afterLevel
      exact marginal_in_prior sched positive (marginal.2 ▸ marginal_recorded oracle marginal.1)
    · have higher : 0 < s.length := by cases s <;> simp_all
      have neighborsAfter : ∀ u ∈ s,
          u ≠ target ∧ sched.adjacent (s.length + 1) q.left u = true := by
        intro u mem
        obtain ⟨inNeighborhood, distinct⟩ := subset u mem
        exact ⟨distinct, sched.decreasing (by omega) (available u inNeighborhood)⟩
      obtain ⟨tested, candidate, permutation⟩ :=
        sched.coverage higher afterLevel nodup rfl neighborsAfter
      have kept := sched.survives higher afterLevel
      have logged := scan_records_all_of_survives kept candidate
      have beforeLevel := sched.decreasing (Nat.le_succ _) afterLevel
      exact ⟨⟨q.left, target, tested⟩, ⟨Or.inl ⟨rfl, rfl⟩, permutation⟩,
        level_in_prior sched higher earlier beforeLevel logged⟩

/-- Proposition 2 for a query whose target edge and all the tested side's
conditioning neighbors are still adjacent at the time of the query. -/
theorem required_history_at_query {oracle : CIOracle n} (sched : Schedule oracle)
    (q : Query (Fin n)) (positive : 0 < q.given.length)
    (adjacentNow : Fin n → Fin n → Bool)
    (startedWith : ∀ x y, adjacentNow x y = true →
      sched.adjacent q.given.length x y = true)
    (edge : adjacentNow q.left q.right = true)
    (neighbors : ∀ u ∈ q.given, adjacentNow q.left u = true) :
    sched.recordsRequired q :=
  required_history_of_frozen_neighbors sched q positive (startedWith _ _ edge)
    (fun u mem => startedWith _ _ (neighbors u mem))

end

end OpenCausalScience.Papers.KimLee2026DFPC.QueryHistory
