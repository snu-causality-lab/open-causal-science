module
public import Std

@[expose] public section

/-! Finite candidate-pair deletion for the adjacency phase of a relational
causal discovery algorithm. The two directions can have different perspectives. -/

namespace RelationalFiniteSearch

universe u v

structure Query (D : Type u) (V : Type v) where
  source : D → V
  target : D → V
  reverse : D → D
  independent : D → List V → Bool

variable {D : Type u} {V : Type v} [DecidableEq D] [DecidableEq V]

def eligible (q : Query D V) (d c : D) : Bool :=
  decide (q.target c = q.target d ∧ q.source c ≠ q.source d)

def conditioningLists : List D → List (List D)
  | [] => [[]]
  | c :: cs => conditioningLists cs ++ (conditioningLists cs).map (c :: ·)

omit [DecidableEq D] in
theorem mem_conditioningLists {s cs : List D} :
    s ∈ conditioningLists cs ↔ s.Sublist cs := by
  induction cs generalizing s with
  | nil => simp [conditioningLists]
  | cons c cs ih =>
    simp only [conditioningLists, List.mem_append, List.mem_map, ih]
    constructor
    · rintro (prior | ⟨tail, prior, rfl⟩)
      · exact prior.cons c
      · exact prior.cons_cons c
    · intro sub
      cases sub with
      | cons _ prior => exact .inl prior
      | cons_cons _ prior => exact .inr ⟨_, prior, rfl⟩

def findSeparator (q : Query D V) (depth : Nat) (current : List D) (d : D) : Bool :=
  (conditioningLists (current.filter (eligible q d))).any
    fun s => (s.length == depth) && q.independent d (s.map q.source)

omit [DecidableEq D] in
theorem separator_iff (q : Query D V) (depth : Nat) (current : List D) (d : D) :
    findSeparator q depth current d = true ↔
      ∃ s : List D, s.Sublist (current.filter (eligible q d)) ∧
        s.length = depth ∧ q.independent d (s.map q.source) = true := by
  simp [findSeparator, List.any_eq_true, mem_conditioningLists]

omit [DecidableEq D] in
private theorem separator_mono {q : Query D V} {depth : Nat} {small large : List D} {d : D}
    (sub : small.Sublist large) (found : findSeparator q depth small d = true) :
    findSeparator q depth large d = true := by
  obtain ⟨s, inside, size, ci⟩ := (separator_iff q depth small d).mp found
  exact (separator_iff q depth large d).mpr ⟨s, inside.trans (sub.filter _), size, ci⟩

def deletePair (q : Query D V) (d : D) (current : List D) : List D :=
  current.filter fun c => decide (c ≠ d ∧ c ≠ q.reverse d)

def test (q : Query D V) (depth : Nat) (d : D) (current : List D) : List D :=
  if d ∈ current ∧ findSeparator q depth current d = true then
    deletePair q d current
  else current

def sweep (q : Query D V) (depth : Nat) (schedule : List D) (current : List D) : List D :=
  schedule.foldl (fun active d => test q depth d active) current

/-- The sweep visits all candidates still present at the start of a level.
Each visit searches in the current, possibly smaller parent sets. -/
def search (q : Query D V) (initial : List D) : Nat → List D
  | 0 => initial
  | depth + 1 =>
    let current := search q initial depth
    sweep q depth current current

private theorem test_sublist (q : Query D V) (depth : Nat) (d : D) (current : List D) :
    (test q depth d current).Sublist current := by
  unfold test
  split
  · exact List.filter_sublist
  · exact List.Sublist.refl _

private theorem sweep_sublist (q : Query D V) (depth : Nat) (schedule current : List D) :
    (sweep q depth schedule current).Sublist current := by
  induction schedule generalizing current with
  | nil => exact List.Sublist.refl _
  | cons d pending ih => exact (ih (test q depth d current)).trans (test_sublist q depth d current)

theorem search_sublist (q : Query D V) (initial : List D) {i j : Nat} (le : i ≤ j) :
    (search q initial j).Sublist (search q initial i) := by
  induction le with
  | refl => exact List.Sublist.refl _
  | step _ ih => exact (sweep_sublist q _ _ _).trans ih

def pairPresent (q : Query D V) (truth : D → Bool) (d : D) : Prop :=
  truth d = true ∨ truth (q.reverse d) = true

def PairClosed (q : Query D V) (current : List D) : Prop :=
  ∀ d ∈ current, q.reverse d ∈ current

private theorem test_closed (q : Query D V) (invol : ∀ d, q.reverse (q.reverse d) = d)
    (depth : Nat) (d : D) (current : List D) (closed : PairClosed q current) :
    PairClosed q (test q depth d current) := by
  unfold test
  split
  · intro c kept
    obtain ⟨mem, survives⟩ := List.mem_filter.mp kept
    obtain ⟨ne, neRev⟩ : c ≠ d ∧ c ≠ q.reverse d := of_decide_eq_true survives
    apply List.mem_filter.mpr
    refine ⟨closed c mem, ?_⟩
    simp only [decide_eq_true_eq]
    constructor
    · intro eq
      exact neRev (by rw [← eq, invol])
    · intro eq
      exact ne (by simpa only [invol] using congrArg q.reverse eq)
  · exact closed

private theorem sweep_closed (q : Query D V) (invol : ∀ d, q.reverse (q.reverse d) = d)
    (depth : Nat) (schedule current : List D) (closed : PairClosed q current) :
    PairClosed q (sweep q depth schedule current) := by
  induction schedule generalizing current with
  | nil => exact closed
  | cons d pending ih => exact ih _ (test_closed q invol depth d current closed)

theorem search_closed (q : Query D V) (invol : ∀ d, q.reverse (q.reverse d) = d)
    (initial : List D) (closed : PairClosed q initial) (levels : Nat) :
    PairClosed q (search q initial levels) := by
  induction levels with
  | zero => exact closed
  | succ n ih => exact sweep_closed q invol n _ _ ih

private theorem sweep_exhausted (q : Query D V) (depth : Nat) (schedule current : List D)
    {d : D} (planned : d ∈ schedule) (retained : d ∈ sweep q depth schedule current) :
    findSeparator q depth (sweep q depth schedule current) d = false := by
  induction schedule generalizing current with
  | nil => simp at planned
  | cons head tail ih =>
    rcases List.mem_cons.mp planned with rfl | pending
    · refine Bool.eq_false_iff.mpr ?_
      intro found
      have before := (sweep_sublist q depth (d :: tail) current).subset retained
      have atVisit := separator_mono (sweep_sublist q depth (d :: tail) current) found
      have after := (sweep_sublist q depth tail (test q depth d current)).subset retained
      rw [test, ite_eq_left ⟨before, atVisit⟩] at after
      simp [deletePair] at after
    · exact ih (test q depth head current) pending retained

omit [DecidableEq D] in
private theorem eligible_conditions_valid {q : Query D V} {current : List D} {d : D}
    {s : List D} (sub : s.Sublist (current.filter (eligible q d)))
    (valid : ∀ c ∈ current, q.source c ≠ q.target c) :
    q.source d ∉ s.map q.source ∧ q.target d ∉ s.map q.source := by
  constructor
  · intro endpoint
    obtain ⟨c, mem, same⟩ := List.mem_map.mp endpoint
    exact (of_decide_eq_true (List.mem_filter.mp (sub.subset mem)).2).2 same
  · intro endpoint
    obtain ⟨c, mem, same⟩ := List.mem_map.mp endpoint
    obtain ⟨candidate, condition⟩ := List.mem_filter.mp (sub.subset mem)
    exact valid c candidate (same.trans (of_decide_eq_true condition).1.symm)

private theorem test_keeps_truth (q : Query D V) (truth : D → Bool) (depth : Nat)
    (d : D) (current : List D) (keep : D → Bool)
    (onlyTruth : ∀ c, keep c = true → truth c = true)
    (valid : ∀ c ∈ current, q.source c ≠ q.target c)
    (faithful : ∀ c, pairPresent q truth c → ∀ C,
      q.source c ∉ C → q.target c ∉ C → q.independent c C = false) :
    (test q depth d current).filter keep = current.filter keep := by
  unfold test
  split
  next trigger =>
    obtain ⟨s, sub, _, ci⟩ := (separator_iff q depth current d).mp trigger.2
    have ends := eligible_conditions_valid sub valid
    have absent : ¬ pairPresent q truth d := by
      intro existsTruth
      rw [faithful d existsTruth _ ends.1 ends.2] at ci
      contradiction
    unfold deletePair
    rw [List.filter_filter]
    apply List.filter_congr
    intro c _
    cases decision : keep c with
    | false => simp
    | true =>
      have trueC := onlyTruth c decision
      have ne : c ≠ d := fun eq => absent (.inl (eq ▸ trueC))
      have neReverse : c ≠ q.reverse d := fun eq => absent (.inr (eq ▸ trueC))
      simp [ne, neReverse]
  · rfl

private theorem sweep_keeps_truth (q : Query D V) (truth : D → Bool) (depth : Nat)
    (schedule current : List D) (keep : D → Bool)
    (onlyTruth : ∀ c, keep c = true → truth c = true)
    (valid : ∀ c ∈ current, q.source c ≠ q.target c)
    (faithful : ∀ c, pairPresent q truth c → ∀ C,
      q.source c ∉ C → q.target c ∉ C → q.independent c C = false) :
    (sweep q depth schedule current).filter keep = current.filter keep := by
  induction schedule generalizing current with
  | nil => rfl
  | cons d pending ih =>
    change (sweep q depth pending (test q depth d current)).filter keep = current.filter keep
    rw [ih _ (fun c mem => valid c ((test_sublist q depth d current).subset mem))]
    exact test_keeps_truth q truth depth d current keep onlyTruth valid faithful

theorem search_keeps_truth (q : Query D V) (truth : D → Bool) (initial : List D) (levels : Nat)
    (keep : D → Bool) (onlyTruth : ∀ c, keep c = true → truth c = true)
    (valid : ∀ c ∈ initial, q.source c ≠ q.target c)
    (faithful : ∀ c, pairPresent q truth c → ∀ C,
      q.source c ∉ C → q.target c ∉ C → q.independent c C = false) :
    (search q initial levels).filter keep = initial.filter keep := by
  induction levels with
  | zero => rfl
  | succ n ih =>
    let current := search q initial n
    change (sweep q n current current).filter keep = initial.filter keep
    rw [sweep_keeps_truth q truth n current current keep onlyTruth ?_ faithful, ih]
    intro c mem
    exact valid c ((search_sublist q initial (Nat.zero_le n)).subset mem)

def trueParentCandidates (q : Query D V) (truth : D → Bool) (initial : List D) (d : D) :
    List D :=
  (initial.filter (eligible q d)).filter truth

def phaseOne (q : Query D V) (initial : List D) : List D :=
  search q initial (initial.length + 1)

/-- Sound deletion and complete recovery for the finite pass. True directed
dependencies supply the parent sets. A missing pair may have a parent
separator in either of its two perspectives. -/
theorem phaseOne_exact (q : Query D V) (truth : D → Bool) (initial : List D)
    (invol : ∀ c, q.reverse (q.reverse c) = c)
    (closed : PairClosed q initial)
    (valid : ∀ c ∈ initial, q.source c ≠ q.target c)
    (faithful : ∀ c, pairPresent q truth c → ∀ C,
      q.source c ∉ C → q.target c ∉ C → q.independent c C = false)
    (parentSeparates : ∀ d ∈ initial, ¬ pairPresent q truth d →
      q.independent d ((trueParentCandidates q truth initial d).map q.source) = true ∨
      q.independent (q.reverse d)
        ((trueParentCandidates q truth initial (q.reverse d)).map q.source) = true)
    (d : D) : d ∈ phaseOne q initial ↔ d ∈ initial ∧ pairPresent q truth d := by
  have preserved (levels : Nat) (c : D) :
      trueParentCandidates q truth (search q initial levels) c =
        trueParentCandidates q truth initial c := by
    simp only [trueParentCandidates, List.filter_filter]
    exact search_keeps_truth q truth initial levels _
      (fun _ h => by simpa using (Bool.and_eq_true_iff.mp h).1) valid faithful
  have answerEliminates (c : D) (survived : c ∈ phaseOne q initial)
      (ci : q.independent c ((trueParentCandidates q truth initial c).map q.source) = true) :
      False := by
    let s := trueParentCandidates q truth initial c
    have sSub : s.Sublist initial := List.filter_sublist.trans List.filter_sublist
    let n := s.length
    have within : n + 1 ≤ initial.length + 1 := Nat.succ_le_succ sSub.length_le
    have passed := (search_sublist q initial within).subset survived
    let current := search q initial n
    have scheduled := (sweep_sublist q n current current).subset passed
    have stable : s.Sublist ((search q initial (n + 1)).filter (eligible q c)) := by
      change (trueParentCandidates q truth initial c).Sublist _
      rw [← preserved (n + 1) c]
      exact List.filter_sublist
    have found := (separator_iff q n (search q initial (n + 1)) c).mpr ⟨s, stable, rfl, ci⟩
    have missed := sweep_exhausted q n current current scheduled passed
    change findSeparator q n (search q initial (n + 1)) c = false at missed
    rw [missed] at found
    contradiction
  constructor
  · intro kept
    have init := (search_sublist q initial (Nat.zero_le (initial.length + 1))).subset kept
    refine ⟨init, ?_⟩
    by_cases truePair : pairPresent q truth d
    · exact truePair
    · rcases parentSeparates d init truePair with forward | backward
      · exact (answerEliminates d kept forward).elim
      · have reverseKept := search_closed q invol initial closed (initial.length + 1) d kept
        exact (answerEliminates _ reverseKept backward).elim
  · rintro ⟨init, truePair⟩
    have trueSurvives (c : D) (mem : c ∈ initial) (trueC : truth c = true) :
        c ∈ phaseOne q initial := by
      have keep := search_keeps_truth q truth initial (initial.length + 1) truth
        (fun _ same => same) valid faithful
      have inside : c ∈ initial.filter truth := List.mem_filter.mpr ⟨mem, trueC⟩
      rw [← keep] at inside
      exact (List.mem_filter.mp inside).1
    rcases truePair with forward | backward
    · exact trueSurvives d init forward
    · have reverseKept := trueSurvives _ (closed d init) backward
      have kept := search_closed q invol initial closed (initial.length + 1) _ reverseKept
      rwa [invol] at kept

private theorem sweep_stationary_when_short (q : Query D V) (depth : Nat)
    (schedule current : List D)
    (short : ∀ d ∈ current, (current.filter (eligible q d)).length < depth) :
    sweep q depth schedule current = current := by
  induction schedule with
  | nil => rfl
  | cons candidate tail ih =>
    have noTest : ¬ (candidate ∈ current ∧ findSeparator q depth current candidate = true) := by
      rintro ⟨active, found⟩
      obtain ⟨_, subset, size, _⟩ := (separator_iff q depth current candidate).mp found
      have available := subset.length_le
      have limit := short candidate active
      omega
    change sweep q depth tail (test q depth candidate current) = _
    rw [test, ite_eq_right noTest]
    exact ih

/-- Continuing once no candidate has enough eligible neighbors cannot change
the surviving list. This justifies the finite level cap and early stopping. -/
theorem search_stationary_when_short (q : Query D V) (initial : List D) (depth tail : Nat)
    (short : ∀ d ∈ search q initial depth,
      ((search q initial depth).filter (eligible q d)).length < depth) :
    search q initial (depth + tail) = search q initial depth := by
  induction tail with
  | zero => rfl
  | succ tail ih =>
    change sweep q (depth + tail) (search q initial (depth+tail))
      (search q initial (depth+tail)) = _
    rw [ih]
    exact sweep_stationary_when_short q _ _ _ (fun d active => by
      have limit := short d active
      omega)

end RelationalFiniteSearch

end
