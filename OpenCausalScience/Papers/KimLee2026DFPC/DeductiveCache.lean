module
public import OpenCausalScience.Papers.KimEtAl2024.DeduceDep

/-! # DEDUCE-HELPER and DEDUCE

[Kim and Lee, DF-PC corrected version](https://www.sanghacklee.me/assets/2026-UAI-dfpc-paper-2026-09-14.pdf),
Algorithms 3–4 and Appendix D, Lemma 1 and Theorem 1. The three labels
represent decisive independence, decisive dependence, and an unresolved
query. A stored unresolved result is distinct from an absent entry.
Cache keys use the supplied endpoint order and conditioning list. The
proof applies to any ordering of the distinct conditioning variables.
-/

namespace OpenCausalScience.Papers.KimLee2026DFPC.DeductiveCache

@[expose] public section

structure Query (α : Type) where
  left : α
  right : α
  given : List α
  deriving DecidableEq

def Query.Valid {α : Type} (q : Query α) : Prop :=
  q.left ≠ q.right ∧ q.left ∉ q.given ∧ q.right ∉ q.given ∧ q.given.Nodup

inductive Label where
  | ind
  | dep
  | unknown
  deriving DecidableEq

abbrev Cache (α : Type) := Query α → Option Label

def emptyCache {α : Type} : Cache α := fun _ => none

def record {α : Type} [DecidableEq α] (cache : Cache α) (q : Query α)
    (label : Label) : Cache α :=
  fun other => if other = q then some label else cache other

def Label.Sound {α : Type} (independent : Query α → Prop) (q : Query α) : Label → Prop
  | .ind => independent q
  | .dep => ¬ independent q
  | .unknown => True

def Cache.Sound {α : Type} (independent : Query α → Prop) (cache : Cache α) : Prop :=
  ∀ q label, cache q = some label → label.Sound independent q

theorem emptyCache_sound {α : Type} (independent : Query α → Prop) :
    (emptyCache : Cache α).Sound independent := by
  intro q label h
  simp [emptyCache] at h

private theorem record_sound {α : Type} [DecidableEq α]
    {independent : Query α → Prop} {cache : Cache α} {q : Query α} {label : Label}
    (good : cache.Sound independent) (answer : label.Sound independent q) :
    (record cache q label).Sound independent := by
  intro other stored hit
  by_cases same : other = q
  · subst other
    have eq := Option.some.inj (by simpa [record] using hit)
    subst stored
    exact answer
  · exact good other stored (by simpa [record, same] using hit)

def lowerQueries {α : Type} [DecidableEq α] (q : Query α) (pivot : α) :
    Query α × Query α × Query α :=
  let rest := q.given.erase pivot
  (⟨q.left, q.right, rest⟩, ⟨q.left, pivot, rest⟩, ⟨q.right, pivot, rest⟩)

private theorem lowerQueries_valid {α : Type} [DecidableEq α]
    {q : Query α} {pivot : α} (valid : q.Valid) (present : pivot ∈ q.given) :
    (lowerQueries q pivot).1.Valid ∧ (lowerQueries q pivot).2.1.Valid ∧
      (lowerQueries q pivot).2.2.Valid := by
  obtain ⟨distinct, noLeft, noRight, nodup⟩ := valid
  have leftDistinct : q.left ≠ pivot := fun eq => noLeft (eq.symm ▸ present)
  have rightDistinct : q.right ≠ pivot := fun eq => noRight (eq.symm ▸ present)
  have leftOutside : q.left ∉ q.given.erase pivot :=
    fun mem => noLeft (List.mem_of_mem_erase mem)
  have rightOutside : q.right ∉ q.given.erase pivot :=
    fun mem => noRight (List.mem_of_mem_erase mem)
  exact ⟨⟨distinct, leftOutside, rightOutside, nodup.erase _⟩,
    ⟨leftDistinct, leftOutside, nodup.not_mem_erase, nodup.erase _⟩,
    ⟨rightDistinct, rightOutside, nodup.not_mem_erase, nodup.erase _⟩⟩

/-- Singleton contraction (followed by decomposition), singleton weak
transitivity, and composition followed by weak union. Both orientations of
contraction and of composition/weak union are stated explicitly. -/
structure Rules {α : Type} [DecidableEq α] (independent : Query α → Prop) : Prop where
  contractLeft : ∀ q pivot, q.Valid → pivot ∈ q.given →
    independent (lowerQueries q pivot).2.1 → independent q → independent (lowerQueries q pivot).1
  contractRight : ∀ q pivot, q.Valid → pivot ∈ q.given →
    independent (lowerQueries q pivot).2.2 → independent q → independent (lowerQueries q pivot).1
  weakTransitivity : ∀ q pivot, q.Valid → pivot ∈ q.given →
    independent (lowerQueries q pivot).1 → independent q →
      independent (lowerQueries q pivot).2.1 ∨ independent (lowerQueries q pivot).2.2
  composeWeakUnionLeft : ∀ q pivot, q.Valid → pivot ∈ q.given →
    independent (lowerQueries q pivot).1 → independent (lowerQueries q pivot).2.1 → independent q
  composeWeakUnionRight : ∀ q pivot, q.Valid → pivot ∈ q.given →
    independent (lowerQueries q pivot).1 → independent (lowerQueries q pivot).2.2 → independent q

/-- A rule needs the decisive labels of exactly its stated premises. -/
def infer (xy xz yz : Label) : Label :=
  match xy with
  | .dep => if xz = .ind ∨ yz = .ind then .dep else .unknown
  | .ind =>
    if xz = .dep ∧ yz = .dep then .dep
    else if xz = .ind ∨ yz = .ind then .ind else .unknown
  | .unknown => .unknown

theorem infer_dep_iff (xy xz yz : Label) :
    infer xy xz yz = .dep ↔
      (xy = .dep ∧ (xz = .ind ∨ yz = .ind)) ∨
        (xy = .ind ∧ xz = .dep ∧ yz = .dep) := by
  cases xy <;> cases xz <;> cases yz <;> decide

theorem infer_ind_iff (xy xz yz : Label) :
    infer xy xz yz = .ind ↔ xy = .ind ∧ (xz = .ind ∨ yz = .ind) := by
  cases xy <;> cases xz <;> cases yz <;> decide

theorem infer_sound {α : Type} [DecidableEq α] {independent : Query α → Prop}
    (rules : Rules independent) {q : Query α} {pivot : α} {xy xz yz : Label}
    (valid : q.Valid) (present : pivot ∈ q.given)
    (xySound : xy.Sound independent (lowerQueries q pivot).1)
    (xzSound : xz.Sound independent (lowerQueries q pivot).2.1)
    (yzSound : yz.Sound independent (lowerQueries q pivot).2.2) :
    (infer xy xz yz).Sound independent q := by
  have dep := KimEtAl2024.DeduceDep.dependence_of_lower_order_ci
    (rules.contractLeft q pivot valid present) (rules.contractRight q pivot valid present)
    (rules.weakTransitivity q pivot valid present)
  cases xy with
  | unknown => trivial
  | dep =>
    by_cases witness : xz = .ind ∨ yz = .ind
    · rw [infer, ite_eq_left witness]
      change ¬ independent q
      apply dep
      rcases witness with same | same
      · subst xz
        exact .inl ⟨xySound, .inl xzSound⟩
      · subst yz
        exact .inl ⟨xySound, .inr yzSound⟩
    · simp [infer, witness, Label.Sound]
  | ind =>
    by_cases negative : xz = .dep ∧ yz = .dep
    · rcases negative with ⟨rfl, rfl⟩
      exact dep (.inr ⟨xySound, xzSound, yzSound⟩)
    by_cases positive : xz = .ind ∨ yz = .ind
    · rw [infer, ite_eq_right negative, ite_eq_left positive]
      rcases positive with rfl | rfl
      · exact rules.composeWeakUnionLeft q pivot valid present xySound xzSound
      · exact rules.composeWeakUnionRight q pivot valid present xySound yzSound
    · simp [infer, negative, positive, Label.Sound]

def fill {α : Type} [DecidableEq α] (q : Query α) (cache : Cache α)
    (solve : Cache α → Label × Cache α) : Label × Cache α :=
  match cache q with
  | some label => (label, cache)
  | none =>
    let (label, next) := solve cache
    (label, record next q label)

private theorem fill_sound {α : Type} [DecidableEq α] {independent : Query α → Prop}
    {q : Query α} {cache : Cache α} {solve : Cache α → Label × Cache α}
    (good : cache.Sound independent)
    (solveGood : ∀ c, c.Sound independent →
      (solve c).1.Sound independent q ∧ (solve c).2.Sound independent) :
    (fill q cache solve).1.Sound independent q ∧ (fill q cache solve).2.Sound independent := by
  cases hit : cache q with
  | some label => exact (by simpa [fill, hit] using And.intro (good q label hit) good)
  | none =>
    obtain ⟨answer, nextGood⟩ := solveGood cache good
    cases solving : solve cache with
    | mk label next =>
      rw [solving] at answer nextGood
      simpa [fill, hit, solving] using And.intro answer (record_sound nextGood answer)

abbrev SmallerSolver {α : Type} (q : Query α) :=
  (child : Query α) → child.given.length < q.given.length → Cache α → Label × Cache α

theorem erase_shorter {α : Type} [DecidableEq α] {given : List α} {pivot : α}
    (present : pivot ∈ given) : (given.erase pivot).length < given.length := by
  rw [List.length_erase_of_mem present]
  have size := List.length_pos_of_mem present
  omega

def runPivot {α : Type} [DecidableEq α] (q : Query α) (pivot : α)
    (present : pivot ∈ q.given) (solve : SmallerSolver q) (cache : Cache α) :
    Label × Cache α :=
  let pivotQueries := lowerQueries q pivot
  let xy := fill pivotQueries.1 cache (solve pivotQueries.1 (erase_shorter present))
  let xz := fill pivotQueries.2.1 xy.2 (solve pivotQueries.2.1 (erase_shorter present))
  let yz := fill pivotQueries.2.2 xz.2 (solve pivotQueries.2.2 (erase_shorter present))
  (infer xy.1 xz.1 yz.1, yz.2)

def scan {α β : Type} (run : β → Cache α → Label × Cache α) :
    List β → Bool → Cache α → Label × Cache α
  | [], seenInd, cache => (if seenInd then .ind else .unknown, cache)
  | pivot :: rest, seenInd, cache =>
    let (label, next) := run pivot cache
    match label with
    | .dep => (.dep, next)
    | .ind => scan run rest true next
    | .unknown => scan run rest seenInd next

def deduceHelper {α : Type} [DecidableEq α] (q : Query α) (cache : Cache α) :
    Label × Cache α :=
  scan
    (fun pivot => runPivot q pivot.1 pivot.2 (fun child _smaller c => deduceHelper child c))
    q.given.attach false cache
termination_by q.given.length
decreasing_by exact _smaller

theorem deduceHelper_marginal {α : Type} [DecidableEq α] (q : Query α) (cache : Cache α)
    (marginal : q.given = []) : deduceHelper q cache = (.unknown, cache) := by
  obtain ⟨left, right, given⟩ := q
  change given = [] at marginal
  subst given
  rw [deduceHelper]
  rfl

private theorem runPivot_sound {α : Type} [DecidableEq α] {independent : Query α → Prop}
    (rules : Rules independent) {q : Query α} {pivot : α} {cache : Cache α}
    {solve : SmallerSolver q} (valid : q.Valid) (present : pivot ∈ q.given)
    (good : cache.Sound independent)
    (solveGood : ∀ child smaller c, child.Valid → c.Sound independent →
      (solve child smaller c).1.Sound independent child ∧
      (solve child smaller c).2.Sound independent) :
    (runPivot q pivot present solve cache).1.Sound independent q ∧
      (runPivot q pivot present solve cache).2.Sound independent := by
  obtain ⟨xyValid, xzValid, yzValid⟩ := lowerQueries_valid valid present
  have xy := fill_sound good (solveGood _ (erase_shorter present) · xyValid)
  have xz := fill_sound xy.2 (solveGood _ (erase_shorter present) · xzValid)
  have yz := fill_sound xz.2 (solveGood _ (erase_shorter present) · yzValid)
  exact ⟨infer_sound rules valid present xy.1 xz.1 yz.1, yz.2⟩

private theorem scan_sound {α β : Type} {independent : Query α → Prop}
    {q : Query α} {run : β → Cache α → Label × Cache α}
    (runGood : ∀ pivot c, c.Sound independent →
      (run pivot c).1.Sound independent q ∧ (run pivot c).2.Sound independent)
    (pivots : List β) (seenInd : Bool) (cache : Cache α)
    (seenGood : seenInd = true → independent q) (good : cache.Sound independent) :
    (scan run pivots seenInd cache).1.Sound independent q ∧
      (scan run pivots seenInd cache).2.Sound independent := by
  induction pivots generalizing seenInd cache with
  | nil =>
    cases seen : seenInd
    · exact ⟨trivial, good⟩
    · exact ⟨seenGood seen, good⟩
  | cons pivot rest ih =>
    obtain ⟨answer, nextGood⟩ := runGood pivot cache good
    cases result : run pivot cache with
    | mk label next =>
      rw [result] at answer nextGood
      cases label with
      | dep => simpa [scan, result] using And.intro answer nextGood
      | ind => simpa [scan, result] using ih true next (fun _ => answer) nextGood
      | unknown => simpa [scan, result] using ih seenInd next seenGood nextGood

/-- Appendix D, Lemma 1. Every recursive call strictly drops the conditioning
order and every cache write preserves soundness, including stored UNKNOWN. -/
theorem deduceHelper_sound {α : Type} [DecidableEq α] {independent : Query α → Prop}
    (rules : Rules independent) (q : Query α) (cache : Cache α)
    (valid : q.Valid) (good : cache.Sound independent) :
    (deduceHelper q cache).1.Sound independent q ∧
      (deduceHelper q cache).2.Sound independent := by
  induction size : q.given.length using Nat.strongRecOn generalizing q cache with
  | ind lengthBound ih =>
    rw [deduceHelper]
    apply scan_sound _ _ _ _ (by simp) good
    intro pivot c cGood
    apply runPivot_sound rules valid pivot.2 cGood
    intro child smaller childCache childValid childGood
    exact ih child.given.length (size ▸ smaller) child childCache childValid childGood rfl

def oracleLabel (independent : Bool) : Label :=
  if independent then .ind else .dep

def OracleExact {α : Type} (independent : Query α → Prop) (oracle : Query α → Bool) : Prop :=
  ∀ q, q.Valid → (oracle q = true ↔ independent q)

structure DeduceResult (α : Type) where
  label : Label
  cache : Cache α
  usedCIT : Bool

/-- Algorithm 3 uses the oracle only for UNKNOWN, and the caller records the
decisive outcome for future queries. -/
def deduce {α : Type} [DecidableEq α] (oracle : Query α → Bool)
    (q : Query α) (cache : Cache α) : DeduceResult α :=
  let (label, next) := deduceHelper q cache
  let useOracle := decide (label = .unknown)
  let answer := if useOracle then oracleLabel (oracle q) else label
  ⟨answer, record next q answer, useOracle⟩

theorem deduce_usesCIT_iff {α : Type} [DecidableEq α] (oracle : Query α → Bool)
    (q : Query α) (cache : Cache α) :
    (deduce oracle q cache).usedCIT = true ↔ (deduceHelper q cache).1 = .unknown := by
  cases result : deduceHelper q cache
  simp [deduce, result]

/-- Appendix D, Theorem 1. The answer is exactly the oracle answer, and the
updated cache is sound for the next call. -/
theorem deduce_sound {α : Type} [DecidableEq α] {independent : Query α → Prop}
    (rules : Rules independent) {oracle : Query α → Bool} (exactOracle : OracleExact independent oracle)
    (q : Query α) (cache : Cache α) (valid : q.Valid) (good : cache.Sound independent) :
    (deduce oracle q cache).label = oracleLabel (oracle q) ∧
      (deduce oracle q cache).label.Sound independent q ∧
      (deduce oracle q cache).cache.Sound independent := by
  obtain ⟨answer, nextGood⟩ := deduceHelper_sound rules q cache valid good
  have oracleGood : (oracleLabel (oracle q)).Sound independent q := by
    cases h : oracle q with
    | false =>
      have dep : ¬ independent q := fun indep => by
        have eq := (exactOracle q valid).mpr indep
        simp [h] at eq
      simpa [oracleLabel, h, Label.Sound] using dep
    | true => simpa [oracleLabel, h, Label.Sound] using (exactOracle q valid).mp h
  cases result : deduceHelper q cache with
  | mk label next =>
    rw [result] at answer nextGood
    have decisive : label ≠ .unknown → label = oracleLabel (oracle q) := by
      intro notUnknown
      cases label with
      | ind =>
        have yes := (exactOracle q valid).mpr answer
        simp [oracleLabel, yes]
      | dep =>
        have no : oracle q = false := by
          cases yes : oracle q
          · rfl
          · exact (answer ((exactOracle q valid).mp yes)).elim
        simp [oracleLabel, no]
      | unknown => exact (notUnknown rfl).elim
    cases label with
    | unknown =>
      simpa [deduce, result] using And.intro
        (Eq.refl (oracleLabel (oracle q))) (And.intro oracleGood (record_sound nextGood oracleGood))
    | ind =>
      simpa [deduce, result] using And.intro
        (decisive (by decide)) (And.intro answer (record_sound nextGood answer))
    | dep =>
      simpa [deduce, result] using And.intro
        (decisive (by decide)) (And.intro answer (record_sound nextGood answer))

/-- A finite adaptive sequence of CI queries. Its terminal result can
contain the skeleton and separating sets determined by its answers. -/
inductive QueryPlan (α β : Type) where
  | done (output : β)
  | ask (q : Query α) (valid : q.Valid) (next : Label → QueryPlan α β)

abbrev Outcome (α β : Type) := β × List (Query α × Label)

def runOracle {α β : Type} (oracle : Query α → Bool) :
    QueryPlan α β → Outcome α β
  | .done output => (output, [])
  | .ask q _ next =>
    let label := oracleLabel (oracle q)
    let later := runOracle oracle (next label)
    (later.1, (q, label) :: later.2)

def runDeduce {α β : Type} [DecidableEq α] (oracle : Query α → Bool) :
    QueryPlan α β → Cache α → Outcome α β × Cache α
  | .done output, cache => ((output, []), cache)
  | .ask q _ next, cache =>
    let answer := deduce oracle q cache
    let later := runDeduce oracle (next answer.label) answer.cache
    ((later.1.1, (q, answer.label) :: later.1.2), later.2)

/-- Replacing an exact oracle by DEDUCE preserves every adaptive query
and answer, as well as the terminal result. The transcript records the
outer queries, which may or may not require an actual CIT. -/
theorem runDeduce_eq_runOracle {α β : Type} [DecidableEq α] {independent : Query α → Prop}
    (rules : Rules independent) {oracle : Query α → Bool} (exactOracle : OracleExact independent oracle)
    (plan : QueryPlan α β) (cache : Cache α) (good : cache.Sound independent) :
    (runDeduce oracle plan cache).1 = runOracle oracle plan ∧
      (runDeduce oracle plan cache).2.Sound independent := by
  induction plan generalizing cache with
  | done => exact ⟨rfl, good⟩
  | ask q valid next ih =>
    obtain ⟨same, _, nextGood⟩ := deduce_sound rules exactOracle q cache valid good
    obtain ⟨later, finalGood⟩ := ih (oracleLabel (oracle q)) (deduce oracle q cache).cache nextGood
    constructor
    · simp only [runDeduce, runOracle, same, later]
    · simpa only [runDeduce, same] using finalGood

theorem runDeduce_from_empty {α β : Type} [DecidableEq α] {independent : Query α → Prop}
    (rules : Rules independent) {oracle : Query α → Bool} (exactOracle : OracleExact independent oracle)
    (plan : QueryPlan α β) :
    (runDeduce oracle plan emptyCache).1 = runOracle oracle plan ∧
      (runDeduce oracle plan emptyCache).2.Sound independent :=
  runDeduce_eq_runOracle rules exactOracle plan emptyCache (emptyCache_sound independent)

end

end OpenCausalScience.Papers.KimLee2026DFPC.DeductiveCache
