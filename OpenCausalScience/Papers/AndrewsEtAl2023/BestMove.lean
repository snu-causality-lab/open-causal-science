module
public import Std

/-! # BOSS single-variable relocation

Andrews et al. (NeurIPS 2023), Section 4, Algorithms 4–5. The ordering
phase uses a fixed exact rational score of the full order. Positions are
represented as the cuts of the list left after deleting the moved vertex.
-/

namespace OpenCausalScience.Papers.AndrewsEtAl2023.BestMove

@[expose] public section

variable {V : Type}

/-- Insert a vertex before each remaining vertex and once after the last. -/
def insertions (v : V) : List V → List (List V)
  | [] => [[v]]
  | w :: rest => (v :: w :: rest) :: (insertions v rest).map (w :: ·)

theorem mem_insertions_iff {v : V} {rest candidate : List V} :
    candidate ∈ insertions v rest ↔
      ∃ before after, rest = before ++ after ∧ candidate = before ++ v :: after := by
  induction rest generalizing candidate with
  | nil =>
      simp only [insertions, List.mem_singleton]
      constructor
      · intro equal
        exact ⟨[], [], rfl, equal⟩
      · rintro ⟨before, after, empty, equal⟩
        have ⟨hp, hs⟩ := List.append_eq_nil_iff.mp empty.symm
        simpa [hp, hs] using equal
  | cons w rest ih =>
      simp only [insertions, List.mem_cons, List.mem_map]
      constructor
      · rintro (rfl | ⟨inner, present, rfl⟩)
        · exact ⟨[], w :: rest, rfl, rfl⟩
        · obtain ⟨before, after, split, glue⟩ := ih.mp present
          exact ⟨w :: before, after, congrArg (w :: ·) split, congrArg (w :: ·) glue⟩
      · rintro ⟨before, after, split, rfl⟩
        cases before with
        | nil =>
            exact Or.inl (congrArg (v :: ·) split.symm)
        | cons first before =>
            simp only [List.cons_append, List.cons.injEq] at split ⊢
            obtain ⟨rfl, split⟩ := split
            exact Or.inr ⟨before ++ v :: after, ih.mpr ⟨before, after, split, rfl⟩, ⟨rfl, rfl⟩⟩

theorem insertions_eq_positions (v : V) (rest : List V) :
    insertions v rest = (List.range (rest.length + 1)).map (fun i => rest.insertIdx i v) := by
  induction rest with
  | nil => rfl
  | cons w rest ih =>
      simp only [insertions, List.length_cons]
      rw [List.range_succ_eq_map (n := rest.length + 1), ih]
      simp [List.map_map, Function.comp_def, List.insertIdx_succ_cons]

section Relocation

variable [DecidableEq V]

def relocations (v : V) (order : List V) : List (List V) :=
  insertions v (order.erase v)

theorem relocation_perm {v : V} {order candidate : List V}
    (present : v ∈ order) (candidateAtCut : candidate ∈ relocations v order) :
    candidate.Perm order := by
  obtain ⟨before, after, split, rfl⟩ := mem_insertions_iff.mp candidateAtCut
  have cut : (before ++ v :: after).Perm (v :: order.erase v) := by
    rw [split]
    exact List.perm_middle
  exact cut.trans (List.perm_cons_erase present).symm

theorem relocation_erase {v : V} {order candidate : List V}
    (unique : order.Nodup) (candidateAtCut : candidate ∈ relocations v order) :
    candidate.erase v = order.erase v := by
  obtain ⟨before, after, split, rfl⟩ := mem_insertions_iff.mp candidateAtCut
  have absent : v ∉ before := by
    intro present
    exact unique.not_mem_erase (split ▸ List.mem_append_left after present)
  rw [List.erase_append_right _ absent, List.erase_cons_head, split]

end Relocation

/-- A strict comparison retains the incumbent on a tie. -/
def bestAmong (score : List V → Rat) (incumbent : List V) : List (List V) → List V
  | [] => incumbent
  | next :: rest => bestAmong score (if score incumbent < score next then next else incumbent) rest

theorem best_among_mem {score : List V → Rat} {incumbent : List V}
    {candidates : List (List V)} :
    bestAmong score incumbent candidates = incumbent ∨ bestAmong score incumbent candidates ∈ candidates := by
  induction candidates generalizing incumbent with
  | nil => exact Or.inl rfl
  | cons next rest ih =>
      by_cases better : score incumbent < score next
      · simp only [bestAmong, ite_eq_left better]
        rcases ih (incumbent := next) with h | h
        · exact Or.inr (List.mem_cons.mpr (Or.inl h))
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · simp only [bestAmong, ite_eq_right better]
        rcases ih (incumbent := incumbent) with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

theorem best_among_ge_incumbent {score : List V → Rat} {incumbent : List V}
    {candidates : List (List V)} : score incumbent ≤ score (bestAmong score incumbent candidates) := by
  induction candidates generalizing incumbent with
  | nil => exact Rat.le_refl
  | cons next rest ih =>
      by_cases better : score incumbent < score next
      · simp only [bestAmong, ite_eq_left better]
        exact Rat.le_trans (Rat.le_of_lt better) ih
      · simpa only [bestAmong, ite_eq_right better] using ih (incumbent := incumbent)

theorem best_among_ge_candidate {score : List V → Rat} {incumbent candidate : List V}
    {candidates : List (List V)} (present : candidate ∈ candidates) :
    score candidate ≤ score (bestAmong score incumbent candidates) := by
  induction candidates generalizing incumbent with
  | nil => simp at present
  | cons next rest ih =>
      have fromHead : score next ≤
          score (if score incumbent < score next then next else incumbent) := by
        split
        · exact Rat.le_refl
        · exact Rat.not_lt.mp ‹¬_›
      simp only [bestAmong]
      rcases List.mem_cons.mp present with rfl | other
      · exact Rat.le_trans fromHead best_among_ge_incumbent
      · exact ih other

theorem best_among_eq_of_score_eq {score : List V → Rat} {incumbent : List V}
    {candidates : List (List V)}
    (equal : score (bestAmong score incumbent candidates) = score incumbent) :
    bestAmong score incumbent candidates = incumbent := by
  induction candidates generalizing incumbent with
  | nil => rfl
  | cons next rest ih =>
      by_cases better : score incumbent < score next
      · simp only [bestAmong, ite_eq_left better] at equal
        have bound := best_among_ge_incumbent (score := score) (incumbent := next) (candidates := rest)
        rw [equal] at bound
        exact False.elim (Rat.not_lt.mpr bound better)
      · simp only [bestAmong, ite_eq_right better] at equal ⊢
        exact ih equal

section Search

variable [DecidableEq V]

def bestMove (score : List V → Rat) (order : List V) (v : V) : List V :=
  bestAmong score order (relocations v order)

theorem best_move_perm {score : List V → Rat} {order : List V} {v : V} (present : v ∈ order) :
    (bestMove score order v).Perm order := by
  rcases best_among_mem (score := score) (incumbent := order) (candidates := relocations v order)
      with unchanged | moved
  · simp [bestMove, unchanged]
  · exact relocation_perm present moved

theorem best_move_maximal {score : List V → Rat} {order candidate : List V} {v : V}
    (legal : candidate ∈ relocations v order) : score candidate ≤ score (bestMove score order v) :=
  best_among_ge_candidate legal

/-- Scan Algorithm 5's positions using the current order at every step.
On rejection its remove-and-reinsert rollback leaves the incumbent unchanged. -/
def scanPositions (score : List V → Rat) (v : V) (order : List V) : List Nat → List V
  | [] => order
  | i :: positions =>
      let candidate := (order.erase v).insertIdx i v
      scanPositions score v (if score order < score candidate then candidate else order) positions

theorem scan_positions_eq_best_among {score : List V → Rat} {v : V}
    {order : List V} {positions : List Nat} (present : v ∈ order) (unique : order.Nodup)
    (valid : ∀ i ∈ positions, i ≤ (order.erase v).length) :
    scanPositions score v order positions =
      bestAmong score order (positions.map (fun i => (order.erase v).insertIdx i v)) := by
  induction positions generalizing order with
  | nil => rfl
  | cons i positions ih =>
      let candidate := (order.erase v).insertIdx i v
      have validFirst := valid i List.mem_cons_self
      have atPosition : candidate ∈ relocations v order := by
        rw [relocations, insertions_eq_positions]
        exact List.mem_map.mpr ⟨i, List.mem_range.mpr (Nat.lt_succ_of_le validFirst), rfl⟩
      have validRest (j : Nat) (inside : j ∈ positions) : j ≤ (order.erase v).length :=
        valid j (List.mem_cons_of_mem i inside)
      by_cases better : score order < score candidate
      · have eraseSame := relocation_erase unique atPosition
        have sameVertices := relocation_perm present atPosition
        have tailEq := ih (sameVertices.mem_iff.mpr present) (sameVertices.nodup_iff.mpr unique)
          (fun j inside => eraseSame.symm ▸ validRest j inside)
        rw [eraseSame] at tailEq
        dsimp [candidate] at better
        simpa only [scanPositions, List.map_cons, bestAmong, ite_eq_left better] using tailEq
      · dsimp [candidate] at better
        simpa only [scanPositions, List.map_cons, bestAmong, ite_eq_right better] using
          ih present unique validRest

theorem algorithm_five_eq_best_move {score : List V → Rat} {v : V} {order : List V}
    (present : v ∈ order) (unique : order.Nodup) :
    scanPositions score v order (List.range order.length) = bestMove score order v := by
  have positive : 0 < order.length := List.length_pos_of_mem present
  have size : (order.erase v).length + 1 = order.length := by
    rw [List.length_erase_of_mem present]
    omega
  rw [bestMove, relocations, insertions_eq_positions, size]
  exact scan_positions_eq_best_among present unique (fun i hi => by
    have bound := List.mem_range.mp hi
    omega)

/-- One sweep visits the vertices in the order at the start of the sweep. -/
def sweep (score : List V → Rat) (order : List V) : List V → List V
  | [] => order
  | v :: pending => sweep score (bestMove score order v) pending

theorem sweep_perm {score : List V → Rat} {order schedule : List V} (valid : schedule ⊆ order) :
    (sweep score order schedule).Perm order := by
  induction schedule generalizing order with
  | nil => exact List.Perm.refl _
  | cons v pending ih =>
      have move := best_move_perm (score := score) (valid (List.mem_cons_self))
      exact (ih fun _ h => move.mem_iff.mpr (valid (List.mem_cons_of_mem _ h))).trans move

theorem sweep_score_mono {score : List V → Rat} {order schedule : List V} :
    score order ≤ score (sweep score order schedule) := by
  induction schedule generalizing order with
  | nil => exact Rat.le_refl
  | cons v pending ih =>
      exact Rat.le_trans best_among_ge_incumbent ih

theorem sweep_fixed_at_equal_score {score : List V → Rat} {order schedule : List V}
    (equal : score (sweep score order schedule) = score order) :
    sweep score order schedule = order ∧
      ∀ v ∈ schedule, ∀ candidate ∈ relocations v order, score candidate ≤ score order := by
  induction schedule generalizing order with
  | nil => simp [sweep]
  | cons v pending ih =>
      have first := best_among_ge_incumbent (score := score) (incumbent := order)
        (candidates := relocations v order)
      have last : score (bestMove score order v) ≤ score (sweep score order (v :: pending)) :=
        sweep_score_mono
      rw [equal] at last
      have noGain : score (bestMove score order v) = score order := Rat.le_antisymm last first
      have same : bestMove score order v = order := best_among_eq_of_score_eq noGain
      change score (sweep score (bestMove score order v) pending) = score order at equal
      rw [same] at equal
      obtain ⟨fixed, optimal⟩ := ih equal
      simp only [sweep, same, fixed, true_and]
      intro target inSchedule candidate legal
      rcases List.mem_cons.mp inSchedule with rfl | later
      · simpa only [same] using best_move_maximal (score := score) legal
      · exact optimal _ later _ legal


/-- Used only in the termination measure, which is erased during execution. -/
def wordsOfLength (alphabet : List V) : Nat → List (List V)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap (fun v => (wordsOfLength alphabet n).map (v :: ·))

omit [DecidableEq V] in
private theorem mem_words_of_length {alphabet order : List V} (within : order ⊆ alphabet) :
    order ∈ wordsOfLength alphabet order.length := by
  induction order with
  | nil => simp [wordsOfLength]
  | cons v rest ih =>
      simp only [List.length_cons, wordsOfLength, List.mem_flatMap, List.mem_map]
      refine ⟨v, within List.mem_cons_self, rest, ih ?_, rfl⟩
      exact fun _ present => within (List.mem_cons_of_mem _ present)

def higherScoreCount (score : List V → Rat) (order : List V) (orders : List (List V)) : Nat :=
  (orders.filter (fun candidate => decide (score order < score candidate))).length

omit [DecidableEq V] in

private theorem higher_score_count_lt {score : List V → Rat} {before after : List V}
    {orders : List (List V)} (better : score before < score after) (present : after ∈ orders) :
    higherScoreCount score after orders < higherScoreCount score before orders := by
  let afterTest := fun candidate => decide (score after < score candidate)
  let beforeTest := fun candidate => decide (score before < score candidate)
  have same : (orders.filter beforeTest).filter afterTest = orders.filter afterTest := by
    rw [List.filter_filter]
    congr 1
    funext candidate
    by_cases greater : score after < score candidate
    · have both : score before < score candidate := Rat.not_le.mp (fun reverse =>
        Rat.not_lt.mpr (Rat.le_trans reverse (Rat.le_of_lt better)) greater)
      simp [afterTest, beforeTest, greater, both]
    · simp [afterTest, greater]
  change (orders.filter afterTest).length < (orders.filter beforeTest).length
  rw [← same]
  have le := List.length_filter_le afterTest (orders.filter beforeTest)
  apply Nat.lt_of_le_of_ne le
  intro equal
  have seen : after ∈ orders.filter beforeTest := List.mem_filter.mpr ⟨present, by simpa [beforeTest]⟩
  have impossible := List.length_filter_eq_length_iff.mp equal after seen
  simp [afterTest, Rat.lt_irrefl] at impossible

/-- All legal single-variable relocations have at most the incumbent's score. -/
def RelocationOptimal (score : List V → Rat) (order : List V) : Prop :=
  ∀ v ∈ order, ∀ candidate ∈ relocations v order, score candidate ≤ score order

/-- The order-search phase of Algorithm 4. The measure counts orders above the
current score over a finite alphabet. It does not enumerate these at runtime. -/
def searchFrom (score : List V → Rat) (initial current : List V) (within : current.Perm initial) :
    {result : List V // result.Perm initial ∧ RelocationOptimal score result} :=
  let next := sweep score current current
  if better : score current < score next then
    searchFrom score initial next ((sweep_perm (fun _ h => h)).trans within)
  else
    let equal := Rat.le_antisymm (Rat.not_lt.mp better) (sweep_score_mono)
    ⟨current, within, (sweep_fixed_at_equal_score equal).2⟩
termination_by higherScoreCount score current (wordsOfLength initial initial.length)
decreasing_by
  apply higher_score_count_lt better
  have nextWithin : next.Perm initial := (sweep_perm (fun _ h => h)).trans within
  have mem := mem_words_of_length (order := next) (alphabet := initial)
    (fun _ present => nextWithin.mem_iff.mp present)
  simpa only [nextWithin.length_eq] using mem

/-- Run BOSS's order search from the supplied starting order. -/
def search (score : List V → Rat) (initial : List V) : List V :=
  (searchFrom score initial initial (List.Perm.refl initial)).val

theorem search_perm_and_locally_optimal (score : List V → Rat) (initial : List V) :
    (search score initial).Perm initial ∧ RelocationOptimal score (search score initial) :=
  (searchFrom score initial initial (List.Perm.refl initial)).property

end Search
end
end OpenCausalScience.Papers.AndrewsEtAl2023.BestMove
