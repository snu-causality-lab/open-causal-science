module
public import Std

/-! The finite equal-score traversal in Algorithm 1 of Lam, Andrews and
Ramsey, UAI 2022. Costs are negative scores with the sign reversed. Candidate
orders and graph keys are supplied by the chosen oracle and tuck tier. -/

namespace OpenCausalScience.Papers.LamEtAl2022

@[expose] public section

namespace Search

variable {Order Key : Type}

/-- A bounded path has equal-cost intermediate orders and a strictly
lower-cost final order. Visited keys prevent repeating a DAG on a branch. -/
inductive Improvement (moves : Order → List Order) (cost : Order → Nat) (key : Order → Key) :
    Nat → List Key → Order → Order → Prop
  | direct {depth seen start target} :
      target ∈ moves start → key target ∉ seen → cost target < cost start →
      Improvement moves cost key (depth + 1) seen start target
  | plateau {depth seen start next target} :
      next ∈ moves start → key next ∉ seen → cost next = cost start →
      Improvement moves cost key depth (key next :: seen) next target →
      Improvement moves cost key (depth + 1) seen start target

def firstImprovement [DecidableEq Key] (moves : Order → List Order)
    (cost : Order → Nat) (key : Order → Key) :
    Nat → List Key → Order → Option Order
  | 0, _, _ => none
  | depth + 1, seen, start => (moves start).findSome? fun candidate =>
      if key candidate ∈ seen then none
      else if cost candidate < cost start then some candidate
      else if cost candidate = cost start then
        firstImprovement moves cost key depth (key candidate :: seen) candidate
      else none

theorem Improvement.lower_cost {moves : Order → List Order} {cost : Order → Nat}
    {key : Order → Key} {depth seen start target}
    (path : Improvement moves cost key depth seen start target) : cost target < cost start := by
  induction path with
  | direct _ _ lower => exact lower
  | plateau _ _ same _ lower => exact same ▸ lower

theorem first_improvement_sound [DecidableEq Key] {moves : Order → List Order}
    {cost : Order → Nat} {key : Order → Key} {depth seen start target}
    (found : firstImprovement moves cost key depth seen start = some target) :
    Improvement moves cost key depth seen start target := by
  induction depth generalizing seen start with
  | zero => simp [firstImprovement] at found
  | succ depth ih =>
    rw [firstImprovement] at found
    obtain ⟨first, candidate, last, partition, branch, _⟩ :=
      List.findSome?_eq_some_iff.mp found
    have member : candidate ∈ moves start := by simp [partition]
    by_cases visited : key candidate ∈ seen
    · simp [visited] at branch
    · by_cases lower : cost candidate < cost start
      · simp [visited, lower] at branch
        subst target
        exact .direct member visited lower
      · by_cases same : cost candidate = cost start
        · exact .plateau member visited same (ih (by simpa [visited, lower, same] using branch))
        · simp [visited, lower, same] at branch

theorem no_first_improvement_iff [DecidableEq Key] {moves : Order → List Order}
    {cost : Order → Nat} {key : Order → Key} {depth seen start} :
    firstImprovement moves cost key depth seen start = none ↔
      ∀ target, ¬ Improvement moves cost key depth seen start target := by
  constructor
  · intro noneFound target path
    induction path with
    | direct member fresh lower =>
      rw [firstImprovement, List.findSome?_eq_none_iff] at noneFound
      simpa [fresh, lower] using noneFound _ member
    | plateau member fresh same _ ih =>
      rw [firstImprovement, List.findSome?_eq_none_iff] at noneFound
      apply ih
      simpa [fresh, same] using noneFound _ member
  · intro impossible
    cases found : firstImprovement moves cost key depth seen start with
    | none => rfl
    | some target => exact False.elim (impossible target (first_improvement_sound found))

/-- The single-tier outer loop of Algorithm 2. Every successful search
strictly reduces the integer edge count, ensuring termination. -/
def descend [DecidableEq Key] (moves : Order → List Order) (cost : Order → Nat)
    (key : Order → Key) (depth : Nat) (start : Order) : Order :=
  match _h : firstImprovement moves cost key depth [key start] start with
  | none => start
  | some target => descend moves cost key depth target
termination_by cost start
decreasing_by exact (first_improvement_sound _h).lower_cost

theorem descend_spec [DecidableEq Key] (moves : Order → List Order) (cost : Order → Nat)
    (key : Order → Key) (depth : Nat) (start : Order) :
    cost (descend moves cost key depth start) ≤ cost start ∧
      firstImprovement moves cost key depth [key (descend moves cost key depth start)]
        (descend moves cost key depth start) = none := by
  rw [descend]
  cases found : firstImprovement moves cost key depth [key start] start with
  | none => simp [found]
  | some target =>
    have lower := (first_improvement_sound found).lower_cost
    obtain ⟨costBound, terminal⟩ := descend_spec moves cost key depth target
    exact ⟨Nat.le_trans costBound (Nat.le_of_lt lower), terminal⟩
termination_by cost start
decreasing_by exact (first_improvement_sound found).lower_cost


theorem Improvement.perm {α : Type} {moves : List α → List (List α)} {cost : List α → Nat}
    {key : List α → Key} {depth seen start target}
    (path : Improvement moves cost key depth seen start target)
    (movePerm : ∀ {a b}, b ∈ moves a → b.Perm a) : target.Perm start := by
  induction path with
  | direct member _ _ => exact movePerm member
  | plateau member _ _ _ tail => exact tail.trans (movePerm member)

theorem descend_perm {α : Type} [DecidableEq Key] (moves : List α → List (List α))
    (cost : List α → Nat) (key : List α → Key) (depth : Nat) (start : List α)
    (movePerm : ∀ {a b}, b ∈ moves a → b.Perm a) :
    (descend moves cost key depth start).Perm start := by
  rw [descend]
  cases found : firstImprovement moves cost key depth [key start] start with
  | none => exact .refl _
  | some target =>
    exact (descend_perm moves cost key depth target movePerm).trans
      ((first_improvement_sound found).perm movePerm)
termination_by cost start
decreasing_by exact (first_improvement_sound found).lower_cost

end Search

end

end OpenCausalScience.Papers.LamEtAl2022
