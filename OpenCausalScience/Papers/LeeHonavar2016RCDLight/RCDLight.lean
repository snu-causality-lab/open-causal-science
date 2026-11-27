module
public import Std

@[expose] public section

namespace RCDLight

/-- The appendix uses positive, one-based prefix lengths. -/
def Pivot (p q : List K) (i : Nat) : Prop :=
  1 ≤ i ∧ i ≤ p.length ∧ i ≤ q.length ∧ p.take i = q.take i

instance [DecidableEq K] (p q : List K) (i : Nat) : Decidable (Pivot p q i) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def joinAt (p q : List K) (i : Nat) : List K :=
  p.take (p.length - i) ++ q.drop (i - 1)

inductive Class
  | A | R | B | S | C | T | D
  deriving DecidableEq

open Class

/-- This is a pair of valid reverse paths across R(A,B), with pivot 3. -/
theorem maximal_pivots_counterexample :
    Pivot ([B,R,A] : List Class).reverse [A,R,B] 3 ∧
      ¬ Pivot ([A,R,B] : List Class).reverse [A,R,B] 3 := by
  decide

theorem maximal_pivots (p q : List K) (i : Nat) (h : Pivot p.reverse q i) :
    Pivot q q i :=
  ⟨h.1, h.2.2.1, h.2.2.1, rfl⟩

/-- In Figure 5's unequal-pivot case the printed pivot can fail to be a pivot. -/
theorem representative_pivot_counterexample :
    let q' : List Class := [A,R,B,S,C]
    let d₁ : List Class := [C,S,B]
    let d₂ : List Class := [C,T,D]
    let m := 3
    let n := 1
    let p' := joinAt q' d₁ m
    let r' := joinAt q' d₂ n
    let r := joinAt d₁.reverse d₂ (min m n)
    Pivot q'.reverse d₁ m ∧ Pivot q'.reverse d₂ n ∧
      ¬ Pivot p'.reverse r (d₁.length - m + (m - n) + 1) ∧
      Pivot p'.reverse r (d₁.length - m + 1) ∧
      joinAt p' r (d₁.length - m + 1) = r' := by
  decide

/-- Composition through a shared reversed suffix, including its final item. -/
theorem join_reversed_suffix (before overlap after : List K) (v : K) :
    Pivot (before ++ v :: overlap.reverse).reverse (overlap ++ v :: after)
        (overlap.length + 1) ∧
      joinAt (before ++ v :: overlap.reverse) (overlap ++ v :: after)
        (overlap.length + 1) = before ++ v :: after := by
  have takePrefix (s : List K) :
      (overlap ++ v :: s).take (overlap.length + 1) = overlap ++ [v] := by
    rw [List.take_append, List.take_of_length_le (by omega)]
    simp
  constructor
  · refine ⟨by omega, by simp, by simp, ?_⟩
    simp [List.reverse_append, takePrefix]
  · unfold joinAt
    have sub : (before ++ v :: overlap.reverse).length - (overlap.length + 1) =
        before.length := by
      simp
    rw [sub]
    simp

/-- When m > n the shared composition prefix ends at the m-th item. -/
theorem representative_pivot_n_lt_m (base gap xTail zTail : List K) (a b : K) :
    let p' := base ++ b :: xTail
    let r := xTail.reverse ++ b :: gap.reverse ++ a :: zTail
    let r' := base ++ b :: gap.reverse ++ a :: zTail
    Pivot p'.reverse r (xTail.length + 1) ∧
      joinAt p' r (xTail.length + 1) = r' := by
  simpa using join_reversed_suffix base xTail.reverse (gap.reverse ++ a :: zTail) b

/-- When m < n the shared composition prefix continues to the n-th item. -/
theorem representative_pivot_m_lt_n (base gap xTail zTail : List K) (a b : K) :
    let p' := base ++ b :: gap.reverse ++ a :: xTail
    let r := xTail.reverse ++ a :: gap ++ b :: zTail
    let r' := base ++ b :: zTail
    Pivot p'.reverse r (xTail.length + gap.length + 2) ∧
      joinAt p' r (xTail.length + gap.length + 2) = r' := by
  have h := join_reversed_suffix base (xTail.reverse ++ a :: gap) zTail b
  simp only [List.reverse_append, List.reverse_cons, List.reverse_reverse, List.append_assoc,
    List.singleton_append, List.length_append, List.length_reverse, List.length_cons] at h
  have eq : xTail.length + (gap.length + 1) + 1 = xTail.length + gap.length + 2 := by omega
  rw [eq] at h
  simpa [List.reverse_append, List.reverse_cons, List.append_assoc] using h

end RCDLight

end
