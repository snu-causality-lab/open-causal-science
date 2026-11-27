module
public import OpenCausalScience.Papers.Chickering1995.CoveredReversal

/-! Counting arrows in the comparison of a covered reversal and a tuck. -/

namespace OpenCausalScience.Papers.LamEtAl2022

open Chickering1995.CoveredReversal

@[expose] public section

variable {n : Nat}

def vertexPairs (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun u => (List.finRange n).map fun v => (u, v)

private theorem mem_vertexPairs (p : Fin n × Fin n) : p ∈ vertexPairs n :=
  List.mem_flatMap.mpr ⟨p.1, List.mem_finRange _, List.mem_map.mpr ⟨p.2, List.mem_finRange _, rfl⟩⟩

private theorem vertexPairs_nodup (n : Nat) : (vertexPairs n).Nodup := by
  rw [vertexPairs, List.Nodup, List.pairwise_flatMap]
  refine ⟨fun u _ => ?_, (List.nodup_finRange n).imp ?_⟩
  · rw [List.pairwise_map]
    exact (List.nodup_finRange n).imp (fun different same => different (congrArg Prod.snd same))
  · intro u v different x hx y hy same
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hy
    exact different (congrArg Prod.fst same)

def arrowCount (G : DAG n) : Nat := (vertexPairs n).countP fun (u, v) => G.edge u v

/-- Including every arrow of a graph cannot decrease the arrow count. -/
theorem arrow_count_le_of_subset {G H : DAG n}
    (subset : ∀ u v, G.edge u v = true → H.edge u v = true) : arrowCount G ≤ arrowCount H := by
  unfold arrowCount
  induction vertexPairs n with
  | nil => exact Nat.le_refl _
  | cons edge rest ih =>
    rcases edge with ⟨u, v⟩
    simp only [List.countP_cons]
    by_cases small : G.edge u v = true
    · simp only [small, subset u v small, ite_true]
      exact Nat.add_le_add_right ih _
    · simp only [small]
      exact Nat.le_trans ih (Nat.le_add_right _ _)

private theorem countP_or_of_disjoint {α : Type} (p q : α → Bool) (xs : List α)
    (disjoint : ∀ x, p x = true → q x = false) :
    xs.countP (fun x => p x || q x) = xs.countP p + xs.countP q := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons, ih]
    cases pValue : p x with
    | false => simp [Nat.add_assoc]
    | true => simp [disjoint x pValue, Nat.add_right_comm]

/-- Reversing a covered arrow removes one arrow and inserts one arrow. -/
theorem arrow_count_eq_of_reversal {G H : DAG n} {a b : Fin n} (move : Reversal G H a b) :
    arrowCount G = arrowCount H := by
  let forward : Fin n × Fin n := (a, b)
  let reverse : Fin n × Fin n := (b, a)
  let other : Fin n × Fin n → Bool := fun p => p != forward && p != reverse && G.edge p.1 p.2
  have different : a ≠ b := fun eq => G.no_directed_cycle a (.single (by simpa [eq] using move.forward))
  have oldOpposite : G.edge b a = false := by
    apply Bool.eq_false_iff.mpr
    intro arrow
    exact G.no_directed_cycle a (.extend (.single move.forward) arrow)
  have newOpposite : H.edge a b = false := by
    apply Bool.eq_false_iff.mpr
    intro arrow
    exact H.no_directed_cycle b (.extend (.single move.reverse) arrow)
  have oldCount : arrowCount G = (vertexPairs n).countP other + (vertexPairs n).count forward := by
    rw [arrowCount, List.count_eq_countP, ← countP_or_of_disjoint]
    · apply List.countP_congr
      intro p _
      rcases p with ⟨u, v⟩
      by_cases first : u = a ∧ v = b
      · obtain ⟨rfl, rfl⟩ := first
        simp [other, forward, move.forward]
      · by_cases second : u = b ∧ v = a
        · obtain ⟨rfl, rfl⟩ := second
          simp [other, forward, reverse, different.symm, oldOpposite]
        · simp [other, forward, reverse, first, second]
    · intro p hp
      have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hp).1).1
      simpa using h
  have newCount : arrowCount H = (vertexPairs n).countP other + (vertexPairs n).count reverse := by
    rw [arrowCount, List.count_eq_countP, ← countP_or_of_disjoint]
    · apply List.countP_congr
      intro p _
      rcases p with ⟨u, v⟩
      by_cases second : u = b ∧ v = a
      · obtain ⟨rfl, rfl⟩ := second
        simp [other, reverse, move.reverse]
      · by_cases first : u = a ∧ v = b
        · obtain ⟨rfl, rfl⟩ := first
          simp [other, forward, reverse, different, newOpposite]
        · simp [other, forward, reverse, first, second, move.unchanged u v first second]
    · intro p hp
      have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hp).1).2
      simpa using h
  have singletonCount (p : Fin n × Fin n) : (vertexPairs n).count p = 1 := by
    simp [(vertexPairs_nodup n).count, mem_vertexPairs]
  rw [oldCount, newCount, singletonCount, singletonCount]

end

end OpenCausalScience.Papers.LamEtAl2022
