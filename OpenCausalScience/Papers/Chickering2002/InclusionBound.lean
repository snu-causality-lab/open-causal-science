module
public import OpenCausalScience.Papers.Chickering2002.InclusionProgress

/-! The operation count in Chickering (2002), Theorem 4. -/

namespace OpenCausalScience.Papers.Chickering2002

open LamEtAl2022 Chickering1995.CoveredReversal Chickering1995.FindEdge
open Chickering1995.Transformation VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n : Nat} {G H K : DAG n}

private theorem countP_mono {α : Type} {p q : α → Bool}
    (sub : ∀ a, p a = true → q a = true) (xs : List α) : xs.countP p ≤ xs.countP q := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons a tail ih =>
    simp only [List.countP_cons]
    cases ha : p a with
    | false => cases q a <;> simp_all <;> omega
    | true => simp [sub a ha, ih]

private theorem countP_change {α : Type} [DecidableEq α] {p q : α → Bool} {a : α}
    (atP : p a = true) (atQ : q a = false) (away : ∀ b, b ≠ a → p b = q b)
    (xs : List α) :
    xs.countP p = xs.countP q + xs.count a := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    by_cases found : head = a
    · subst head
      simp [atP, atQ, ih, Nat.add_assoc]
    · simp only [List.countP_cons, List.count_cons, beq_eq_false_iff_ne.mpr found,
        Bool.false_eq_true, ↓reduceIte, Nat.add_zero, away head found, ih]
      omega

private theorem pairs_count (a : Fin n × Fin n) : (vertexPairs n).count a = 1 := by
  simp [(vertexPairs_nodup n).count, mem_vertexPairs a]

def missingAdjacency (G H : DAG n) (uv : Fin n × Fin n) : Bool :=
  H.edge uv.1 uv.2 && !(G.edge uv.1 uv.2 || G.edge uv.2 uv.1)

/-- The number of target arrows absent in both directions in the current DAG. -/
def missingAdjacencies (G H : DAG n) : Nat :=
  (vertexPairs n).countP (missingAdjacency G H)

private theorem reversal_missing_eq {u v : Fin n} (reversal : Reversal G K u v) :
    missingAdjacencies G H = missingAdjacencies K H := by
  have same := sameDConnections_of_reversal reversal
  have forward := IndependenceMap.of_same_dConnections same
  have backward := IndependenceMap.of_same_dConnections
    (show SameDConnections K G from fun s x y => (same s x y).symm)
  apply List.countP_congr
  intro p _
  rcases p with ⟨x, y⟩
  have adjacentEq : (G.edge x y || G.edge y x) = (K.edge x y || K.edge y x) :=
    Bool.eq_iff_iff.mpr (Bool.or_eq_true_iff.trans (Iff.trans
      ⟨forward.adjacent, backward.adjacent⟩ Bool.or_eq_true_iff.symm))
  simp [missingAdjacency, adjacentEq]

private theorem insertion_missing_decreases {u v : Fin n}
    (fresh : G.edge u v = false) (add : G.IsInsertion K u v) (map : IndependenceMap K H) :
    missingAdjacencies K H + 1 = missingAdjacencies G H := by
  have arrow := (add u v).mpr (.inr ⟨rfl, rfl⟩)
  have opposite : G.edge v u = false := by
    apply Bool.eq_false_iff.mpr
    intro backwards
    exact K.no_directed_cycle u (.extend (.single arrow) ((add v u).mpr (.inl backwards)))
  have oldTarget := map.adjacent (x := u) (y := v) (.inl arrow)
  have one (targetTail targetHead : Fin n)
      (reach : (targetTail = u ∧ targetHead = v) ∨ (targetTail = v ∧ targetHead = u))
      (targetArrow : H.edge targetTail targetHead = true) :
      missingAdjacencies K H + 1 = missingAdjacencies G H := by
    have targetBackward : H.edge targetHead targetTail = false := Bool.eq_false_iff.mpr
      fun edge => H.no_directed_cycle targetTail (.extend (.single targetArrow) edge)
    have before : missingAdjacency G H (targetTail, targetHead) = true := by
      rcases reach with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · simp [missingAdjacency, targetArrow, fresh, opposite]
      · simp [missingAdjacency, targetArrow, fresh, opposite]
    have after : missingAdjacency K H (targetTail, targetHead) = false := by
      rcases reach with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [missingAdjacency, arrow]
    have unchanged (pair : Fin n × Fin n) (elsewhere : pair ≠ (targetTail, targetHead)) :
        missingAdjacency G H pair = missingAdjacency K H pair := by
      rcases pair with ⟨a, b⟩
      have sameAt (pairs : ¬ (a = u ∧ b = v)) : K.edge a b = G.edge a b :=
        Bool.eq_iff_iff.mpr (by simp [add a b, pairs])
      by_cases first : a = u ∧ b = v
      · obtain ⟨rfl, rfl⟩ := first
        rcases reach with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact (elsewhere rfl).elim
        · simp [missingAdjacency, targetBackward]
      · by_cases second : b = u ∧ a = v
        · obtain ⟨rfl, rfl⟩ := second
          rcases reach with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
          · simp [missingAdjacency, targetBackward]
          · exact (elsewhere rfl).elim
        · have other : K.edge b a = G.edge b a :=
            Bool.eq_iff_iff.mpr (by simp [add b a, second])
          simp [missingAdjacency, sameAt first, other]
    rw [missingAdjacencies, missingAdjacencies, countP_change before after unchanged,
      pairs_count]
  exact oldTarget.elim (one u v (.inl ⟨rfl,rfl⟩)) (one v u (.inr ⟨rfl,rfl⟩))

private theorem insertion_disagreement_bound {u v : Fin n}
    (add : G.IsInsertion K u v) :
    orientationDisagreements K H ≤ orientationDisagreements G H + 1 := by
  let old : Fin n × Fin n → Bool := fun (a, b) => G.edge a b && H.edge b a
  let new : Fin n × Fin n → Bool := fun (a, b) => K.edge a b && H.edge b a
  let allowed : Fin n × Fin n → Bool := fun p => old p || decide (p = (u, v))
  have sub (p : Fin n × Fin n) (kept : new p = true) : allowed p = true := by
    rcases p with ⟨a,b⟩
    obtain ⟨edge, target⟩ := Bool.and_eq_true_iff.mp kept
    rcases (add a b).mp edge with prior | ⟨rfl,rfl⟩
    · simp [allowed, old, prior, target]
    · simp [allowed]
  have count : (vertexPairs n).countP allowed ≤ (vertexPairs n).countP old + 1 := by
    by_cases present : old (u,v) = true
    · have same : (vertexPairs n).countP allowed = (vertexPairs n).countP old := by
        apply List.countP_congr
        intro p _
        by_cases matchPair : p = (u,v)
        · subst p
          simp [allowed, present]
        · simp [allowed, matchPair]
      omega
    · have before : allowed (u,v) = true := by simp [allowed]
      have after : old (u,v) = false := Bool.eq_false_iff.mpr present
      have away (p : Fin n × Fin n) (different : p ≠ (u,v)) : allowed p = old p := by
        simp [allowed, different]
      simp only [countP_change before after away, pairs_count, Nat.le_refl]
  exact Nat.le_trans (countP_mono sub (vertexPairs n)) count

/-- The bound in the paper's notation is `r + 2m`. -/
def operationBound (G H : DAG n) : Nat :=
  orientationDisagreements G H + 2 * missingAdjacencies G H

theorem ForwardStep.decreases_bound (step : ForwardStep H G K) :
    operationBound K H < operationBound G H := by
  cases step with
  | reverse chosen reversal _ =>
    have missing := reversal_missing_eq (H := H) reversal
    have disagrees := reversal_toward_target_decreases_disagreement reversal chosen
    unfold operationBound
    omega
  | insert fresh add map =>
    have missing := insertion_missing_decreases fresh add map
    have disagrees := insertion_disagreement_bound (H := H) add
    unfold operationBound
    omega

/-- Forward operations counted individually, retaining the target inclusion at each step. -/
inductive ForwardSequence (target : DAG n) : DAG n → Nat → Prop
  | done {A} : A.edge = target.edge → ForwardSequence target A 0
  | next {A B k} : ForwardStep target A B → ForwardSequence target B k →
      ForwardSequence target A (k + 1)

theorem ForwardSequence.to_backward {k : Nat} (path : ForwardSequence H G k) :
    BackwardSequence G H := by
  induction path with
  | done same => exact .done same.symm
  | next step _ ih => exact ih.append step.backward

theorem bounded_forward_sequence_of_progress
    (progress : ∀ A B : DAG n, IndependenceMap A B → A.edge ≠ B.edge →
      ∃ C, ForwardStep B A C) (G H : DAG n) (map : IndependenceMap G H) :
    ∃ k, k ≤ operationBound G H ∧ ForwardSequence H G k := by
  classical
  by_cases same : G.edge = H.edge
  · exact ⟨0, Nat.zero_le _, .done same⟩
  · obtain ⟨next, step⟩ := progress G H map same
    obtain ⟨k, bound, path⟩ := bounded_forward_sequence_of_progress progress next H step.map_held
    exact ⟨k + 1, Nat.add_one_le_iff.mpr (Nat.lt_of_le_of_lt bound step.decreases_bound), .next step path⟩
termination_by operationBound G H
decreasing_by exact step.decreases_bound

end

end OpenCausalScience.Papers.Chickering2002
