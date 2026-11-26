module
public import OpenCausalScience.Graph.DAG

/-! Single-edge edits on ranked finite DAGs. For insertion, move the
ancestors of the source ahead of the other vertices. -/

namespace OpenCausalScience.DAG

@[expose] public section

variable {n : Nat}

private theorem prepend_walk {G : DAG n} {u v w : Fin n}
    (first : G.edge u v = true) (rest : G.DirectedWalk v w) :
    G.DirectedWalk u w := by
  induction rest with
  | single edge => exact .extend (.single first) edge
  | extend _ edge ih => exact .extend ih edge

def ancestor (G : DAG n) (u v : Fin n) : Prop :=
  u = v ∨ G.DirectedWalk u v

theorem ancestor_of_edge {G : DAG n} {u v w : Fin n}
    (first : G.edge u v = true) (rest : G.ancestor v w) : G.ancestor u w := by
  rcases rest with rfl | walk
  · exact .inr (.single first)
  · exact .inr (prepend_walk first walk)

def rankBound (G : DAG n) : Nat :=
  ((List.finRange n).foldr (fun v bound => max (G.rank v) bound) 0) + 1

private theorem rank_le_fold (rank : Fin n → Nat) (u : Fin n) (xs : List (Fin n))
    (mem : u ∈ xs) : rank u ≤ xs.foldr (fun v bound => max (rank v) bound) 0 := by
  induction xs with
  | nil => cases mem
  | cons v rest ih =>
    rcases List.mem_cons.mp mem with rfl | usingRest
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih usingRest) (Nat.le_max_right _ _)

theorem rank_lt_bound (G : DAG n) (u : Fin n) : G.rank u < G.rankBound :=
  Nat.lt_succ_of_le (rank_le_fold G.rank u _ (List.mem_finRange u))

/-- Removing one arrow preserves the original acyclicity ranks. -/
def deleteArrow (G : DAG n) (source target : Fin n) : DAG n where
  edge u v := G.edge u v && !(u == source && v == target)
  rank := G.rank
  edge_increases u v edge := G.edge_increases u v (Bool.and_eq_true_iff.mp edge).1

theorem deleteArrow_edge_iff (G : DAG n) (x y u v : Fin n) :
    (G.deleteArrow x y).edge u v = true ↔ G.edge u v = true ∧ ¬ (u = x ∧ v = y) := by
  by_cases same : u = x <;> simp [deleteArrow, same]

def IsInsertion (G H : DAG n) (x y : Fin n) : Prop :=
  ∀ u v, H.edge u v = true ↔ G.edge u v = true ∨ (u = x ∧ v = y)

theorem exists_insertion_iff (G : DAG n) {x y : Fin n} (distinct : x ≠ y) :
    (∃ H : DAG n, G.IsInsertion H x y) ↔ ¬ G.DirectedWalk y x := by
  classical
  constructor
  · rintro ⟨H, edits⟩ reverse
    have keep {u v} (walk : G.DirectedWalk u v) : H.DirectedWalk u v := by
      induction walk with
      | single edge => exact .single ((edits _ _).mpr (.inl edge))
      | extend _ edge ih => exact .extend ih ((edits _ _).mpr (.inl edge))
    exact H.no_directed_cycle y (.extend (keep reverse) ((edits x y).mpr (.inr ⟨rfl, rfl⟩)))
  · intro noReverse
    have out : ¬ G.ancestor y x := fun h => h.elim distinct.symm noReverse
    let newRank (v : Fin n) := if G.ancestor v x then G.rank v else G.rank v + G.rankBound
    have increasing u v (edge : G.edge u v = true ∨ (u = x ∧ v = y)) :
        newRank u < newRank v := by
      rcases edge with original | ⟨sameU, sameV⟩
      · have before := G.edge_increases _ _ original
        by_cases inside : G.ancestor v x
        · have parent := ancestor_of_edge original inside
          simpa [newRank, inside, parent] using before
        · by_cases parent : G.ancestor u x
          · simp [newRank, inside, parent]
            omega
          · simp [newRank, inside, parent, before]
      · subst u
        subst v
        have inside : G.ancestor x x := .inl rfl
        have bound := G.rank_lt_bound x
        simp [newRank, inside, out]
        omega
    exact ⟨⟨fun u v => decide (G.edge u v = true ∨ (u = x ∧ v = y)),
      newRank, fun u v edge => increasing u v (of_decide_eq_true edge)⟩,
      fun u v => decide_eq_true_iff⟩

end
end OpenCausalScience.DAG
