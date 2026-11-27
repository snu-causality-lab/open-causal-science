module
public import Std

/-! # Running intersection from a perfect elimination order

The input order is the order of the finite vertex labels. A bag is
a vertex and its later neighbours. Each nonroot bag attaches to the
bag of its earliest later neighbour. Restricting to maximal bags
and the reverse characterization are outside this construction.
Source: https://doi.org/10.1017/S1446788700027300
-/

namespace OpenCausalScience.Papers.LauritzenSpeedVijayan1984.EliminationBags

@[expose] public section

variable {n : Nat}

structure UndirectedGraph (n : Nat) where
  edge : Fin n → Fin n → Bool
  symmetric : ∀ u v, edge u v = edge v u
  loopFree : ∀ v, edge v v = false

def PerfectElimination (G : UndirectedGraph n) : Prop :=
  ∀ x u v, x < u → x < v → u ≠ v →
    G.edge x u = true → G.edge x v = true → G.edge u v = true

def LaterNeighbor (G : UndirectedGraph n) (u v : Fin n) : Prop :=
  u < v ∧ G.edge u v = true

def InBag (G : UndirectedGraph n) (bag member : Fin n) : Prop :=
  member = bag ∨ LaterNeighbor G bag member

def parent (G : UndirectedGraph n) (u : Fin n) : Option (Fin n) :=
  (List.finRange n).find? (fun v => decide (u < v) && G.edge u v)

theorem parent_is_later_neighbor {G : UndirectedGraph n} {u v : Fin n}
    (p : parent G u = some v) : LaterNeighbor G u v := by
  have found := List.find?_some p
  simpa only [LaterNeighbor, Bool.and_eq_true, decide_eq_true_eq] using found

theorem parent_is_first {G : UndirectedGraph n} {u v w : Fin n}
    (p : parent G u = some v) (later : LaterNeighbor G u w) : v ≤ w := by
  obtain ⟨_, i, inside, equal, prior⟩ := List.find?_eq_some_iff_getElem.mp p
  have indexVal (j : Nat) (valid : j < (List.finRange n).length) :
      ((List.finRange n)[j]).val = j := by rw [List.getElem_finRange]; rfl
  have value : v.val = i := by rw [← equal, indexVal]
  by_cases ordered : v ≤ w
  · exact ordered
  · have earlier : w.val < i := by
      have notLe : ¬ v.val ≤ w.val := ordered
      omega
    have member := prior w.val earlier
    have atIndex : (List.finRange n)[w.val]'(by omega) = w := Fin.ext (indexVal _ _)
    rw [atIndex] at member
    simp [later.1, later.2] at member

theorem has_parent_of_later_neighbor {G : UndirectedGraph n} {u v : Fin n}
    (later : LaterNeighbor G u v) : ∃ w, parent G u = some w := by
  cases h : parent G u with
  | none =>
    have none := List.find?_eq_none.mp h v (List.mem_finRange v)
    simp [later.1, later.2] at none
  | some w => exact ⟨w, rfl⟩

theorem separator_in_parent_bag {G : UndirectedGraph n}
    (perfect : PerfectElimination G) {u p v : Fin n}
    (parentOf : parent G u = some p) (later : LaterNeighbor G u v) : InBag G p v := by
  by_cases same : v = p
  · exact .inl same
  · have minimal := parent_is_first parentOf later
    have pv : p < v := by
      have le : p.val ≤ v.val := minimal
      have distinct : p.val ≠ v.val := fun equal => same (Fin.ext equal.symm)
      show p.val < v.val
      omega
    have up := parent_is_later_neighbor parentOf
    exact .inr ⟨pv, perfect u p v up.1 later.1 (Ne.symm same) up.2 later.2⟩

inductive BagPath (G : UndirectedGraph n) (member : Fin n) : Fin n → Fin n → Prop
  | done {i} : InBag G i member → BagPath G member i i
  | next {i p top} : InBag G i member → parent G i = some p →
      BagPath G member p top → BagPath G member i top

/-- Every occurrence of a vertex can reach its own bag, without
leaving the bags containing that vertex. -/
theorem running_intersection {G : UndirectedGraph n} (perfect : PerfectElimination G)
    {i v : Fin n} (appears : InBag G i v) : BagPath G v i v := by
  have connected : ∀ k j, n - j.val = k → InBag G j v → BagPath G v j v := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro j rank hj
      rcases hj with rfl | later
      · exact .done (.inl rfl)
      · obtain ⟨p, parentOf⟩ := has_parent_of_later_neighbor later
        have jp : j.val < p.val := (parent_is_later_neighbor parentOf).1
        have progress : n - p.val < k := by have := p.isLt; omega
        exact .next (.inr later) parentOf
          (ih _ progress p rfl (separator_in_parent_bag perfect parentOf later))
  exact connected _ i rfl appears

theorem bag_is_clique {G : UndirectedGraph n} (perfect : PerfectElimination G)
    {i u v : Fin n} (inU : InBag G i u) (inV : InBag G i v) (distinct : u ≠ v) :
    G.edge u v = true := by
  rcases inU with rfl | uLater
  · rcases inV with rfl | vLater
    · exact (distinct rfl).elim
    · exact vLater.2
  · rcases inV with rfl | vLater
    · rw [G.symmetric]
      exact uLater.2
    · exact perfect i u v uLater.1 vLater.1 distinct uLater.2 vLater.2

end
end OpenCausalScience.Papers.LauritzenSpeedVijayan1984.EliminationBags
