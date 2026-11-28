module
public import OpenCausalScience.Papers.RaskuttiUhler2018.Minimality
public import OpenCausalScience.Papers.AndrewsEtAl2023.BestMove
public import OpenCausalScience.Papers.LamEtAl2022.EdgeCount

/-! # Oracle sparsest permutation search

[Raskutti and Uhler (2018), Section 2](https://doi.org/10.1002/sta4.183).
The executable search retains all edge-count minimizers. -/

namespace OpenCausalScience.Papers.RaskuttiUhler2018

open Discovery LamEtAl2022
open AndrewsEtAl2023.BestMove (insertions mem_insertions_iff)

@[expose] public section

variable {n : Nat}

def permutations {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: rest => (permutations rest).flatMap (insertions a)

theorem mem_permutations_iff {α : Type} {xs order : List α} :
    order ∈ permutations xs ↔ order.Perm xs := by
  induction xs generalizing order with
  | nil =>
    exact ⟨fun h => List.Perm.of_eq (List.mem_singleton.mp h), fun h => by simp [permutations, h.eq_nil]⟩
  | cons a rest ih =>
    rw [permutations, List.mem_flatMap]
    constructor
    · rintro ⟨inner, present, inserted⟩
      obtain ⟨before, after, rfl, rfl⟩ := mem_insertions_iff.mp inserted
      exact List.perm_middle.trans ((ih.mp present).cons a)
    · intro h
      obtain ⟨before, after, rfl⟩ := List.append_of_mem (h.mem_iff.mpr (List.mem_cons_self ..))
      exact ⟨before ++ after, ih.mpr (List.perm_middle.symm.trans h).cons_inv,
        mem_insertions_iff.mpr ⟨before, after, rfl, rfl⟩⟩

/-- Any DAG has a topological order obtained by sorting its ranks. -/
def topologicalOrder (G : DAG n) : List (Fin n) :=
  (List.finRange n).mergeSort fun u v => decide (G.rank u ≤ G.rank v)

theorem topological_order_perm (G : DAG n) : (topologicalOrder G).Perm (List.finRange n) :=
  List.mergeSort_perm _ _

theorem idxOf_injective {order : List (Fin n)} (complete : order.Perm (List.finRange n))
    (u v : Fin n) (equal : order.idxOf u = order.idxOf v) : u = v := by
  have left := List.idxOf_lt_length_iff.mpr (complete.mem_iff.mpr (List.mem_finRange u))
  have right := List.idxOf_lt_length_iff.mpr (complete.mem_iff.mpr (List.mem_finRange v))
  have equalValues : order[order.idxOf u]'left = order[order.idxOf v]'right := by simp [equal]
  simpa only [List.getElem_idxOf] using equalValues

theorem topological_order_increases (G : DAG n) (u v : Fin n) (arrow : G.edge u v = true) :
    (topologicalOrder G).idxOf u < (topologicalOrder G).idxOf v := by
  let order := topologicalOrder G
  have complete := topological_order_perm G
  have sorted : order.Pairwise (fun x y => G.rank x ≤ G.rank y) := by
    have rel := List.pairwise_mergeSort
      (le := fun x y : Fin n => decide (G.rank x ≤ G.rank y))
      (fun x y z hxy hyz => decide_eq_true (Nat.le_trans (of_decide_eq_true hxy) (of_decide_eq_true hyz)))
      (fun x y => Bool.or_eq_true_iff.mpr ((Nat.le_total (G.rank x) (G.rank y)).elim
        (fun h => .inl (decide_eq_true h)) (fun h => .inr (decide_eq_true h)))) (List.finRange n)
    simpa [order, topologicalOrder] using rel
  have left := List.idxOf_lt_length_iff.mpr (complete.mem_iff.mpr (List.mem_finRange u))
  have right := List.idxOf_lt_length_iff.mpr (complete.mem_iff.mpr (List.mem_finRange v))
  rcases Nat.lt_trichotomy (order.idxOf u) (order.idxOf v) with before | same | after
  · exact before
  · have equal := idxOf_injective complete u v same
    subst v
    exact (G.no_directed_cycle u (.single arrow)).elim
  · have ranks := List.pairwise_iff_getElem.mp sorted (order.idxOf v) (order.idxOf u) right left after
    change G.rank (order[order.idxOf v]'right) ≤ G.rank (order[order.idxOf u]'left) at ranks
    rw [List.getElem_idxOf, List.getElem_idxOf] at ranks
    exact (Nat.not_lt_of_ge ranks (G.edge_increases _ _ arrow)).elim

def graphOfOrder (independent : CIOracle n) (order : List (Fin n)) : DAG n :=
  orderDAG order.idxOf independent

def edgeCost (independent : CIOracle n) (order : List (Fin n)) : Nat :=
  arrowCount (graphOfOrder independent order)

def allOrders (n : Nat) : List (List (Fin n)) := permutations (List.finRange n)

private theorem length_insertions {α : Type} (a : α) (xs : List α) :
    (insertions a xs).length = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [insertions, ih]

private theorem sum_constant {α : Type} (xs : List α) (value : Nat) :
    (xs.map (fun _ => value)).sum = xs.length * value := by
  induction xs with
  | nil => simp
  | cons _ _ ih => simp [ih, Nat.succ_mul, Nat.add_comm]

private theorem length_permutations {α : Type} (xs : List α) :
    (permutations xs).length = ((List.range xs.length).map Nat.succ).prod := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    rw [permutations, List.length_flatMap]
    have equallyLong : ((permutations rest).map fun order => (insertions a order).length) =
        (permutations rest).map (fun _ => rest.length + 1) := by
      apply List.map_congr_left
      intro order mem
      rw [length_insertions, (mem_permutations_iff.mp mem).length_eq]
    rw [equallyLong, sum_constant, ih, List.length_cons, List.range_succ,
      List.map_append, List.prod_append]
    simp

/-- The complete list has n! entries, the depth bound used by oracle GRaSP. -/
theorem all_orders_length (n : Nat) : (allOrders n).length = ((List.range n).map Nat.succ).prod := by
  rw [allOrders, length_permutations]
  simp

def optimalCount (independent : CIOracle n) : Nat :=
  ((allOrders n).map (edgeCost independent)).min?.getD 0

def sparsestOrders (independent : CIOracle n) : List (List (Fin n)) :=
  (allOrders n).filter fun order => edgeCost independent order == optimalCount independent

private theorem optimal_count_is_minimum (independent : CIOracle n) :
    (∃ order, order.Perm (List.finRange n) ∧ edgeCost independent order = optimalCount independent) ∧
      ∀ order, order.Perm (List.finRange n) → optimalCount independent ≤ edgeCost independent order := by
  let costs := (allOrders n).map (edgeCost independent)
  have present : edgeCost independent (List.finRange n) ∈ costs :=
    List.mem_map.mpr ⟨_, mem_permutations_iff.mpr (.refl _), rfl⟩
  have existsMin : ∃ c, costs.min? = some c := by
    cases found : costs.min? with
    | none => rw [List.min?_eq_none_iff.mp found] at present; cases present
    | some c => exact ⟨c, rfl⟩
  obtain ⟨c, found⟩ := existsMin
  have ⟨chosen, lower⟩ := List.min?_eq_some_iff.mp found
  obtain ⟨order, inOrders, equal⟩ := List.mem_map.mp chosen
  have opt : optimalCount independent = c := by
    change costs.min?.getD 0 = c
    rw [found]
    rfl
  exact ⟨⟨order, mem_permutations_iff.mp inOrders, equal.trans opt.symm⟩,
    fun candidate isOrder => opt.symm ▸ lower _ (List.mem_map.mpr ⟨_, mem_permutations_iff.mpr isOrder, rfl⟩)⟩

theorem sparsest_orders_nonempty (independent : CIOracle n) : sparsestOrders independent ≠ [] := by
  obtain ⟨⟨order, perm, minCost⟩, _⟩ := optimal_count_is_minimum independent
  have present : order ∈ sparsestOrders independent :=
    List.mem_filter.mpr ⟨mem_permutations_iff.mpr perm, beq_iff_eq.mpr minCost⟩
  intro empty
  rw [empty] at present
  cases present

theorem mem_sparsest_orders_iff (independent : CIOracle n) (order : List (Fin n)) :
    order ∈ sparsestOrders independent ↔ order.Perm (List.finRange n) ∧
      ∀ other, other.Perm (List.finRange n) → edgeCost independent order ≤ edgeCost independent other := by
  obtain ⟨⟨witness, isOrder, optimum⟩, lower⟩ := optimal_count_is_minimum independent
  rw [sparsestOrders, List.mem_filter, beq_iff_eq, allOrders, mem_permutations_iff]
  refine and_congr_right fun perm => ⟨fun equal other hp => equal.symm ▸ lower other hp, ?_⟩
  intro minimal
  exact Nat.le_antisymm (optimum ▸ minimal witness isOrder) (lower order perm)

theorem sparsest_cost_le_of_markov {G : DAG n} {independent : CIOracle n}
    (markov : IsMarkov G independent) {order : List (Fin n)} (selected : order ∈ sparsestOrders independent) :
    edgeCost independent order ≤ arrowCount G := by
  have lower := ((mem_sparsest_orders_iff independent order).mp selected).2 _ (topological_order_perm G)
  exact Nat.le_trans lower (arrow_count_le_of_subset fun a b arrow =>
    orderDAG_subgraph_of_markov _ (idxOf_injective (topological_order_perm G))
      (topological_order_increases G) markov arrow)

end

end OpenCausalScience.Papers.RaskuttiUhler2018
