module
public import OpenCausalScience.Discovery.OrderedMarkov
public import OpenCausalScience.Papers.LamEtAl2022.TuckSequences

/-! # Adjacent transpositions of an order-induced DAG

Supplement Lemmas B.3–B.4 of Lam, Andrews and Ramsey describe swaps of
consecutive variables and moving the head of a covered arrow forward.
-/

namespace OpenCausalScience.Papers.LamEtAl2022

open Probability.CI Discovery
open RaskuttiUhler2018

@[expose] public section

variable {n : Nat}

private theorem swap_causal_order {G : DAG n} (pre post : List (Fin n)) {a b : Fin n}
    (old : CausalOrder G (pre ++ a :: b :: post)) (noArrow : G.edge a b = false) :
    CausalOrder G (pre ++ b :: a :: post) := by
  obtain ⟨preOK, suffixOK, cross⟩ := List.pairwise_append.mp old
  obtain ⟨aAll, tailOK⟩ := List.pairwise_cons.mp suffixOK
  obtain ⟨bAll, postOK⟩ := List.pairwise_cons.mp tailOK
  apply List.pairwise_append.mpr
  refine ⟨preOK, List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_, postOK⟩⟩, ?_⟩
  · intro u inTail
    rcases List.mem_cons.mp inTail with rfl | inPost
    · exact noArrow
    · exact bAll u inPost
  · intro u inPost
    exact aAll u (List.mem_cons_of_mem _ inPost)
  · intro u inPre v inNew
    exact cross u inPre v (((List.Perm.swap a b post).mem_iff).mp inNew)

theorem adjacent_swap_of_nonedge {J : Relation n} {independent : CIOracle n}
    (g : Graphoid J) (agrees : MatchesOracle J independent) (pre post : List (Fin n))
    (a b : Fin n) (valid : VertexOrder (pre ++ a :: b :: post))
    (noArrow : (orderDAG (pre ++ a :: b :: post).idxOf independent).edge a b = false) :
    (orderDAG (pre ++ a :: b :: post).idxOf independent).edge =
      (orderDAG (pre ++ b :: a :: post).idxOf independent).edge := by
  let order := pre ++ a :: b :: post
  let next := pre ++ b :: a :: post
  let G := orderDAG order.idxOf independent
  let H := orderDAG next.idxOf independent
  have nextValid : VertexOrder next := valid.of_perm ((List.Perm.swap a b post).append_left pre)
  have nextCausal : CausalOrder G next :=
    swap_causal_order pre post (valid.causal_order_iff.mpr G.edge_increases) noArrow
  have markovG := induced_order_is_markov g agrees order.idxOf valid.idx_unique
  have markovH := induced_order_is_markov g agrees next.idxOf nextValid.idx_unique
  have sub (u v : Fin n) (arrow : H.edge u v = true) : G.edge u v = true :=
    orderDAG_subgraph_of_markov next.idxOf nextValid.idx_unique
      (nextValid.causal_order_iff.mp nextCausal) markovG arrow
  exact (markov_subgraph_edges_eq order.idxOf valid.idx_unique sub markovH).symm

private theorem pair_positions (pre post : List (Fin n)) {a b : Fin n}
    (aFresh : a ∉ pre) (bFresh : b ∉ pre) (distinct : a ≠ b) :
    (pre ++ a :: b :: post).idxOf a = pre.length ∧
      (pre ++ a :: b :: post).idxOf b = pre.length + 1 := by
  constructor
  · simp [List.idxOf_append, aFresh]
  · simp [List.idxOf_append, List.idxOf_cons, bFresh, distinct, Nat.add_comm]

private theorem second_predecessors_except_first (pre post : List (Fin n)) {a b : Fin n}
    (aFresh : a ∉ pre) (bFresh : b ∉ pre) (distinct : a ≠ b) :
    predecessorsExcept (pre ++ a :: b :: post).idxOf a b = fun v => pre.contains v := by
  funext v
  have pos := (pair_positions pre post aFresh bFresh distinct).2
  by_cases inPre : v ∈ pre
  · have noA : v ≠ a := fun h => aFresh (h ▸ inPre)
    have bound := List.idxOf_lt_length_iff.mpr inPre
    have smaller : pre.idxOf v < pre.length + 1 := by omega
    simp [predecessorsExcept, List.idxOf_append, pos, inPre, noA, smaller]
  · by_cases vA : v = a
    · simp [predecessorsExcept, vA, aFresh]
    · by_cases vB : v = b
      · simp [predecessorsExcept, vB, bFresh]
      · have after :
            ¬ (pre ++ a :: b :: post).idxOf v < pre.length + 1 := by
          rw [List.idxOf_append]
          simp only [inPre, ite_false, List.idxOf_cons, beq_iff_eq, Ne.symm vA, Ne.symm vB, ite_false]
          omega
        simp [predecessorsExcept, pos, after, inPre]

/-- Two adjacent vertices can be swapped without changing the induced DAG
exactly when their singleton CI holds given the preceding block. -/
theorem adjacent_swap_iff_ci {J : Relation n} {independent : CIOracle n}
    (g : Graphoid J) (agrees : MatchesOracle J independent) (pre post : List (Fin n))
    (a b : Fin n) (covers : ∀ v, v ∈ pre ++ a :: b :: post)
    (unique : (pre ++ a :: b :: post).Nodup) :
    (orderDAG (pre ++ a :: b :: post).idxOf independent).edge =
        (orderDAG (pre ++ b :: a :: post).idxOf independent).edge ↔
      independent a b (fun v => pre.contains v) = true := by
  let old := pre ++ a :: b :: post
  let new := pre ++ b :: a :: post
  let G := orderDAG old.idxOf independent
  let H := orderDAG new.idxOf independent
  have swap : new.Perm old := (List.Perm.swap a b post).append_left pre
  have oldValid : VertexOrder old := ⟨covers, unique⟩
  have newValid := oldValid.of_perm swap
  obtain ⟨_, tailDistinct, noCross⟩ := List.nodup_append.mp unique
  have aFresh : a ∉ pre := fun present => noCross a present a (by simp) rfl
  have bFresh : b ∉ pre := fun present => noCross b present b (by simp) rfl
  have different : a ≠ b := by
    intro eq
    exact (List.nodup_cons.mp tailDistinct).1 (by simp [eq])
  have oldPos := pair_positions pre post aFresh bFresh different
  have newPos := pair_positions pre post bFresh aFresh different.symm
  have oldEarlier : old.idxOf a < old.idxOf b := by
    change (pre ++ a :: b :: post).idxOf a < (pre ++ a :: b :: post).idxOf b
    rw [oldPos.1, oldPos.2]
    omega
  have newEarlier : new.idxOf b < new.idxOf a := by
    change (pre ++ b :: a :: post).idxOf b < (pre ++ b :: a :: post).idxOf a
    rw [newPos.1, newPos.2]
    omega
  have localTest := second_predecessors_except_first pre post bFresh aFresh different.symm
  have absent_old : G.edge b a = false := by
    apply Bool.eq_false_iff.mpr
    intro present
    exact Nat.lt_asymm oldEarlier (((orderDAG_edge_iff _ _ _ _).mp present).1)
  have newTest : H.edge b a = true ↔ independent a b (fun v => pre.contains v) = false := by
    change (orderDAG (pre ++ b :: a :: post).idxOf independent).edge b a = true ↔ _
    rw [orderDAG_edge_iff, localTest]
    exact ⟨And.right, fun ci => ⟨newEarlier, ci⟩⟩
  change G.edge = H.edge ↔ _
  constructor
  · intro edges
    cases test : independent a b (fun v => pre.contains v)
    · have present := newTest.mpr test
      rw [← edges, absent_old] at present
      contradiction
    · rfl
  · intro test
    have noBack : H.edge b a = false := by
      apply Bool.eq_false_iff.mpr
      intro included
      exact Bool.false_ne_true ((newTest.mp included).symm.trans test)
    exact (adjacent_swap_of_nonedge g agrees pre post b a newValid noBack).symm

private theorem slide_past_nonparents_reverse {J : Relation n} {independent : CIOracle n}
    (g : Graphoid J) (agrees : MatchesOracle J independent) (pre revMiddle post : List (Fin n))
    (b : Fin n) (valid : VertexOrder (pre ++ revMiddle.reverse ++ b :: post))
    (absent : ∀ u ∈ revMiddle,
      (orderDAG (pre ++ revMiddle.reverse ++ b :: post).idxOf independent).edge u b = false) :
    (orderDAG (pre ++ revMiddle.reverse ++ b :: post).idxOf independent).edge =
      (orderDAG (pre ++ b :: revMiddle.reverse ++ post).idxOf independent).edge := by
  induction revMiddle generalizing post with
  | nil => simp
  | cons m revTail ih =>
    let earlierBlock := pre ++ revTail.reverse
    have shape : pre ++ (m :: revTail).reverse ++ b :: post = earlierBlock ++ m :: b :: post := by
      simp [earlierBlock, List.reverse_cons, List.append_assoc]
    rw [shape] at valid absent ⊢
    have middle : (orderDAG (earlierBlock ++ m :: b :: post).idxOf independent).edge m b = false :=
      absent m List.mem_cons_self
    have swapEdges := adjacent_swap_of_nonedge g agrees earlierBlock post m b valid middle
    have swapped := valid.of_perm ((List.Perm.swap m b post).append_left earlierBlock)
    have shifted := ih (m :: post) swapped (by
      intro u earlier
      change (orderDAG (earlierBlock ++ b :: m :: post).idxOf independent).edge u b = false
      rw [← swapEdges]
      exact absent u (List.mem_cons_of_mem _ earlier))
    refine swapEdges.trans ?_
    simpa [earlierBlock, List.reverse_cons, List.append_assoc] using shifted

theorem slide_past_nonparents {J : Relation n} {independent : CIOracle n}
    (g : Graphoid J) (agrees : MatchesOracle J independent) (pre middle post : List (Fin n))
    (b : Fin n) (valid : VertexOrder (pre ++ middle ++ b :: post))
    (absent : ∀ u ∈ middle,
      (orderDAG (pre ++ middle ++ b :: post).idxOf independent).edge u b = false) :
    (orderDAG (pre ++ middle ++ b :: post).idxOf independent).edge =
      (orderDAG (pre ++ b :: middle ++ post).idxOf independent).edge := by
  have validReverse : VertexOrder (pre ++ middle.reverse.reverse ++ b :: post) := by simpa using valid
  have h := slide_past_nonparents_reverse g agrees pre middle.reverse post b validReverse (by
    intro u member
    simpa using absent u (by simpa using member))
  simpa using h

/-- Moving a covered-arrow head directly after its tail preserves the
entire order-induced DAG. This is Supplement Lemma B.4. -/
theorem covered_head_slide_preserves_graph {J : Relation n} {independent : CIOracle n}
    (g : Graphoid J) (agrees : MatchesOracle J independent) (s : OrderSplit (Fin n))
    (valid : VertexOrder s.original)
    (cov : Covered (orderDAG s.original.idxOf independent) s.tailVertex s.headVertex) :
    (orderDAG s.original.idxOf independent).edge =
      (orderDAG (s.pre ++ [s.tailVertex, s.headVertex] ++ s.between ++ s.suffix).idxOf
        independent).edge := by
  let G := orderDAG s.original.idxOf independent
  let earlierBlock := s.pre ++ [s.tailVertex]
  have causal := valid.causal_order_iff.mpr G.edge_increases
  have shape : s.original = earlierBlock ++ s.between ++ s.headVertex :: s.suffix := by
    simp [OrderSplit.original, earlierBlock, List.append_assoc]
  have unique : (earlierBlock ++ (s.between ++ [s.headVertex] ++ s.suffix)).Nodup := by
    simpa [OrderSplit.original, earlierBlock, List.append_assoc] using valid.nodup
  have noCross := (List.nodup_append.mp unique).2.2
  have absent (u : Fin n) (member : u ∈ s.between) : G.edge u s.headVertex = false := by
    apply Bool.eq_false_iff.mpr
    intro arrow
    have early := covered_parent_in_early_segment s causal valid.covers cov arrow
    exact noCross u early u (by simp [member]) rfl
  have moved := slide_past_nonparents g agrees earlierBlock s.between s.suffix s.headVertex
    (shape ▸ valid) (fun u h => shape ▸ absent u h)
  simpa [OrderSplit.original, earlierBlock, List.append_assoc] using moved

end

end OpenCausalScience.Papers.LamEtAl2022
