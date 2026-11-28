module
public import OpenCausalScience.Papers.LamEtAl2022.TuckSequences

/-! # Improving TSP traces

An improving TSP trace has a plateau of covered reversals through
SGS-minimal DAGs. Its final reversal is followed by strict deletion
into an SGS-minimal DAG. A trace can be shortened to avoid repeated
DAG edge sets before it is translated to executable GRaSP moves. -/

namespace OpenCausalScience.Papers.LamEtAl2022

open Discovery Chickering1995.CoveredReversal Chickering2002 RaskuttiUhler2018

@[expose] public section

variable {n : Nat}

/-- The terminal state records the target of the final deletion phase. -/
inductive ImprovingTSP (independent : CIOracle n) : DAG n → List (DAG n) → Prop
  | turn {G H D a b} : Reversal G H a b → ArrowSubset D H → arrowCount D < arrowCount H →
      SGSMinimal independent D → ImprovingTSP independent G [D]
  | plateau {G H rest a b} : Reversal G H a b → SGSMinimal independent H →
      ImprovingTSP independent H rest → ImprovingTSP independent G (H :: rest)

private theorem reversal_of_same_source_arrows {G H K : DAG n} {a b : Fin n}
    (rev : Reversal G H a b) (eq : K.edge = G.edge) : Reversal K H a b := by
  refine ⟨?_, rev.reverse, ?_, ?_⟩
  · rw [eq]
    exact rev.forward
  · intro u v h₁ h₂
    rw [eq]
    exact rev.unchanged u v h₁ h₂
  · intro u h₁ h₂
    rw [eq]
    exact rev.parents u h₁ h₂

theorem ImprovingTSP.rebase {independent : CIOracle n} {G H : DAG n} {steps : List (DAG n)}
    (trace : ImprovingTSP independent G steps) (eq : H.edge = G.edge) :
    ImprovingTSP independent H steps := by
  cases trace with
  | turn r subset fewer sgs => exact .turn (reversal_of_same_source_arrows r eq) subset fewer sgs
  | plateau r sgs rest => exact .plateau (reversal_of_same_source_arrows r eq) sgs rest

private theorem arrows_eq_count_eq {G H : DAG n} (eq : G.edge = H.edge) :
    arrowCount G = arrowCount H := by simp [arrowCount, eq]

private theorem ImprovingTSP.tail_at_same_count {independent : CIOracle n}
    {G : DAG n} {steps : List (DAG n)} (trace : ImprovingTSP independent G steps)
    {K : DAG n} (present : K ∈ G :: steps) (count : arrowCount K = arrowCount G) :
    ∃ tail, ImprovingTSP independent K tail ∧ (K :: tail).Sublist (G :: steps) := by
  induction trace with
  | @turn G H D a b r subset fewer sgs =>
    rcases List.mem_cons.mp present with rfl | h
    · exact ⟨_, .turn r subset fewer sgs, List.Sublist.refl _⟩
    · have eq : K = D := by simpa using h
      subst K
      have counts := arrow_count_eq_of_reversal r
      omega
  | @plateau G H rest a b r sgs tail ih =>
    rcases List.mem_cons.mp present with rfl | h
    · exact ⟨_, .plateau r sgs tail, List.Sublist.refl _⟩
    · obtain ⟨after, segment, sublist⟩ := ih h (count.trans (arrow_count_eq_of_reversal r))
      exact ⟨after, segment, .cons G sublist⟩

/-- Cycle elimination is performed on DAG edge sets before converting the
walk to orders. Each repetition has the original plateau edge count. -/
theorem ImprovingTSP.exists_distinct {independent : CIOracle n}
    {G : DAG n} {steps : List (DAG n)} (trace : ImprovingTSP independent G steps) :
    ∃ tail, ImprovingTSP independent G tail ∧ (G :: tail).Pairwise (fun H K => H.edge ≠ K.edge) := by
  classical
  induction trace with
  | @turn G H D a b r subset fewer sgs =>
    refine ⟨[D], .turn r subset fewer sgs, ?_⟩
    have unequal : G.edge ≠ D.edge := by
      intro same
      have gc := arrows_eq_count_eq same
      have hc := arrow_count_eq_of_reversal r
      omega
    simpa using unequal
  | @plateau G H steps a b r sgs tail ih =>
    obtain ⟨shorter, newTail, distinct⟩ := ih
    by_cases repeated : ∃ K ∈ H :: shorter, G.edge = K.edge
    · obtain ⟨K, mem, equal⟩ := repeated
      have count : arrowCount K = arrowCount H :=
        (arrows_eq_count_eq equal).symm.trans (arrow_count_eq_of_reversal r)
      obtain ⟨rest, fromK, sublist⟩ := newTail.tail_at_same_count mem count
      have onK := List.Pairwise.sublist sublist distinct
      refine ⟨rest, fromK.rebase equal, List.pairwise_cons.mpr ⟨?_, (List.pairwise_cons.mp onK).2⟩⟩
      intro D present eq
      exact (List.pairwise_cons.mp onK).1 D present (equal.symm.trans eq)
    · refine ⟨H :: shorter, .plateau r sgs newTail, List.pairwise_cons.mpr ⟨?_, distinct⟩⟩
      exact fun K present same => repeated ⟨K, present, same⟩

private theorem arrow_subset_refl (G : DAG n) : ArrowSubset G G := fun _ _ h => h

private theorem arrow_subset_trans {G H K : DAG n} (a : ArrowSubset G H) (b : ArrowSubset H K) :
    ArrowSubset G K := fun u v edge => b u v (a u v edge)

private theorem markov_of_same_arrows {independent : CIOracle n} {G H : DAG n}
    (eq : G.edge = H.edge) (h : IsMarkov G independent) : IsMarkov H independent :=
  markov_of_separation_subset (SeparationSubset.of_edge_subset (by intro u v edge; rw [eq] at edge; exact edge)) h

private theorem sgs_of_same_arrows {independent : CIOracle n} {G H : DAG n}
    (eq : G.edge = H.edge) (good : SGSMinimal independent G) : SGSMinimal independent H := by
  refine ⟨markov_of_same_arrows eq good.1, ?_⟩
  intro K sub mk
  exact (good.2 K (fun u v edge => by rw [eq]; exact sub u v edge) mk).trans eq

theorem exists_sgs_subgraph {independent : CIOracle n} (G : DAG n) (markov : IsMarkov G independent) :
    ∃ H, ArrowSubset H G ∧ SGSMinimal independent H := by
  classical
  by_cases good : SGSMinimal independent G
  · exact ⟨G, arrow_subset_refl G, good⟩
  · have failed : ¬∀ H, ArrowSubset H G → IsMarkov H independent → H.edge = G.edge :=
      fun h => good ⟨markov, h⟩
    have found : ∃ H, ArrowSubset H G ∧ IsMarkov H independent ∧ H.edge ≠ G.edge := by
      by_cases any : ∃ H, ArrowSubset H G ∧ IsMarkov H independent ∧ H.edge ≠ G.edge
      · exact any
      · exfalso
        apply failed
        intro H sub mk
        by_cases eq : H.edge = G.edge
        · exact eq
        · exact (any ⟨H, sub, mk, eq⟩).elim
    obtain ⟨H, sub, mk, proper⟩ := found
    have less := arrow_count_lt_of_proper_subset sub proper
    obtain ⟨K, smaller, good⟩ := exists_sgs_subgraph H mk
    exact ⟨K, arrow_subset_trans smaller sub, good⟩
termination_by arrowCount G

theorem improving_tsp_of_chickering_sequence {independent : CIOracle n} {G K : DAG n}
    (seq : BackwardSequence K G) (source : SGSMinimal independent G)
    (target : IsMarkov K independent) (strict : ¬ SeparationSubset K G) :
    ∃ steps, ImprovingTSP independent G steps := by
  classical
  induction seq with
  | done equal => exact (strict (.of_edge_eq equal.symm)).elim
  | @reverse G H a b rev tail ih =>
    by_cases stable : SGSMinimal independent H
    · have strictH : ¬ SeparationSubset K H :=
        fun backwards => strict (backwards.trans (.of_reversal rev.symm))
      obtain ⟨steps, found⟩ := ih stable strictH
      exact ⟨H :: steps, .plateau rev stable found⟩
    · have mk := markov_of_separation_subset tail.implies_map target
      obtain ⟨D, sub, good⟩ := exists_sgs_subgraph H mk
      have proper : D.edge ≠ H.edge := fun eq => stable (sgs_of_same_arrows eq good)
      exact ⟨[D], .turn rev sub (arrow_count_lt_of_proper_subset sub proper) good⟩
  | @delete G a b arrow tail _ =>
    have mk := markov_of_separation_subset tail.implies_map target
    have count := arrows_eq_count_eq
      (source.2 (G.deleteArrow a b) (fun u v h => ((G.deleteArrow_edge_iff a b u v).mp h).1) mk)
    have fewer := delete_arrow_decreases_count arrow
    omega

end

end OpenCausalScience.Papers.LamEtAl2022
