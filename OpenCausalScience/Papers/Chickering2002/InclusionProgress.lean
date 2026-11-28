module
public import OpenCausalScience.Papers.Chickering2002.InclusionStructure

/-! A single directed-edge operation in Theorem 4 and its inverse. -/

namespace OpenCausalScience.Papers.Chickering2002

open LamEtAl2022
open Chickering1995.CoveredReversal Chickering1995.FindEdge Chickering1995.Transformation
open VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n : Nat} {G H K : DAG n}

/-- A rank change alone does not change the possible predecessor of a backward sequence. -/
theorem BackwardSequence.of_start_edges {T : DAG n} (sequence : BackwardSequence T H)
    (same : G.edge = H.edge) : BackwardSequence T G := by
  induction sequence generalizing G with
  | done finish => exact .done (same.trans finish)
  | reverse rev rest _ =>
    refine .reverse ⟨?_, rev.reverse, ?_, ?_⟩ rest
    · rw [same]
      exact rev.forward
    · intro u v forward backward
      rw [same]
      exact rev.unchanged u v forward backward
    · intro u differentU differentV
      rw [same]
      exact rev.parents u differentU differentV
  | @delete original u v arrow _rest ih =>
    refine .delete (?_ : G.edge u v = true) (ih ?_)
    · rw [same]
      exact arrow
    · funext a b
      simp [DAG.deleteArrow, same]

theorem BackwardSequence.append (first : BackwardSequence H G) (tail : BackwardSequence K H) :
    BackwardSequence K G := by
  induction first with
  | done same => exact tail.of_start_edges same
  | reverse rev _ ih => exact .reverse rev ih
  | delete arrow _ ih => exact .delete arrow ih

/-- A Figure 2 step is an insertion of an absent arrow or the reversal of
an arrow that disagrees with the target. The target remains an I-map of the edited DAG. -/
inductive ForwardStep (target : DAG n) : DAG n → DAG n → Prop
  | reverse {A B u v} : DifferingEdge A target u v → Reversal A B u v →
      IndependenceMap B target → ForwardStep target A B
  | insert {A B u v} : A.edge u v = false → A.IsInsertion B u v →
      IndependenceMap B target → ForwardStep target A B

private theorem forward_insertion_arrow {A B : DAG n} {u v : Fin n}
    (addition : A.IsInsertion B u v) : B.edge u v = true :=
  (addition u v).mpr (.inr ⟨rfl, rfl⟩)

private theorem insert_then_delete_eq {A B : DAG n} {u v : Fin n}
    (fresh : A.edge u v = false) (addition : A.IsInsertion B u v) :
    (B.deleteArrow u v).edge = A.edge := by
  funext a b
  apply Bool.eq_iff_iff.mpr
  rw [DAG.deleteArrow_edge_iff, addition]
  constructor
  · rintro ⟨(old | newly), distinct⟩
    · exact old
    · exact (distinct newly).elim
  · intro old
    exact ⟨.inl old, fun ⟨rfl, rfl⟩ => Bool.false_ne_true (fresh.symm.trans old)⟩

theorem ForwardStep.backward {target A B : DAG n} (step : ForwardStep target A B) :
    BackwardSequence A B := by
  cases step with
  | reverse _ reversal _ => exact .reverse reversal.symm (.done rfl)
  | insert fresh add _ =>
    exact .delete (forward_insertion_arrow add) (.done (insert_then_delete_eq fresh add))

theorem ForwardStep.map_held {target A B : DAG n} (step : ForwardStep target A B) :
    IndependenceMap B target := by
  cases step with
  | reverse _ _ h => exact h
  | insert _ _ h => exact h

end

end OpenCausalScience.Papers.Chickering2002
