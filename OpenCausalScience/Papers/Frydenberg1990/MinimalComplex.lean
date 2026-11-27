module
public import OpenCausalScience.Papers.Frydenberg1990.MoralSeparation
public import OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

/-! # Minimal complexes and the DAG case

A complex is an induced chain a → c₁ — ··· — cₖ ← b. The number of
internal lines is the index used here. Frydenberg's minimal complexes
reduce exactly to unshielded colliders on DAGs.
-/

namespace OpenCausalScience.Papers.Frydenberg1990.MinimalComplex

open ChainGraph
open MoralSeparation (adjacent)
open VermaPearl1990.DAGEquivalence (Adjacent UnshieldedCollider)

@[expose] public section

variable {n : Nat}

structure Complex (G : ChainGraph n) (lines : Nat) where
  vertex : Fin (lines + 3) → Fin n
  injective : ∀ {i j}, vertex i = vertex j → i = j
  first : G.arrow (vertex ⟨0, by omega⟩) (vertex ⟨1, by omega⟩) = true
  last : G.arrow (vertex ⟨lines + 2, by omega⟩) (vertex ⟨lines + 1, by omega⟩) = true
  interior : ∀ i : Fin lines,
    G.line (vertex ⟨i.val + 1, by omega⟩) (vertex ⟨i.val + 2, by omega⟩) = true
  no_chord : ∀ i j, i.val + 1 < j.val → adjacent G (vertex i) (vertex j) = false

theorem ofDAG_lines_eq_zero (G : DAG n) {lines : Nat} (complex : Complex (ofDAG G) lines) :
    lines = 0 := by
  by_cases zero : lines = 0
  · exact zero
  · have next := complex.interior ⟨0, Nat.pos_of_ne_zero zero⟩
    simp [ofDAG] at next

theorem ofDAG_collider (G : DAG n) (complex : Complex (ofDAG G) 0) :
    UnshieldedCollider G (complex.vertex 0) (complex.vertex 1) (complex.vertex 2) := by
  refine ⟨fun same => ?_, ?_, ?_, ?_⟩
  · have i : (0 : Fin 3) = 2 := complex.injective same
    contradiction
  · have absent := complex.no_chord 0 2 (by decide)
    simpa [adjacent, Adjacent, ofDAG, Bool.or_eq_false_iff] using absent
  · exact complex.first
  · exact complex.last

private def triple (a c b : Fin n) (i : Fin 3) : Fin n :=
  if i.val = 0 then a else if i.val = 1 then c else b

private theorem fin_three (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  have bound := i.isLt
  have values : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases values with first | second | third
  · exact .inl (Fin.ext first)
  · exact .inr (.inl (Fin.ext second))
  · exact .inr (.inr (Fin.ext third))

theorem ofDAG_zero_complex_iff (G : DAG n) (a c b : Fin n) :
    (∃ complex : Complex (ofDAG G) 0,
      complex.vertex 0 = a ∧ complex.vertex 1 = c ∧ complex.vertex 2 = b) ↔
        UnshieldedCollider G a c b := by
  constructor
  · rintro ⟨complex, first, middle, last⟩
    rw [← first, ← middle, ← last]
    exact ofDAG_collider G complex
  · rintro ⟨ab, nonadjacent, acEdge, bcEdge⟩
    have ac : a ≠ c := by
      intro same
      exact Nat.lt_irrefl _ (same ▸ G.edge_increases _ _ acEdge)
    have bc : b ≠ c := by
      intro same
      exact Nat.lt_irrefl _ (same ▸ G.edge_increases _ _ bcEdge)
    have absent : adjacent (ofDAG G) a b = false := by
      simpa [adjacent, Adjacent, ofDAG, Bool.or_eq_false_iff] using nonadjacent
    refine ⟨⟨triple a c b, ?_, acEdge, bcEdge, ?_, ?_⟩, rfl, rfl, rfl⟩
    · intro i j same
      rcases fin_three i with rfl | rfl | rfl <;> rcases fin_three j with rfl | rfl | rfl
      all_goals first | rfl | exact ((ab (by exact same)).elim) |
        exact ((ab (by exact same.symm)).elim) |
        exact ((ac (by exact same)).elim) | exact ((ac (by exact same.symm)).elim) |
        exact ((bc (by exact same)).elim) | exact ((bc (by exact same.symm)).elim)
    · intro i
      exact Fin.elim0 i
    · intro i j far
      have i0 : i = 0 := Fin.ext (by have := j.isLt; simpa using (show i.val = 0 by omega))
      have j2 : j = 2 := Fin.ext (by have := j.isLt; simpa using (show j.val = 2 by omega))
      subst i
      subst j
      exact absent

end
end OpenCausalScience.Papers.Frydenberg1990.MinimalComplex
