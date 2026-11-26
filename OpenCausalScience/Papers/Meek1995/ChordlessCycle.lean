module
public import OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

/-! Lemma 2 of Meek (1995). A highest-ranked vertex on an induced cycle
receives both cycle arrows. Its two neighbors are distinct and nonadjacent. -/

namespace OpenCausalScience.Papers.Meek1995.ChordlessCycle

open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n m : Nat}

structure Cycle (G : DAG n) (m : Nat) where
  length : 4 ≤ m
  vertex : Fin m → Fin n
  previous : Fin m → Fin m
  following : Fin m → Fin m
  leftEdge : ∀ k, Adjacent G (vertex (previous k)) (vertex k)
  rightEdge : ∀ k, Adjacent G (vertex (following k)) (vertex k)
  unshielded : ∀ k, vertex (previous k) ≠ vertex (following k) ∧
    ¬ Adjacent G (vertex (previous k)) (vertex (following k))

private theorem exists_highest {α : Type} (rank : α → Nat) :
    ∀ xs : List α, xs ≠ [] → ∃ a, a ∈ xs ∧ ∀ b, b ∈ xs → rank b ≤ rank a := by
  intro xs
  induction xs with
  | nil => intro h; exact (h rfl).elim
  | cons a rest ih =>
    intro _
    by_cases empty : rest = []
    · subst rest
      exact ⟨a, .head _, fun b hb => by obtain rfl := List.mem_singleton.mp hb; exact Nat.le_refl _⟩
    · obtain ⟨top, member, maximal⟩ := ih empty
      by_cases superior : rank top ≤ rank a
      · refine ⟨a, .head _, fun b hb => ?_⟩
        rcases List.mem_cons.mp hb with rfl | old
        · exact Nat.le_refl _
        · exact Nat.le_trans (maximal _ old) superior
      · refine ⟨top, .tail _ member, fun b hb => ?_⟩
        rcases List.mem_cons.mp hb with rfl | old
        · omega
        · exact maximal _ old

/-- Orienting a chordless cycle in a DAG creates an unshielded collider
on the cycle. It is enough that both neighbors of every cycle vertex
be distinct and nonadjacent. -/
theorem contains_collider {G : DAG n} (cycle : Cycle G m) :
    ∃ k, UnshieldedCollider G (cycle.vertex (cycle.previous k)) (cycle.vertex k)
      (cycle.vertex (cycle.following k)) := by
  have nonempty : List.finRange m ≠ [] := by
    have present : (⟨0, by have := cycle.length; omega⟩ : Fin m) ∈ List.finRange m :=
      List.mem_finRange _
    intro empty
    simp [empty] at present
  obtain ⟨k, _, highest⟩ := exists_highest (fun i => G.rank (cycle.vertex i)) _ nonempty
  have incoming {neighbor : Fin m} (edge : Adjacent G (cycle.vertex neighbor) (cycle.vertex k)) :
      G.edge (cycle.vertex neighbor) (cycle.vertex k) = true := by
    rcases edge with before | after
    · exact before
    · have later := G.edge_increases _ _ after
      have earlier := highest neighbor (List.mem_finRange _)
      omega
  exact ⟨k, (cycle.unshielded k).1, (cycle.unshielded k).2,
    incoming (cycle.leftEdge k), incoming (cycle.rightEdge k)⟩

end
end OpenCausalScience.Papers.Meek1995.ChordlessCycle
