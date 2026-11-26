module
public import OpenCausalScience.Papers.Meek1995.Orientation

/-! Meek (1995), Figure 1 and Theorem 2. The reference DAG supplies the
fixed skeleton and collider signature. The partially directed graph
stores which orientations have been imposed so far. -/

namespace OpenCausalScience.Papers.Meek1995.Closure

open OpenCausalScience.Papers.Meek1995.Orientation
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence

@[expose] public section

variable {n : Nat}

abbrev Orientations (n : Nat) := Fin n → Fin n → Prop

/-- The current orientation contains the two arrows of each original
unshielded collider, as in the input pattern and after fixing knowledge. -/
def ContainsColliders (base : DAG n) (fixed : Orientations n) : Prop :=
  ∀ u v w, UnshieldedCollider base u v w → fixed u v ∧ fixed w v

/-- A consistent extension preserves the same skeleton and unshielded
colliders and agrees with the imposed directions. -/
structure Extension (base : DAG n) (fixed : Orientations n) (candidate : DAG n) : Prop where
  skeleton : ∀ u v, Adjacent base u v ↔ Adjacent candidate u v
  colliders : ∀ u v w, UnshieldedCollider base u v w ↔ UnshieldedCollider candidate u v w
  oriented : ∀ u v, fixed u v → candidate.edge u v = true

def Unoriented (base : DAG n) (fixed : Orientations n) (u v : Fin n) : Prop :=
  Adjacent base u v ∧ ¬ fixed u v ∧ ¬ fixed v u

inductive Proposal (base : DAG n) (fixed : Orientations n) : Fin n → Fin n → Prop
  | r1 {a b c} : Unoriented base fixed a b → fixed c a → c ≠ b →
      ¬ Adjacent base c b → Proposal base fixed a b
  | r2 {a b c} : Unoriented base fixed a b → fixed a c → fixed c b → Proposal base fixed a b
  | r3 {a b c d} : Unoriented base fixed a b → Unoriented base fixed a c →
      Unoriented base fixed a d → fixed c b → fixed d b → c ≠ d →
      ¬ Adjacent base c d → Proposal base fixed a b
  | r4 {a b c d} : Unoriented base fixed a b → Unoriented base fixed a c →
      fixed c d → fixed d b → c ≠ b → ¬ Adjacent base c b → Proposal base fixed a b

private theorem unshielded_excluded {base candidate : DAG n} {fixed : Orientations n}
    (contains : ContainsColliders base fixed) (consistent : Extension base fixed candidate)
    {c a b : Fin n} (edge : Unoriented base fixed a b) :
    ¬ UnshieldedCollider candidate c a b := by
  intro collider
  exact edge.2.2 (contains c a b ((consistent.colliders c a b).mpr collider)).2

/-- Each of the four orientations is forced in every consistent
extension, including the R4 case used with background knowledge. -/
theorem proposal_sound {base candidate : DAG n} {fixed : Orientations n}
    (contains : ContainsColliders base fixed) (consistent : Extension base fixed candidate)
    {u v : Fin n} (rule : Proposal base fixed u v) : candidate.edge u v = true := by
  cases rule with
  | @r1 c ab ca different nonAdj =>
    exact orient_unshielded_noncollider (consistent.oriented _ _ ca)
      ((consistent.skeleton _ _).mp ab.1) different
      (fun adj => nonAdj ((consistent.skeleton _ _).mpr adj))
      (unshielded_excluded contains consistent ab)
  | @r2 c ab ac cb =>
    exact orient_along_directed_path
      (.extend (.single (consistent.oriented _ _ ac)) (consistent.oriented _ _ cb))
      ((consistent.skeleton _ _).mp ab.1)
  | @r3 c d ab ac ad cb db different nonAdj =>
    rcases (consistent.skeleton _ _).mp ab.1 with forward | back
    · exact forward
    · have fromC := orient_along_directed_path
        (.extend (.single (consistent.oriented _ _ cb)) back)
        (Or.symm ((consistent.skeleton _ _).mp ac.1))
      have fromD := orient_along_directed_path
        (.extend (.single (consistent.oriented _ _ db)) back)
        (Or.symm ((consistent.skeleton _ _).mp ad.1))
      exact (unshielded_excluded contains consistent ad
        ⟨different, fun adj => nonAdj ((consistent.skeleton _ _).mpr adj), fromC, fromD⟩).elim
  | @r4 c d ab ac cd db different nonAdj =>
    rcases (consistent.skeleton _ _).mp ab.1 with forward | back
    · exact forward
    · have fromC := orient_along_directed_path
        (.extend (.extend (.single (consistent.oriented _ _ cd))
          (consistent.oriented _ _ db)) back)
        (Or.symm ((consistent.skeleton _ _).mp ac.1))
      exact (unshielded_excluded contains consistent ab
        ⟨different, fun adj => nonAdj ((consistent.skeleton _ _).mpr adj), fromC, back⟩).elim

def closeRound (base : DAG n) (fixed : Orientations n) : Orientations n :=
  fun u v => fixed u v ∨ Proposal base fixed u v

def iterate (base : DAG n) : Nat → Orientations n → Orientations n
  | 0, fixed => fixed
  | rounds + 1, fixed => closeRound base (iterate base rounds fixed)

private theorem contains_after_round {base : DAG n} {fixed : Orientations n}
    (contains : ContainsColliders base fixed) : ContainsColliders base (closeRound base fixed) :=
  fun u v w collider =>
    ⟨.inl (contains u v w collider).1, .inl (contains u v w collider).2⟩

private theorem contains_after_iteration {base : DAG n} {fixed : Orientations n}
    (contains : ContainsColliders base fixed) (rounds : Nat) :
    ContainsColliders base (iterate base rounds fixed) := by
  induction rounds with
  | zero => exact contains
  | succ _ ih => exact contains_after_round ih

/-- A simultaneous round of sound orientations preserves the entire
consistent extension set. -/
theorem extension_iff_after_round {base candidate : DAG n} {fixed : Orientations n}
    (contains : ContainsColliders base fixed) :
    Extension base (closeRound base fixed) candidate ↔ Extension base fixed candidate := by
  constructor
  · intro extended
    exact ⟨extended.skeleton, extended.colliders,
      fun u v known => extended.oriented u v (.inl known)⟩
  · intro consistent
    exact ⟨consistent.skeleton, consistent.colliders,
      fun u v known => known.elim (consistent.oriented u v) (proposal_sound contains consistent)⟩

/-- Preservation applies to any finite number of simultaneous rounds. -/
theorem extension_iff_after_iterations {base candidate : DAG n} {fixed : Orientations n}
    (contains : ContainsColliders base fixed) (rounds : Nat) :
    Extension base (iterate base rounds fixed) candidate ↔ Extension base fixed candidate := by
  induction rounds with
  | zero => exact Iff.rfl
  | succ rounds prior =>
    exact (extension_iff_after_round (contains_after_iteration contains rounds)).trans prior

def pairs (n : Nat) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun u => (List.finRange n).map fun v => (u, v)

private theorem mem_pairs (u v : Fin n) : (u, v) ∈ pairs n :=
  List.mem_flatMap.mpr ⟨u, List.mem_finRange _, List.mem_map.mpr ⟨v, List.mem_finRange _, rfl⟩⟩

private noncomputable def numArrows (fixed : Orientations n) : Nat :=
  open Classical in (pairs n).countP fun e => decide (fixed e.1 e.2)

private theorem count_le {α : Type} {f g : α → Bool}
    (imp : ∀ x, f x = true → g x = true) (xs : List α) :
    xs.countP f ≤ xs.countP g := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x _ ih =>
    rw [List.countP_cons, List.countP_cons]
    by_cases known : f x = true
    · simp [known, imp x known, ih]
    · simp [known]
      split <;> omega

private theorem count_lt {α : Type} {f g : α → Bool}
    (imp : ∀ x, f x = true → g x = true) {w : α} {xs : List α}
    (witness : w ∈ xs) (absent : f w ≠ true) (present : g w = true) :
    xs.countP f < xs.countP g := by
  induction xs with
  | nil => cases witness
  | cons x rest ih =>
    rw [List.countP_cons, List.countP_cons]
    rcases List.mem_cons.mp witness with rfl | next
    · have prior := count_le imp rest
      simp [absent, present]
      omega
    · have prior := ih next
      by_cases known : f x = true
      · simp [known, imp x known, prior]
      · simp [known]
        split <;> omega

private theorem numArrows_increases_of_changes (base : DAG n) (fixed : Orientations n)
    (changed : closeRound base fixed ≠ fixed) :
    numArrows fixed < numArrows (closeRound base fixed) := by
  classical
  have extra : ∃ u v, ¬ fixed u v ∧ closeRound base fixed u v := by
    apply Classical.byContradiction
    intro none
    apply changed
    funext u v
    apply propext
    exact ⟨fun edge => Classical.byContradiction (fun absent => none ⟨u, v, absent, edge⟩),
      Or.inl⟩
  obtain ⟨u,v,absent,present⟩ := extra
  unfold numArrows
  exact count_lt (fun e prior => decide_eq_true (.inl (of_decide_eq_true prior)))
    (mem_pairs u v) (fun h => absent (of_decide_eq_true h)) (decide_eq_true present)

private theorem numArrows_bounded (fixed : Orientations n) :
    numArrows fixed ≤ (pairs n).length := by
  unfold numArrows
  rw [List.countP_eq_length_filter]
  exact List.length_filter_le _ _

/-- Simultaneous closure becomes stationary within the number of
ordered vertex pairs. A nonterminal round adds at least one arrow. -/
theorem exists_stationary_round (base : DAG n) (fixed : Orientations n) :
    ∃ k ≤ (pairs n).length, closeRound base (iterate base k fixed) = iterate base k fixed := by
  classical
  apply Classical.byContradiction
  intro none
  have growing (k : Nat) (within : k ≤ (pairs n).length) :
      numArrows (iterate base k fixed) < numArrows (iterate base (k+1) fixed) :=
    numArrows_increases_of_changes base (iterate base k fixed) (fun equal => none ⟨k, within, equal⟩)
  have bound (k : Nat) (within : k ≤ (pairs n).length + 1) :
      k ≤ numArrows (iterate base k fixed) := by
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have prior := ih (by omega)
      have step := growing k (by omega)
      omega
  have tooMany := bound ((pairs n).length + 1) (Nat.le_refl _)
  have cap := numArrows_bounded (iterate base ((pairs n).length + 1) fixed)
  omega

end
end OpenCausalScience.Papers.Meek1995.Closure
