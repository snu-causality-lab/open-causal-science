module
public import OpenCausalScience.Graph.MoralizationExecutable

/-! # The DAG induced by a variable order and a conditional-independence oracle -/

namespace OpenCausalScience.Discovery

open OpenCausalScience.Moralization
open OpenCausalScience.Papers.KimEtAl2026.BayesBallCorrectness

@[expose] public section

variable {n : Nat}

/-- An oracle on two distinct variables and a conditioning set. -/
abbrev CIOracle (n : Nat) := Fin n → Fin n → (Fin n → Bool) → Bool

/-- The predecessors of `target` other than `source`. -/
def predecessorsExcept (order : Fin n → Nat) (source target : Fin n) (z : Fin n) : Bool :=
  decide (order z < order target) && z != source

/-- A forward arrow is present exactly when its endpoints are dependent
conditional on the other predecessors of its head. -/
def orderDAG (order : Fin n → Nat) (independent : CIOracle n) : DAG n where
  edge u v := decide (order u < order v) && !independent v u (predecessorsExcept order u v)
  rank := order
  edge_increases u v edge := by
    simpa using (Bool.and_eq_true_iff.mp edge).1

theorem orderDAG_edge_iff (order : Fin n → Nat) (independent : CIOracle n) (u v : Fin n) :
    (orderDAG order independent).edge u v = true ↔
      order u < order v ∧ independent v u (predecessorsExcept order u v) = false := by
  simp [orderDAG, Bool.and_eq_true]

/-- Query d-separation using the ancestral moral graph. -/
def graphOracle (G : DAG n) : CIOracle n := fun x y condition =>
  let Q : Query G := ⟨(· == x), (· == y), Conditioning.ofPredicate G condition⟩
  Q.dagMoralSeparated

private theorem graphOracle_iff_no_moralConnection (G : DAG n) (x y : Fin n)
    (condition : Fin n → Bool) (xOutside : condition x = false) (yOutside : condition y = false) :
    graphOracle G x y condition = true ↔
      ¬ (show Query G from ⟨(· == x), (· == y), Conditioning.ofPredicate G condition⟩).MoralConnection := by
  let Q : Query G := ⟨(· == x), (· == y), Conditioning.ofPredicate G condition⟩
  have leftOutside : ∀ v, Q.left v = true → Q.condition.member v = false := by
    intro v hv
    change (v == x) = true at hv
    simpa [Q, Conditioning.ofPredicate, beq_iff_eq.mp hv] using xOutside
  have rightOutside : ∀ v, Q.right v = true → Q.condition.member v = false := by
    intro v hv
    change (v == y) = true at hv
    simpa [Q, Conditioning.ofPredicate, beq_iff_eq.mp hv] using yOutside
  exact (Q.dagMoralSeparated_eq_true_iff leftOutside rightOutside).trans
    (Q.dSeparation_iff_no_moralConnection leftOutside rightOutside)

/-- Removing arrows preserves each d-separation. The smaller ancestral moral
search uses a subset of the relevant vertices and of the available edges. -/
theorem graphOracle_of_edge_subset {G H : DAG n}
    (subset : ∀ u v, G.edge u v = true → H.edge u v = true)
    {x y : Fin n} {condition : Fin n → Bool}
    (xOutside : condition x = false) (yOutside : condition y = false)
    (separated : graphOracle H x y condition = true) : graphOracle G x y condition = true := by
  let Q : Query G := ⟨(· == x), (· == y), Conditioning.ofPredicate G condition⟩
  let T : Query H := ⟨(· == x), (· == y), Conditioning.ofPredicate H condition⟩
  have ancestry {u v : Fin n} (path : Ancestor G u v) : Ancestor H u v := by
    rcases path with rfl | route
    · exact .inl rfl
    · apply Or.inr
      induction route with
      | single arrow => exact .single (subset _ _ arrow)
      | extend _ arrow ih => exact .extend ih (subset _ _ arrow)
  have relevant {v : Fin n} (present : Q.relevant v) : T.relevant v := by
    obtain ⟨w, member, path⟩ := (Q.relevant_iff _).mp present
    exact (T.relevant_iff _).mpr ⟨w, member, ancestry path⟩
  have liftEdge {u v : Fin n} (edge : Q.MoralEdge u v) : T.MoralEdge u v := by
    refine ⟨relevant edge.sourceRelevant, relevant edge.targetRelevant, edge.sourceOutside,
      edge.targetOutside, edge.distinct, ?_⟩
    rcases edge.connection with (forward | backward | ⟨c, present, first, second⟩)
    · exact .inl (subset _ _ forward)
    · exact .inr (.inl (subset _ _ backward))
    · exact .inr (.inr ⟨c, relevant present, subset _ _ first, subset _ _ second⟩)
  have liftWalk {u v : Fin n} (walk : Q.MoralWalk u v) : T.MoralWalk u v := by
    induction walk with
    | nil v => exact .nil v
    | cons edge _ ih => exact .cons (liftEdge edge) ih
  apply (graphOracle_iff_no_moralConnection G x y condition xOutside yOutside).mpr
  rintro ⟨u, v, left, right, walk⟩
  exact (graphOracle_iff_no_moralConnection H x y condition xOutside yOutside).mp separated
    ⟨u, v, left, right, liftWalk walk⟩

private theorem walk_increases {G : DAG n} (order : Fin n → Nat)
    (topological : ∀ x y, G.edge x y = true → order x < order y)
    {x y : Fin n} (route : G.DirectedWalk x y) : order x < order y := by
  induction route with
  | single arrow => exact topological _ _ arrow
  | extend _ arrow ih => exact Nat.lt_trans ih (topological _ _ arrow)

/-- In a topological order, conditioning on the other predecessors detects
exactly the arrows into the target when the CI oracle is d-separation in `G`. -/
theorem graphOracle_predecessors_eq_not_edge {G : DAG n} (order : Fin n → Nat)
    (uniqueRank : ∀ x y, order x = order y → x = y)
    (topological : ∀ x y, G.edge x y = true → order x < order y)
    {u v : Fin n} (earlier : order u < order v) :
    graphOracle G v u (predecessorsExcept order u v) = !G.edge u v := by
  let Q : Query G := ⟨(· == v), (· == u), Conditioning.ofPredicate G (predecessorsExcept order u v)⟩
  have different : u ≠ v := by
    intro equal
    subst u
    exact (Nat.lt_irrefl _) earlier
  have outsideV : Q.condition.member v = false := by
    simp [Q, Conditioning.ofPredicate, predecessorsExcept]
  have outsideU : Q.condition.member u = false := by
    simp [Q, Conditioning.ofPredicate, predecessorsExcept]
  have leftOutside : ∀ x, Q.left x = true → Q.condition.member x = false := by
    intro x source
    change (x == v) = true at source
    have equal := beq_iff_eq.mp source
    simpa [equal] using outsideV
  have rightOutside : ∀ x, Q.right x = true → Q.condition.member x = false := by
    intro x target
    change (x == u) = true at target
    have equal := beq_iff_eq.mp target
    simpa [equal] using outsideU
  have relevantBound (x : Fin n) (relevant : Q.relevant x) : order x ≤ order v := by
    obtain ⟨w, belongs, ancestry⟩ := (Q.relevant_iff x).mp relevant
    have wBound : order w ≤ order v := by
      rcases belongs with left | right | condition
      · change (w == v) = true at left
        rw [beq_iff_eq.mp left]
        exact Nat.le_refl _
      · change (w == u) = true at right
        rw [beq_iff_eq.mp right]
        exact Nat.le_of_lt earlier
      · change (decide (order w < order v) && w != u) = true at condition
        exact Nat.le_of_lt (of_decide_eq_true (Bool.and_eq_true_iff.mp condition).1)
    rcases ancestry with rfl | route
    · exact wBound
    · exact Nat.le_trans (Nat.le_of_lt (walk_increases order topological route)) wBound
  have connection_iff : Q.MoralConnection ↔ G.edge u v = true := by
    constructor
    · rintro ⟨a, b, left, right, walk⟩
      change (a == v) = true at left
      change (b == u) = true at right
      rw [beq_iff_eq.mp left, beq_iff_eq.mp right] at walk
      cases walk with
      | nil => exact (different rfl).elim
      | @cons _ w _ step _ =>
        have wBound := relevantBound w step.targetRelevant
        have wEarlier : order w < order v :=
          Nat.lt_of_le_of_ne wBound (fun same => step.distinct (uniqueRank _ _ same).symm)
        have wIsU : w = u := by
          have h := step.targetOutside
          simpa [Q, Conditioning.ofPredicate, predecessorsExcept, wEarlier] using h
        subst w
        rcases step.connection with out | into | ⟨c, rel, out, _⟩
        · exact (Nat.lt_asymm earlier (topological _ _ out)).elim
        · exact into
        · exact (Nat.not_lt_of_ge (relevantBound c rel) (topological _ _ out)).elim
    · intro arrow
      refine ⟨v, u, by simp [Q], by simp [Q], .cons ?_ (.nil u)⟩
      refine ⟨?_, ?_, outsideV, outsideU, different.symm, .inr (.inl arrow)⟩
      · exact (Q.relevant_iff v).mpr ⟨v, .inl (by simp [Q]), .inl rfl⟩
      · exact (Q.relevant_iff u).mpr ⟨u, .inr (.inl (by simp [Q])), .inl rfl⟩
  have correct : Q.dagMoralSeparated = true ↔ ¬ Q.MoralConnection :=
    (Q.dagMoralSeparated_eq_true_iff leftOutside rightOutside).trans
      (Q.dSeparation_iff_no_moralConnection leftOutside rightOutside)
  change Q.dagMoralSeparated = !G.edge u v
  apply Bool.eq_iff_iff.mpr
  rw [correct, connection_iff, Bool.not_eq_true']
  exact Bool.eq_false_iff.symm

/-- Every topological order with distinct ranks reconstructs the original
edge set from its graphical CI oracle. -/
theorem orderDAG_recovers_graphOracle {G : DAG n} (order : Fin n → Nat)
    (uniqueRank : ∀ x y, order x = order y → x = y)
    (topological : ∀ x y, G.edge x y = true → order x < order y) :
    (orderDAG order (graphOracle G)).edge = G.edge := by
  funext u v
  apply Bool.eq_iff_iff.mpr
  rw [orderDAG_edge_iff]
  constructor
  · rintro ⟨earlier, dependent⟩
    simpa [graphOracle_predecessors_eq_not_edge order uniqueRank topological earlier] using dependent
  · intro arrow
    have earlier := topological u v arrow
    exact ⟨earlier, by simp [graphOracle_predecessors_eq_not_edge order uniqueRank topological earlier, arrow]⟩

end

end OpenCausalScience.Discovery
