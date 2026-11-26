module
public import OpenCausalScience.Graph.MixedPath

/-! # Runge's O-set construction

Runge (NeurIPS 2021; arXiv:2102.10324v4), Definitions 3 and 4. In the graph
criterion for an ADMG, independence in the eligibility test is interpreted as
m-separation. Bidirected chains start at the outcome or a mediator, and each
subsequent vertex must satisfy both eligibility conditions. The theorem below
checks the reduction to the parent set when there are no bidirected edges.

Source: https://arxiv.org/html/2102.10324v4#S2.SS3.
-/

namespace OpenCausalScience.Papers.Runge2021.OSet

@[expose] public section

variable {n : Nat}

def DirectedReach (graph : MixedGraph n) (u v : Fin n) : Prop :=
  graph.AncestorOf (· == v) u

/-- The union of the outcome and all vertices strictly between `x` and `y`
on directed paths, for an acyclic directed part and distinct endpoints. -/
def OutcomeAndMediators (graph : MixedGraph n) (x y v : Fin n) : Prop :=
  v = y ∨ (v ≠ x ∧ DirectedReach graph x v ∧ DirectedReach graph v y)

def Forbidden (graph : MixedGraph n) (x y v : Fin n) : Prop :=
  v = x ∨ ∃ w, OutcomeAndMediators graph x y w ∧ DirectedReach graph w v

def ValidAncestor (graph : MixedGraph n) (x y : Fin n) (fixed : Fin n → Bool) (v : Fin n) : Prop :=
  graph.AncestorOf (fun w => (w == x) || (w == y) || fixed w) v ∧ ¬ Forbidden graph x y v

noncomputable def validAncestors (graph : MixedGraph n) (x y : Fin n)
    (fixed : Fin n → Bool) : Fin n → Bool := by
  classical
  exact fun v => decide (ValidAncestor graph x y fixed v)

/-- Definition 3 (1) and (2a)/(2b). The separation test always uses the
same valid ancestor set, independent of earlier members of a collider path. -/
def Eligible (graph : MixedGraph n) (x y : Fin n) (fixed : Fin n → Bool) (v : Fin n) : Prop :=
  ¬ Forbidden graph x y v ∧ (ValidAncestor graph x y fixed v ∨
    ¬ graph.PathConnected (· == v) (· == x) (validAncestors graph x y fixed))

inductive EligibleChain (graph : MixedGraph n) (eligible : Fin n → Prop) :
    Fin n → List (Fin n) → Prop
  | nil (u) : EligibleChain graph eligible u []
  | cons {u v rest} : graph.edge u true v true = true → eligible v →
      EligibleChain graph eligible v rest → EligibleChain graph eligible u (v :: rest)

theorem EligibleChain.member_eligible {graph : MixedGraph n} {eligible : Fin n → Prop}
    {u v : Fin n} {rest : List (Fin n)} (chain : EligibleChain graph eligible u rest)
    (member : v ∈ rest) : eligible v := by
  induction chain with
  | nil => simp at member
  | cons _ allowed _ ih =>
    rcases List.mem_cons.mp member with rfl | tailMember
    · exact allowed
    · exact ih tailMember

def Collider (graph : MixedGraph n) (x y : Fin n) (fixed : Fin n → Bool) (v : Fin n) : Prop :=
  ∃ w nodes, OutcomeAndMediators graph x y w ∧ (w :: nodes).Nodup ∧
    EligibleChain graph (Eligible graph x y fixed) w nodes ∧ v ∈ nodes

theorem collider_eligible {graph : MixedGraph n} {x y v : Fin n} {fixed : Fin n → Bool}
    (collider : Collider graph x y fixed v) : Eligible graph x y fixed v := by
  obtain ⟨_, _, _, _, chain, member⟩ := collider
  exact chain.member_eligible member

def ParentPart (graph : MixedGraph n) (x y v : Fin n) : Prop :=
  ¬ Forbidden graph x y v ∧ ∃ w, OutcomeAndMediators graph x y w ∧ graph.edge v false w true = true

def InOSet (graph : MixedGraph n) (x y : Fin n) (fixed : Fin n → Bool) (v : Fin n) : Prop :=
  ParentPart graph x y v ∨ Collider graph x y fixed v ∨
    ∃ w, Collider graph x y fixed w ∧ graph.edge v false w true = true

private theorem no_collider_without_bidirected {graph : MixedGraph n} {x y v : Fin n}
    {fixed : Fin n → Bool} (noBidirected : ∀ u w, graph.edge u true w true = false) :
    ¬ Collider graph x y fixed v := by
  rintro ⟨_, _, _, _, chain, member⟩
  cases chain with
  | nil => simp at member
  | cons edge _ _ => simp [noBidirected] at edge

/-- The formula reduces to `pa(YM) \ forb` on a graph without bidirected edges. -/
theorem o_set_iff_parent_part_without_bidirected (graph : MixedGraph n) (x y : Fin n)
    (fixed : Fin n → Bool) (v : Fin n)
    (noBidirected : ∀ u w, graph.edge u true w true = false) :
    InOSet graph x y fixed v ↔ ParentPart graph x y v := by
  constructor
  · rintro (parent | collider | ⟨_, collider, _⟩)
    · exact parent
    · exact (no_collider_without_bidirected noBidirected collider).elim
    · exact (no_collider_without_bidirected noBidirected collider).elim
  · exact Or.inl

end

end OpenCausalScience.Papers.Runge2021.OSet
