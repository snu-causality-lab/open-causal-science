module
public import OpenCausalScience.Graph.DirectedEdgeEdit
public import OpenCausalScience.Graph.Moralization
public import OpenCausalScience.Papers.Pearl1995.RuleTwo

/-! # Action and observation exchange from the ancestral moral graph

Pearl (1995), Theorem 4.1 Rule 2, with a finite factorized tabulation of
the ancestral margin of the cut-regime responses. The moral graph
places the unconditioned coordinates of each factor on one side of the
separator. Thus the four masses in the conditional-independence
identity split into two sums. This permits conditioning on nonroots.

The input tabulation is the factorized marginal on the ancestors of
the natural exchanged responses, set outcomes, and set covariates. The
graph represents these responses after the earlier actions and the
outgoing-arrow cut. The tabulation identity connects it to the original
response model. Source: https://proceedings.mlr.press/r0/pearl95a.html
-/

namespace OpenCausalScience.Papers.Pearl1995.RuleTwoMoralization

open Moralization

@[expose] public section

variable {n : Nat} {G : DAG n}

abbrev Assignment (n : Nat) := Fin n → Bool

def InScope (G : DAG n) (factorVertex coordinate : Fin n) : Prop :=
  coordinate = factorVertex ∨ G.edge coordinate factorVertex = true

def FactorLocal (G : DAG n) (factor : Fin n → Assignment n → Rat) : Prop :=
  ∀ v (s t : Assignment n), (∀ u, InScope G v u → s u = t u) → factor v s = factor v t

def LeftReach (Q : Query G) (v : Fin n) : Prop :=
  ∃ x, Q.left x = true ∧ Q.MoralWalk x v

theorem left_reach_of_left (Q : Query G) {v : Fin n} (left : Q.left v = true) :
    LeftReach Q v :=
  ⟨v, left, .nil v⟩

theorem not_left_reach_of_right (Q : Query G) (separated : ¬ Q.MoralConnection)
    {v : Fin n} (right : Q.right v = true) : ¬ LeftReach Q v := by
  rintro ⟨x, left, walk⟩
  exact separated ⟨x, v, left, right, walk⟩

private theorem moralWalk_snoc {Q : Query G} {x u v : Fin n}
    (walk : Q.MoralWalk x u) (edge : Q.MoralEdge u v) : Q.MoralWalk x v := by
  induction walk with
  | nil _ => exact .cons edge (.nil _)
  | cons first _ ih => exact .cons first (ih edge)

private theorem relevant_in_scope {Q : Query G} {v u : Fin n}
    (included : Q.relevant v) (member : InScope G v u) : Q.relevant u := by
  obtain same | parent := member
  · exact same.symm ▸ included
  · obtain ⟨w, hw, path⟩ := (Q.relevant_iff v).mp included
    exact (Q.relevant_iff u).mpr
      ⟨w, hw, DAG.ancestor_of_edge parent path⟩

private theorem moral_edge_of_common_scope {Q : Query G} {v u w : Fin n}
    (included : Q.relevant v) (left : InScope G v u) (right : InScope G v w)
    (uOutside : Q.condition.member u = false) (wOutside : Q.condition.member w = false)
    (distinct : u ≠ w) : Q.MoralEdge u w := by
  refine ⟨relevant_in_scope included left, relevant_in_scope included right,
    uOutside, wOutside, distinct, ?_⟩
  obtain same | parent := left
  · subst u
    exact right.elim (fun bad => (distinct bad.symm).elim) (fun edge => .inr (.inl edge))
  · obtain same | otherParent := right
    · subst w
      exact .inl parent
    · exact .inr (.inr ⟨v, included, parent, otherParent⟩)

/-- Every unconditioned coordinate of one factor is on the same side of
the moral separation. A factor containing only fixed coordinates may
be assigned to the other side. -/
theorem scope_stays_on_one_side {Q : Query G} {v u w : Fin n}
    (included : Q.relevant v) (left : InScope G v u) (right : InScope G v w)
    (uOutside : Q.condition.member u = false) (wOutside : Q.condition.member w = false)
    (reachable : LeftReach Q u) : LeftReach Q w := by
  by_cases same : u = w
  · exact same ▸ reachable
  · obtain ⟨x, hx, walk⟩ := reachable
    exact ⟨x, hx, moralWalk_snoc walk
      (moral_edge_of_common_scope included left right uOutside wOutside same)⟩

def LeftFactor (Q : Query G) (v : Fin n) : Prop :=
  ∃ u, InScope G v u ∧ Q.condition.member u = false ∧ LeftReach Q u

noncomputable def merge (Q : Query G) (w left right : Assignment n) : Assignment n :=
  open Classical in
  fun u => if Q.condition.member u then w u else if LeftReach Q u then left u else right u

/-- On the query coordinates, the merged table uses the fixed evidence,
the left row on the left query, and the right row on the right query. -/
theorem merge_on_query (Q : Query G) (w left right : Assignment n)
    (leftOutside : ∀ v, Q.left v = true → Q.condition.member v = false)
    (rightOutside : ∀ v, Q.right v = true → Q.condition.member v = false)
    (separated : ¬ Q.MoralConnection) :
    (∀ v, Q.condition.member v = true → merge Q w left right v = w v) ∧
    (∀ v, Q.left v = true → merge Q w left right v = left v) ∧
    (∀ v, Q.right v = true → merge Q w left right v = right v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    simp [merge, hv]
  · intro v hv
    simp [merge, leftOutside v hv, left_reach_of_left Q hv]
  · intro v hv
    simp [merge, rightOutside v hv, not_left_reach_of_right Q separated hv]

private theorem factor_eq_left {Q : Query G} (factor : Fin n → Assignment n → Rat)
    (locality : FactorLocal G factor) {v : Fin n} (included : Q.relevant v)
    (leftSide : LeftFactor Q v) (w l r : Assignment n) :
    factor v (merge Q w l r) = factor v (merge Q w l (fun _ => false)) := by
  apply locality
  intro u hu
  obtain ⟨a, ha, aOutside, aLeft⟩ := leftSide
  cases huW : Q.condition.member u with
  | true => simp [merge, huW]
  | false =>
    have left := scope_stays_on_one_side included ha hu aOutside huW aLeft
    simp [merge, huW, left]

private theorem factor_eq_right {Q : Query G} (factor : Fin n → Assignment n → Rat)
    (locality : FactorLocal G factor) {v : Fin n} (rightSide : ¬ LeftFactor Q v)
    (w l r : Assignment n) :
    factor v (merge Q w l r) = factor v (merge Q w (fun _ => false) r) := by
  apply locality
  intro u hu
  cases huW : Q.condition.member u with
  | true => simp [merge, huW]
  | false =>
    have right : ¬ LeftReach Q u := fun left => rightSide ⟨u, hu, huW, left⟩
    simp [merge, huW, right]

noncomputable def relevantVertices (Q : Query G) : List (Fin n) :=
  open Classical in
  (List.finRange n).filter (fun v => decide (Q.relevant v))

noncomputable def leftWeight (Q : Query G) (factor : Fin n → Assignment n → Rat)
    (w l : Assignment n) : Rat :=
  open Classical in
  (((relevantVertices Q).filter fun v => decide (LeftFactor Q v)).map
    fun v => factor v (merge Q w l (fun _ => false))).prod

noncomputable def rightWeight (Q : Query G) (factor : Fin n → Assignment n → Rat)
    (w r : Assignment n) : Rat :=
  open Classical in
  (((relevantVertices Q).filter fun v => !(decide (LeftFactor Q v))).map
    fun v => factor v (merge Q w (fun _ => false) r)).prod

private theorem product_split {A : Type} (rows : List A) (side : A → Bool)
    (full left right : A → Rat)
    (leftEq : ∀ a ∈ rows, side a = true → full a = left a)
    (rightEq : ∀ a ∈ rows, side a = false → full a = right a) :
    (rows.map full).prod =
      ((rows.filter side).map left).prod * ((rows.filter (fun a => !side a)).map right).prod := by
  induction rows with
  | nil => simp
  | cons a rest ih =>
    have lr : ∀ b ∈ rest, side b = true → full b = left b :=
      fun b hb => leftEq b (List.mem_cons_of_mem _ hb)
    have rr : ∀ b ∈ rest, side b = false → full b = right b :=
      fun b hb => rightEq b (List.mem_cons_of_mem _ hb)
    cases sideA : side a with
    | true =>
      simp only [List.map_cons, List.prod_cons, List.filter_cons, sideA, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, ih lr rr,
        leftEq a List.mem_cons_self sideA, Rat.mul_assoc]
    | false =>
      simp only [List.map_cons, List.prod_cons, List.filter_cons, sideA, Bool.not_false,
        Bool.false_eq_true, ↓reduceIte, ih lr rr,
        rightEq a List.mem_cons_self sideA]
      rw [← Rat.mul_assoc, Rat.mul_comm (right a), Rat.mul_assoc]

/-- The ancestral product at a fixed evidence value is a product of two
functions on disjoint coordinate sets. -/
theorem ancestral_product_splits (Q : Query G) (factor : Fin n → Assignment n → Rat)
    (locality : FactorLocal G factor) (w l r : Assignment n) :
    ((relevantVertices Q).map (fun v => factor v (merge Q w l r))).prod =
      leftWeight Q factor w l * rightWeight Q factor w r := by
  classical
  unfold leftWeight rightWeight
  apply product_split
  · intro v hv left
    have incl : Q.relevant v := of_decide_eq_true (List.mem_filter.mp hv).2
    exact factor_eq_left factor locality incl (of_decide_eq_true left) w l r
  · intro v _ right
    have noLeft : ¬ LeftFactor Q v := fun left => by simp [left] at right
    exact factor_eq_right factor locality noLeft w l r

structure Table (G : DAG n) where
  factor : Fin n → Assignment n → Rat
  locality : FactorLocal G factor
  leftRows : List (Assignment n)
  rightRows : List (Assignment n)

noncomputable def Table.mass (table : Table G) (Q : Query G) (w : Assignment n)
    (p q : Assignment n → Bool) : Rat :=
  (table.leftRows.map fun l =>
    (table.rightRows.map fun r => if p l && q r then
      ((relevantVertices Q).map (fun v => table.factor v (merge Q w l r))).prod else 0).sum).sum

private theorem sum_mul_const {A : Type} (xs : List A) (f : A → Rat) (c : Rat) :
    (xs.map (fun a => f a * c)).sum = (xs.map f).sum * c := by
  induction xs with
  | nil => simp
  | cons a rest ih => simp [ih, Rat.add_mul]

theorem Table.mass_product (table : Table G) (Q : Query G) (w : Assignment n)
    (p q : Assignment n → Bool) :
    table.mass Q w p q =
      (table.leftRows.map (fun l => if p l then leftWeight Q table.factor w l else 0)).sum *
      (table.rightRows.map (fun r => if q r then rightWeight Q table.factor w r else 0)).sum := by
  let leftTerm := fun l => if p l then leftWeight Q table.factor w l else 0
  let rightTerm := fun r => if q r then rightWeight Q table.factor w r else 0
  unfold Table.mass
  rw [← sum_mul_const table.leftRows leftTerm]
  apply congrArg List.sum
  apply List.map_congr_left
  intro l _
  change _ = leftTerm l * (table.rightRows.map rightTerm).sum
  rw [Rat.mul_comm (leftTerm l), ← sum_mul_const table.rightRows rightTerm]
  apply congrArg List.sum
  apply List.map_congr_left
  intro r _
  rw [Rat.mul_comm]
  cases lp : p l <;> cases rq : q r <;>
    simp [leftTerm, rightTerm, lp, rq, ancestral_product_splits Q table.factor table.locality]

/-- Event mass in the tabulated ancestral margin, with the evidence fixed. -/
noncomputable def Table.marginMass (table : Table G) (Q : Query G) (w : Assignment n)
    (event : Assignment n → Bool) : Rat :=
  (table.leftRows.map fun l =>
    (table.rightRows.map fun r => if event (merge Q w l r) then
      ((relevantVertices Q).map (fun v => table.factor v (merge Q w l r))).prod else 0).sum).sum

def ReadsOnly {A : Type} (coordinates : Fin n → Bool) (readout : Assignment n → A) : Prop :=
  ∀ first second, (∀ v, coordinates v = true → first v = second v) → readout first = readout second

theorem Table.marginMass_eq_side_mass {Z Y : Type} (table : Table G) (Q : Query G) (w : Assignment n)
    (leftReadout : Assignment n → Z) (rightReadout : Assignment n → Y)
    (leftReads : ReadsOnly Q.left leftReadout) (rightReads : ReadsOnly Q.right rightReadout)
    (leftOutside : ∀ v, Q.left v = true → Q.condition.member v = false)
    (rightOutside : ∀ v, Q.right v = true → Q.condition.member v = false)
    (separated : ¬ Q.DConnection) (p : Z → Bool) (q : Y → Bool) :
    table.marginMass Q w (fun a => p (leftReadout a) && q (rightReadout a)) =
      table.mass Q w (p ∘ leftReadout) (q ∘ rightReadout) := by
  unfold Table.marginMass Table.mass
  apply congrArg List.sum
  apply List.map_congr_left
  intro l _
  apply congrArg List.sum
  apply List.map_congr_left
  intro r _
  have noWalk := (Q.dSeparation_iff_no_moralConnection leftOutside rightOutside).mp separated
  have merged := merge_on_query Q w l r leftOutside rightOutside noWalk
  simp only [Function.comp_apply, leftReads _ _ merged.2.1, rightReads _ _ merged.2.2]

/-- Exact tabulation of the cut-regime ancestral marginal at a given
evidence value. The readouts here are functions of the full merged
assignment. Separation is what makes them evaluable on their own rows. -/
def MatchesResponses {Ω Z Y W : Type} [DecidableEq W]
    (table : Table G) (Q : Query G) (model : RuleTwo.Model Ω Z Y W)
    (z : Z) (w : W) (evidence : Assignment n)
    (leftReadout : Assignment n → Z) (rightReadout : Assignment n → Y) : Prop :=
  ∀ (p : Z → Bool) (q : Y → Bool),
    model.mass (fun atom => decide ((model.respond z atom).2 = w) &&
      (p (model.observe atom) && q (model.respond z atom).1)) =
      table.marginMass Q evidence (fun a => p (leftReadout a) && q (rightReadout a))

private theorem mul_cross (a b c d : Rat) : (a * b) * (c * d) = (c * b) * (a * d) := by
  calc
    (a * b) * (c * d) = a * ((b * c) * d) := by rw [Rat.mul_assoc a b, Rat.mul_assoc b c]
    _ = (a * (c * b)) * d := by rw [Rat.mul_comm b c, Rat.mul_assoc a]
    _ = (c * b) * (a * d) := by rw [Rat.mul_comm a (c * b), Rat.mul_assoc]

/-- D-separation in the cut graph entails the cellwise independence
identity for a response model with an exact factorized ancestral table.
The endpoint readouts may be joint values. The evidence may contain
nonroot coordinates. -/
theorem independent_at_of_factorized_ancestral_margin {Ω Z Y W : Type}
    [DecidableEq Z] [DecidableEq Y] [DecidableEq W]
    (table : Table G) (Q : Query G) (model : RuleTwo.Model Ω Z Y W)
    (z : Z) (y : Y) (w : W) (evidence : Assignment n)
    (leftReadout : Assignment n → Z) (rightReadout : Assignment n → Y)
    (leftReads : ReadsOnly Q.left leftReadout) (rightReads : ReadsOnly Q.right rightReadout)
    (leftOutside : ∀ v, Q.left v = true → Q.condition.member v = false)
    (rightOutside : ∀ v, Q.right v = true → Q.condition.member v = false)
    (separated : ¬ Q.DConnection)
    (tabulated : MatchesResponses table Q model z w evidence leftReadout rightReadout) :
    model.independentAt z y w := by
  let zEvent : Z → Bool := fun a => decide (a = z)
  let yEvent : Y → Bool := fun b => decide (b = y)
  have masses (p : Z → Bool) (q : Y → Bool) :
      model.mass (fun atom => decide ((model.respond z atom).2 = w) &&
        (p (model.observe atom) && q (model.respond z atom).1)) =
        table.mass Q evidence (p ∘ leftReadout) (q ∘ rightReadout) :=
    (tabulated p q).trans (table.marginMass_eq_side_mass Q evidence leftReadout rightReadout
      leftReads rightReads leftOutside rightOutside separated p q)
  have joint : model.setNaturalJointMass z y w =
      table.mass Q evidence (zEvent ∘ leftReadout) (yEvent ∘ rightReadout) := by
    rw [← masses zEvent yEvent]
    apply congrArg model.mass
    funext atom
    rcases h : model.respond z atom with ⟨out,cov⟩
    simp [zEvent, yEvent, Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
  have evidenceOnly : model.setCovariateMass z w =
      table.mass Q evidence (fun _ => true) (fun _ => true) := by
    simpa [RuleTwo.Model.setCovariateMass, Function.comp_def] using
      masses (fun _ => true) (fun _ => true)
  have outcome : model.setJointMass z y w =
      table.mass Q evidence (fun _ => true) (yEvent ∘ rightReadout) := by
    change _ = table.mass Q evidence ((fun _ : Z => true) ∘ leftReadout)
      (yEvent ∘ rightReadout)
    rw [← masses (fun _ => true) yEvent]
    apply congrArg model.mass
    funext atom
    rcases h : model.respond z atom with ⟨out,cov⟩
    simp [yEvent, Bool.and_comm]
  have natural : model.setNaturalCovariateMass z w =
      table.mass Q evidence (zEvent ∘ leftReadout) (fun _ => true) := by
    simpa [RuleTwo.Model.setNaturalCovariateMass, Function.comp_def, zEvent, Bool.and_comm] using
      masses zEvent (fun _ => true)
  unfold RuleTwo.Model.independentAt
  rw [joint, evidenceOnly, outcome, natural]
  simp only [Table.mass_product]
  exact mul_cross _ _ _ _

/-- Pearl's exchange identity on supported cells, deriving the
independence premise from separation and a factorized ancestral table. -/
theorem supported_rule_two_of_factorized_ancestral_margin {Ω Z Y W : Type}
    [DecidableEq Z] [DecidableEq Y] [DecidableEq W]
    (table : Table G) (Q : Query G) (model : RuleTwo.Model Ω Z Y W)
    (z : Z) (y : Y) (w : W) (evidence : Assignment n)
    (leftReadout : Assignment n → Z) (rightReadout : Assignment n → Y)
    (leftReads : ReadsOnly Q.left leftReadout) (rightReads : ReadsOnly Q.right rightReadout)
    (leftOutside : ∀ v, Q.left v = true → Q.condition.member v = false)
    (rightOutside : ∀ v, Q.right v = true → Q.condition.member v = false)
    (separated : ¬ Q.DConnection)
    (tabulated : MatchesResponses table Q model z w evidence leftReadout rightReadout)
    (observed : 0 < model.observationalCovariateMass z w) (action : 0 < model.setCovariateMass z w) :
    model.setJointMass z y w / model.setCovariateMass z w =
      model.observationalJointMass z y w / model.observationalCovariateMass z w :=
  model.supported_action_observation_exchange z y w observed action
    (independent_at_of_factorized_ancestral_margin table Q model z y w evidence
      leftReadout rightReadout leftReads rightReads leftOutside rightOutside separated tabulated)

end

end OpenCausalScience.Papers.Pearl1995.RuleTwoMoralization
