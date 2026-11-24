module
public import OpenCausalScience.Papers.HwangEtAl2024Positivity.AncestorPartition

/-! # Retaining scope feasibility in the mixed-policy reduction

[Lee and Bareinboim, corrected version, Proposition 5 and Appendix F](https://www.sanghacklee.me/ai-corrected/POMPS2020_AI_corrected_2026-09-20.pdf).
The reduced mechanisms use the induced directed graph. The policy scopes
continue to use the original feasibility condition. A topological rank
witnesses feasibility. Exogenous and policy inputs are fixed throughout each
pointwise comparison, so they may subsequently be integrated against a
common joint law. Mechanisms can ignore inputs allowed by the graph.
-/

namespace OpenCausalScience.Papers.LeeBareinboim2020.ScopeReduction

open OpenCausalScience.Papers.HwangEtAl2024Positivity.AncestorPartition (Reaches cutIncoming)

@[expose] public section

variable {V : Type}

structure Scope (V : Type) where
  target : V → Prop
  context : V → V → Prop
  context_target : ∀ {u v}, context u v → target v

def scopedEdge (edge : V → V → Prop) (S : Scope V) (u v : V) : Prop :=
  cutIncoming edge S.target u v ∨ S.context u v

def TopologicalRank (edge : V → V → Prop) (rank : V → Nat) : Prop :=
  ∀ u v, edge u v → rank u < rank v

def ValidScope (edge : V → V → Prop) (actions contexts : V → Prop) (S : Scope V) : Prop :=
  (∀ v, S.target v → actions v) ∧
  (∀ u v, S.context u v → contexts u ∧ u ≠ v) ∧
  ∃ rank, TopologicalRank (scopedEdge edge S) rank

/-- Strict descendants of the reward after cutting incoming edges to every
eligible action. -/
def deleted (edge : V → V → Prop) (actions : V → Prop) (reward v : V) : Prop :=
  v ≠ reward ∧ Reaches (cutIncoming edge actions) reward v

def inducedEdge (edge : V → V → Prop) (D : V → Prop) (u v : V) : Prop :=
  edge u v ∧ ¬ D u ∧ ¬ D v

private theorem reaches_mono {g h : V → V → Prop} (sub : ∀ u v, g u v → h u v)
    {u v : V} (path : Reaches g u v) : Reaches h u v := by
  induction path with
  | refl node => exact .refl node
  | step e _ ih => exact .step (sub _ _ e) ih

private theorem rank_le {edge : V → V → Prop} {rank : V → Nat}
    (topo : TopologicalRank edge rank) {u v : V} (path : Reaches edge u v) : rank u ≤ rank v := by
  induction path with
  | refl => exact Nat.le_refl _
  | step e _ ih => exact Nat.le_trans (Nat.le_of_lt (topo _ _ e)) ih

private theorem rank_lt {edge : V → V → Prop} {rank : V → Nat}
    (topo : TopologicalRank edge rank) {u v : V} (path : Reaches edge u v)
    (distinct : u ≠ v) : rank u < rank v := by
  cases path with
  | refl => exact False.elim (distinct rfl)
  | step e tail => exact Nat.lt_of_lt_of_le (topo _ _ e) (rank_le topo tail)

private theorem action_free_endpoint {edge : V → V → Prop} {actions : V → Prop}
    {u v : V} (path : Reaches (cutIncoming edge actions) u v) (notEligible : ¬ actions u) :
    ¬ actions v := by
  induction path with
  | refl => exact notEligible
  | step e _ ih => exact ih e.2

theorem deleted_not_eligible {edge : V → V → Prop} {actions : V → Prop} {reward d : V}
    (hd : deleted edge actions reward d) : ¬ actions d := by
  rcases hd with ⟨different, path⟩
  cases path with
  | refl => exact False.elim (different rfl)
  | step e tail => exact action_free_endpoint tail e.2

private theorem cut_path_stays {edge : V → V → Prop} {actions : V → Prop} {S : Scope V}
    (eligible : ∀ v, S.target v → actions v) {u v : V}
    (path : Reaches (cutIncoming edge actions) u v) : Reaches (scopedEdge edge S) u v :=
  reaches_mono (fun _ v e => Or.inl ⟨e.1, fun h => e.2 (eligible v h)⟩) path

/-- Every deleted vertex stays a strict descendant of the reward in every
originally valid scope, even if context arrows are added. -/
theorem deleted_not_reward_ancestor {edge : V → V → Prop} {actions : V → Prop}
    {S : Scope V} {rank : V → Nat} (eligible : ∀ v, S.target v → actions v)
    (topo : TopologicalRank (scopedEdge edge S) rank) {reward d : V}
    (hd : deleted edge actions reward d) : ¬ Reaches (scopedEdge edge S) d reward := by
  intro reversePath
  have strict := rank_lt topo (cut_path_stays eligible hd.2) (Ne.symm hd.1)
  exact (Nat.not_le_of_gt strict) (rank_le topo reversePath)

/-- Any action that observes a deleted vertex lies outside the reward
ancestry. This is the graph step behind removing the observation. -/
theorem deleted_context_target_not_reward_ancestor {edge : V → V → Prop} {actions : V → Prop}
    {S : Scope V} {rank : V → Nat} (eligible : ∀ v, S.target v → actions v)
    (topo : TopologicalRank (scopedEdge edge S) rank) {reward d a : V}
    (hd : deleted edge actions reward d) (observes : S.context d a) :
    ¬ Reaches (scopedEdge edge S) a reward := by
  intro path
  exact deleted_not_reward_ancestor eligible topo hd (.step (Or.inr observes) path)

/-- The original topological ranking remains valid after dropping vertices
from the natural graph. It still witnesses the original feasibility test. -/
theorem induced_scope_rank {edge : V → V → Prop} {D : V → Prop} {S : Scope V} {rank : V → Nat}
    (topo : TopologicalRank (scopedEdge edge S) rank) :
    TopologicalRank (scopedEdge (inducedEdge edge D) S) rank := by
  intro u v arrow
  rcases arrow with ⟨⟨edge, _, _⟩, noTarget⟩ | context
  · exact topo u v (Or.inl ⟨edge, noTarget⟩)
  · exact topo u v (Or.inr context)

abbrev Assignment (Value : V → Type) := (v : V) → Value v

structure Mechanisms (edge : V → V → Prop) (Noise Value : V → Type) where
  eval (v : V) : Noise v → Assignment Value → Value v
  local_inputs (v : V) (z : Noise v) (x x' : Assignment Value) :
    (∀ u, edge u v → x u = x' u) → eval v z x = eval v z x'

abbrev Equations (Value : V → Type) := (v : V) → Assignment Value → Value v

private def LocalInputs (edge : V → V → Prop) {Value : V → Type} (eqn : Equations Value) : Prop :=
  ∀ v x x', (∀ u, edge u v → x u = x' u) → eqn v x = eqn v x'

noncomputable def solve {Value : V → Type} (rank : V → Nat) (initial : Assignment Value)
    (eqn : Equations Value) : Assignment Value :=
  (measure rank).wf.fix fun v solveEarlier =>
    eqn v (fun u => if h : rank u < rank v then solveEarlier u h else initial u)

private theorem solve_eq {edge : V → V → Prop} {Value : V → Type} {rank : V → Nat}
    (topo : TopologicalRank edge rank) (initial : Assignment Value)
    (eqn : Equations Value) (onlyParents : LocalInputs edge eqn) (v : V) :
    solve rank initial eqn v = eqn v (solve rank initial eqn) := by
  unfold solve
  rw [WellFounded.fix_eq]
  apply onlyParents
  intro u arrow
  exact dite_eq_left (topo _ _ arrow)

private theorem agree_on_ancestors {edge : V → V → Prop} {Value : V → Type}
    {rank : V → Nat} (topo : TopologicalRank edge rank) (reward : V)
    (eqn other : Equations Value) (x x' : Assignment Value)
    (xSolves : ∀ v, x v = eqn v x) (x'Solves : ∀ v, x' v = other v x')
    (eqnAgree : ∀ v, Reaches edge v reward → ∀ a a',
      (∀ u, edge u v → a u = a' u) → eqn v a = other v a') :
    ∀ v, Reaches edge v reward → x v = x' v := by
  intro v
  induction v using (measure rank).wf.induction with
  | h v ih =>
    intro path
    rw [xSolves v, x'Solves v]
    exact eqnAgree v path x x' (fun u arrow => ih u (topo _ _ arrow) (.step arrow path))

noncomputable def policyEquations {edge : V → V → Prop} {Noise Seed Value : V → Type}
    {S : Scope V} (m : Mechanisms edge Noise Value) (π : Mechanisms S.context Seed Value)
    (z : Assignment Noise) (seed : Assignment Seed) : Equations Value := by
  classical
  exact fun v x => if S.target v then π.eval v (seed v) x else m.eval v (z v) x

private theorem policy_equations_local {edge : V → V → Prop} {Noise Seed Value : V → Type}
    {S : Scope V} (m : Mechanisms edge Noise Value) (π : Mechanisms S.context Seed Value)
    (z : Assignment Noise) (seed : Assignment Seed) :
    LocalInputs (scopedEdge edge S) (policyEquations m π z seed) := by
  intro v x x' eqParents
  by_cases h : S.target v
  · simpa [policyEquations, h] using π.local_inputs v (seed v) x x'
      (fun u observes => eqParents u (Or.inr observes))
  · simpa [policyEquations, h] using m.local_inputs v (z v) x x'
      (fun u e => eqParents u (Or.inl ⟨e, h⟩))

noncomputable def restrictMechanisms {edge : V → V → Prop} {Noise Value : V → Type}
    (D : V → Prop) (initial : Assignment Value) (m : Mechanisms edge Noise Value) :
    Mechanisms (inducedEdge edge D) Noise Value := by
  classical
  refine ⟨fun v z x => if D v then initial v else m.eval v z (fun u => if D u then initial u else x u), ?_⟩
  intro v z x x' eqParents
  by_cases dv : D v
  · simp [dv]
  · simp only [ite_eq_right dv]
    apply m.local_inputs
    intro u e
    by_cases du : D u
    · simp [du]
    · simpa [du] using eqParents u ⟨e, du, dv⟩

noncomputable def extendMechanisms {edge : V → V → Prop} {Noise Value : V → Type}
    (D : V → Prop) (initial : Assignment Value) (m : Mechanisms (inducedEdge edge D) Noise Value) :
    Mechanisms edge Noise Value := by
  classical
  refine ⟨fun v z x => if D v then initial v else m.eval v z x, ?_⟩
  intro v z x x' eqParents
  by_cases dv : D v
  · simp [dv]
  · simpa [dv] using m.local_inputs v z x x' (fun u e => eqParents u e.1)

noncomputable def policyReward {edge : V → V → Prop} {Noise Seed Value : V → Type}
    {S : Scope V} (rank : V → Nat) (initial : Assignment Value) (reward : V)
    (m : Mechanisms edge Noise Value) (π : Mechanisms S.context Seed Value)
    (z : Assignment Noise) (seed : Assignment Seed) : Value reward :=
  solve rank initial (policyEquations m π z seed) reward

/-- Fixing deleted parents gives the same reward for every original SCM,
valid scope, policy, exogenous draw, and draw of the policy's private seeds.
The restriction of the natural mechanisms is independent of the scope. -/
theorem restrict_preserves_policy_reward {edge : V → V → Prop} {actions : V → Prop}
    {Noise Seed Value : V → Type} {S : Scope V} {rank : V → Nat}
    (eligible : ∀ v, S.target v → actions v) (topo : TopologicalRank (scopedEdge edge S) rank)
    (initial : Assignment Value) (reward : V) (m : Mechanisms edge Noise Value)
    (π : Mechanisms S.context Seed Value) (z : Assignment Noise) (seed : Assignment Seed) :
    policyReward rank initial reward m π z seed =
      policyReward rank initial reward (restrictMechanisms (deleted edge actions reward) initial m)
        π z seed := by
  classical
  let reduced := restrictMechanisms (deleted edge actions reward) initial m
  let originalEquation := policyEquations m π z seed
  let reducedEquation := policyEquations reduced π z seed
  refine agree_on_ancestors topo reward originalEquation reducedEquation _ _
    (solve_eq topo initial _ (policy_equations_local m π z seed))
    (solve_eq (induced_scope_rank topo) initial _ (policy_equations_local reduced π z seed))
    ?_ reward (.refl reward)
  intro v path x x' agreeParents
  by_cases target : S.target v
  · simpa [originalEquation, reducedEquation, policyEquations, target] using
      π.local_inputs v (seed v) x x' (fun u observes => agreeParents u (Or.inr observes))
  · have retainedV : ¬ deleted edge actions reward v :=
      fun isDeleted => deleted_not_reward_ancestor eligible topo isDeleted path
    simp only [originalEquation, reducedEquation, policyEquations, ite_eq_right target,
      reduced, restrictMechanisms, ite_eq_right retainedV]
    apply m.local_inputs
    intro u incoming
    have arrow : scopedEdge edge S u v := Or.inl ⟨incoming, target⟩
    have retainedU : ¬ deleted edge actions reward u :=
      fun isDeleted => deleted_not_reward_ancestor eligible topo isDeleted (.step arrow path)
    simpa [retainedU] using agreeParents u arrow

/-- Giving deleted vertices constant mechanisms, and letting retained
mechanisms ignore the added inputs, preserves each reward in the other
direction. The retained mechanism uses the same local noise value. -/
theorem extend_preserves_policy_reward {edge : V → V → Prop} {actions : V → Prop}
    {Noise Seed Value : V → Type} {S : Scope V} {rank : V → Nat}
    (eligible : ∀ v, S.target v → actions v) (topo : TopologicalRank (scopedEdge edge S) rank)
    (initial : Assignment Value) (reward : V)
    (m : Mechanisms (inducedEdge edge (deleted edge actions reward)) Noise Value)
    (π : Mechanisms S.context Seed Value) (z : Assignment Noise) (seed : Assignment Seed) :
    policyReward rank initial reward (extendMechanisms (deleted edge actions reward) initial m)
      π z seed = policyReward rank initial reward m π z seed := by
  classical
  let extended := extendMechanisms (deleted edge actions reward) initial m
  let extendedEquation := policyEquations extended π z seed
  let reducedEquation := policyEquations m π z seed
  refine agree_on_ancestors topo reward extendedEquation reducedEquation _ _
    (solve_eq topo initial _ (policy_equations_local extended π z seed))
    (solve_eq (induced_scope_rank topo) initial _ (policy_equations_local m π z seed))
    ?_ reward (.refl reward)
  intro v path x x' agreeParents
  by_cases target : S.target v
  · simpa [extendedEquation, reducedEquation, policyEquations, target] using
      π.local_inputs v (seed v) x x' (fun u observes => agreeParents u (Or.inr observes))
  · have retainedV : ¬ deleted edge actions reward v :=
      fun isDeleted => deleted_not_reward_ancestor eligible topo isDeleted path
    simpa [extendedEquation, reducedEquation, policyEquations, target, extended,
      extendMechanisms, retainedV] using
      m.local_inputs v (z v) x x' (fun u e => agreeParents u (Or.inl ⟨e.1, target⟩))

def removeObservation (S : Scope V) (d a : V) : Scope V where
  target := S.target
  context u v := S.context u v ∧ ¬ (u = d ∧ v = a)
  context_target h := S.context_target h.1

private theorem removed_arrow_was_present {edge : V → V → Prop} {S : Scope V} {d a u v : V}
    (e : scopedEdge edge (removeObservation S d a) u v) : scopedEdge edge S u v :=
  e.imp id And.left

theorem removing_observation_preserves_validity {edge : V → V → Prop} {actions contexts : V → Prop}
    {S : Scope V} (valid : ValidScope edge actions contexts S) (d a : V) :
    ValidScope edge actions contexts (removeObservation S d a) := by
  obtain ⟨eligible, permitted, rank, topo⟩ := valid
  exact ⟨eligible, fun u v h => permitted u v h.1, rank,
    fun u v h => topo u v (removed_arrow_was_present h)⟩

noncomputable def dropPolicyInput {Noise Value : V → Type} {S : Scope V}
    (d a : V) (initial : Assignment Value) (π : Mechanisms S.context Noise Value) :
    Mechanisms (removeObservation S d a).context Noise Value := by
  classical
  refine ⟨fun v z x => π.eval v z (fun u => if u = d ∧ v = a then initial u else x u), ?_⟩
  intro v z x x' agree
  apply π.local_inputs
  intro u observes
  by_cases dropped : u = d ∧ v = a
  · simp [dropped]
  · simpa [dropped] using agree u ⟨observes, dropped⟩

def ignorePolicyInput {Noise Value : V → Type} {S : Scope V} {d a : V}
    (π : Mechanisms (removeObservation S d a).context Noise Value) : Mechanisms S.context Noise Value :=
  ⟨π.eval, fun v z x x' agree => π.local_inputs v z x x' (fun u observes => agree u observes.1)⟩

/-- If an originally valid policy observes a deleted node, replacing that
input at the observing action leaves its reward unchanged. The two rank
witnesses may differ, as when each scope chooses its own topological order. -/
theorem drop_deleted_observation_preserves_policy_reward {edge : V → V → Prop}
    {actions : V → Prop} {Noise Seed Value : V → Type} {S : Scope V} {rank reducedRank : V → Nat}
    {reward d a : V}
    (eligible : ∀ v, S.target v → actions v) (topo : TopologicalRank (scopedEdge edge S) rank)
    (reducedTopo : TopologicalRank (scopedEdge edge (removeObservation S d a)) reducedRank)
    (initial : Assignment Value) (hd : deleted edge actions reward d)
    (observes : S.context d a) (m : Mechanisms edge Noise Value)
    (π : Mechanisms S.context Seed Value) (z : Assignment Noise) (seed : Assignment Seed) :
    policyReward rank initial reward m π z seed =
      policyReward reducedRank initial reward m (dropPolicyInput d a initial π) z seed := by
  classical
  let smallerPolicy := dropPolicyInput d a initial π
  let originalEquation := policyEquations m π z seed
  let smallerEquation := policyEquations m smallerPolicy z seed
  refine agree_on_ancestors topo reward originalEquation smallerEquation _ _
    (solve_eq topo initial _ (policy_equations_local m π z seed))
    (solve_eq reducedTopo initial _ (policy_equations_local m smallerPolicy z seed))
    ?_ reward (.refl reward)
  intro v path x x' agreeParents
  have notTargetOfDropped : v ≠ a := by
    intro eq
    subst v
    exact deleted_context_target_not_reward_ancestor eligible topo hd observes path
  by_cases target : S.target v
  · simpa [originalEquation, smallerEquation, policyEquations, removeObservation, target,
      smallerPolicy, dropPolicyInput, notTargetOfDropped] using
      π.local_inputs v (seed v) x x' (fun u e => agreeParents u (Or.inr e))
  · simpa [originalEquation, smallerEquation, policyEquations, removeObservation, target] using
      m.local_inputs v (z v) x x' (fun u e => agreeParents u (Or.inl ⟨e, target⟩))

/-- A policy for the smaller scope can ignore the extra observation and
attain the same reward in the larger scope. -/
theorem ignoring_observation_preserves_policy_reward {edge : V → V → Prop}
    {Noise Seed Value : V → Type} {S : Scope V} {rank reducedRank : V → Nat} {d a : V}
    (topo : TopologicalRank (scopedEdge edge S) rank)
    (reducedTopo : TopologicalRank (scopedEdge edge (removeObservation S d a)) reducedRank)
    (initial : Assignment Value) (reward : V) (m : Mechanisms edge Noise Value)
    (π : Mechanisms (removeObservation S d a).context Seed Value)
    (z : Assignment Noise) (seed : Assignment Seed) :
    policyReward rank initial reward m (ignorePolicyInput π) z seed =
      policyReward reducedRank initial reward m π z seed := by
  classical
  let largerPolicy := ignorePolicyInput π
  let largerEquation := policyEquations m largerPolicy z seed
  let smallerEquation := policyEquations m π z seed
  refine agree_on_ancestors topo reward largerEquation smallerEquation _ _
    (solve_eq topo initial _ (policy_equations_local m largerPolicy z seed))
    (solve_eq reducedTopo initial _ (policy_equations_local m π z seed))
    ?_ reward (.refl reward)
  intro v _ x x' agreeParents
  by_cases target : S.target v
  · simpa [largerEquation, smallerEquation, policyEquations, removeObservation, target,
      largerPolicy, ignorePolicyInput] using
      π.local_inputs v (seed v) x x' (fun u e => agreeParents u (Or.inr e.1))
  · simpa [largerEquation, smallerEquation, policyEquations, removeObservation, target] using
      m.local_inputs v (z v) x x' (fun u e => agreeParents u (Or.inl ⟨e, target⟩))

structure Problem (V : Type) where
  edge : V → V → Prop
  actions : V → Prop
  contexts : V → Prop
  reward : V

def Problem.valid (P : Problem V) (S : Scope V) : Prop :=
  ValidScope P.edge P.actions P.contexts S

def Problem.deleted (P : Problem V) : V → Prop :=
  ScopeReduction.deleted P.edge P.actions P.reward

def Problem.retained (P : Problem V) (S : Scope V) : Prop :=
  P.valid S ∧ ∀ u v, S.context u v → ¬ P.deleted u

def Problem.induced (P : Problem V) : V → V → Prop := inducedEdge P.edge P.deleted

noncomputable def Problem.rank (P : Problem V) (S : Scope V) : V → Nat := by
  classical
  exact if valid : P.valid S then Classical.choose valid.2.2 else fun _ => 0

private theorem Problem.rank_witness {P : Problem V} {S : Scope V} (valid : P.valid S) :
    TopologicalRank (scopedEdge P.edge S) (P.rank S) := by
  classical
  simpa [Problem.rank, valid] using Classical.choose_spec valid.2.2

def Subscope (T S : Scope V) : Prop :=
  (∀ v, T.target v → S.target v) ∧ (∀ u v, T.context u v → S.context u v)

def ProperSubscope (T S : Scope V) : Prop := Subscope T S ∧ ¬ Subscope S T

private theorem removed_observation_proper {S : Scope V} {d a : V} (observes : S.context d a) :
    ProperSubscope (removeObservation S d a) S := by
  refine ⟨⟨fun _ h => h, fun _ _ h => h.1⟩, ?_⟩
  intro h
  exact (h.2 d a observes).2 ⟨rfl, rfl⟩

private theorem retained_proper_subscope {P : Problem V} {S T : Scope V}
    (retained : P.retained S) (valid : P.valid T) (subscope : Subscope T S) : P.retained T :=
  ⟨valid, fun u v input => retained.2 u v (subscope.2 u v input)⟩

abbrev RewardTrace (Noise Seed Value : V → Type) (reward : V) :=
  Assignment Noise → Assignment Seed → Value reward

/-- The readout can be expected reward under any fixed common joint law of
the exogenous inputs and private policy randomizers. The same admissible
class applies on both graphs and can impose the chosen independence
constraints. -/
structure Model (edge : V → V → Prop) (Noise Seed Value : V → Type) (reward : V) (Score : Type)
    (admissible : (RewardTrace Noise Seed Value reward → Score) → Prop) where
  mechanisms : Mechanisms edge Noise Value
  expected : RewardTrace Noise Seed Value reward → Score
  expected_admissible : admissible expected

def Attainable (P : Problem V) {edge : V → V → Prop} {Noise Seed Value : V → Type} {Score : Type}
    {admissible : (RewardTrace Noise Seed Value P.reward → Score) → Prop}
    (initial : Assignment Value) (m : Model edge Noise Seed Value P.reward Score admissible)
    (S : Scope V) (score : Score) : Prop :=
  ∃ π : Mechanisms S.context Seed Value,
    m.expected (policyReward (P.rank S) initial P.reward m.mechanisms π) = score

noncomputable def restrictModel {P : Problem V} {Noise Seed Value : V → Type} {Score : Type}
    {admissible : (RewardTrace Noise Seed Value P.reward → Score) → Prop}
    (initial : Assignment Value) (m : Model P.edge Noise Seed Value P.reward Score admissible) :
    Model P.induced Noise Seed Value P.reward Score admissible :=
  ⟨restrictMechanisms P.deleted initial m.mechanisms, m.expected, m.expected_admissible⟩

noncomputable def extendModel {P : Problem V} {Noise Seed Value : V → Type} {Score : Type}
    {admissible : (RewardTrace Noise Seed Value P.reward → Score) → Prop}
    (initial : Assignment Value) (m : Model P.induced Noise Seed Value P.reward Score admissible) :
    Model P.edge Noise Seed Value P.reward Score admissible :=
  ⟨extendMechanisms P.deleted initial m.mechanisms, m.expected, m.expected_admissible⟩

theorem restriction_preserves_attainable {P : Problem V} {Noise Seed Value : V → Type} {Score : Type}
    {admissible : (RewardTrace Noise Seed Value P.reward → Score) → Prop}
    (initial : Assignment Value) (m : Model P.edge Noise Seed Value P.reward Score admissible)
    {S : Scope V} (valid : P.valid S) :
    Attainable P initial m S = Attainable P initial (restrictModel initial m) S := by
  have same (π : Mechanisms S.context Seed Value) :
      policyReward (P.rank S) initial P.reward m.mechanisms π =
        policyReward (P.rank S) initial P.reward (restrictModel initial m).mechanisms π := by
    funext z seed
    exact restrict_preserves_policy_reward valid.1 (P.rank_witness valid)
      initial P.reward m.mechanisms π z seed
  funext score
  apply propext
  change (∃ π : Mechanisms S.context Seed Value, m.expected _ = score) ↔
    (∃ π : Mechanisms S.context Seed Value, m.expected _ = score)
  simp only [same]

theorem extension_preserves_attainable {P : Problem V} {Noise Seed Value : V → Type} {Score : Type}
    {admissible : (RewardTrace Noise Seed Value P.reward → Score) → Prop}
    (initial : Assignment Value) (m : Model P.induced Noise Seed Value P.reward Score admissible)
    {S : Scope V} (valid : P.valid S) :
    Attainable P initial (extendModel initial m) S = Attainable P initial m S := by
  have same (π : Mechanisms S.context Seed Value) :
      policyReward (P.rank S) initial P.reward (extendModel initial m).mechanisms π =
        policyReward (P.rank S) initial P.reward m.mechanisms π := by
    funext z seed
    exact extend_preserves_policy_reward valid.1 (P.rank_witness valid)
      initial P.reward m.mechanisms π z seed
  funext score
  apply propext
  change (∃ π : Mechanisms S.context Seed Value, m.expected _ = score) ↔
    (∃ π : Mechanisms S.context Seed Value, m.expected _ = score)
  simp only [same]

private theorem dropping_deleted_observation_attainable {P : Problem V}
    {Noise Seed Value : V → Type} {Score : Type}
    {admissible : (RewardTrace Noise Seed Value P.reward → Score) → Prop}
    (initial : Assignment Value) (m : Model P.edge Noise Seed Value P.reward Score admissible)
    {S : Scope V} (valid : P.valid S) {d a : V} (hd : P.deleted d) (obs : S.context d a) :
    Attainable P initial m S = Attainable P initial m (removeObservation S d a) := by
  have smallerValid := removing_observation_preserves_validity valid d a
  funext score
  apply propext
  constructor
  · rintro ⟨π, h⟩
    refine ⟨dropPolicyInput d a initial π, ?_⟩
    have same : policyReward (P.rank S) initial P.reward m.mechanisms π =
        policyReward (P.rank (removeObservation S d a)) initial P.reward m.mechanisms
          (dropPolicyInput d a initial π) := by
      funext z seed
      exact drop_deleted_observation_preserves_policy_reward valid.1
        (P.rank_witness valid) (P.rank_witness smallerValid) initial hd obs m.mechanisms π z seed
    simpa only [same] using h
  · rintro ⟨π, h⟩
    refine ⟨ignorePolicyInput π, ?_⟩
    have same : policyReward (P.rank S) initial P.reward m.mechanisms (ignorePolicyInput π) =
        policyReward (P.rank (removeObservation S d a)) initial P.reward m.mechanisms π := by
      funext z seed
      exact ignoring_observation_preserves_policy_reward (P.rank_witness valid)
        (P.rank_witness smallerValid) initial P.reward m.mechanisms π z seed
    simpa only [same] using h

def IsMaximum {Score : Type} [LE Score] (values : Score → Prop) (value : Score) : Prop :=
  values value ∧ ∀ other, values other → other ≤ value

def Beats {Score : Type} [LE Score] [LT Score] (a b : Score → Prop) : Prop :=
  ∃ x y, IsMaximum a x ∧ IsMaximum b y ∧ y < x

private theorem never_beats_itself {Score : Type} [LE Score] [LT Score] [Std.LawfulOrderLT Score]
    (values : Score → Prop) : ¬ Beats values values := by
  rintro ⟨x, y, maxX, maxY, better⟩
  exact (Std.not_le_of_gt better) (maxY.2 x maxX.1)

/-- One model produces the whole vector on the original valid retained
scopes. The maxima may be read off as soon as each is attained. -/
theorem optimal_value_vectors_equal {P : Problem V} {Noise Seed Value : V → Type} {Score : Type}
    (admissible : (RewardTrace Noise Seed Value P.reward → Score) → Prop)
    [LE Score] (initial : Assignment Value) (vector : Scope V → Score) :
    (∃ m : Model P.edge Noise Seed Value P.reward Score admissible, ∀ S, P.retained S →
      IsMaximum (Attainable P initial m S) (vector S)) ↔
    (∃ m : Model P.induced Noise Seed Value P.reward Score admissible, ∀ S, P.retained S →
      IsMaximum (Attainable P initial m S) (vector S)) := by
  constructor
  · rintro ⟨m, h⟩
    exact ⟨restrictModel initial m, fun S retained =>
      restriction_preserves_attainable initial m retained.1 ▸ h S retained⟩
  · rintro ⟨m, h⟩
    exact ⟨extendModel initial m, fun S retained =>
      (extension_preserves_attainable initial m retained.1).symm ▸ h S retained⟩

def NRO {M Score : Type} [LE Score] [LT Score] (attainable : M → Scope V → Score → Prop)
    (valid : Scope V → Prop) (S : Scope V) : Prop :=
  valid S ∧ ∃ m, ∀ T, valid T → ProperSubscope T S → Beats (attainable m S) (attainable m T)

def POMPS {M Score : Type} [LE Score] [LT Score] (attainable : M → Scope V → Score → Prop)
    (valid : Scope V → Prop) (S : Scope V) : Prop :=
  NRO attainable valid S ∧ ∃ m, ∀ T, NRO attainable valid T → T ≠ S →
    Beats (attainable m S) (attainable m T)

/-- Every original NRO scope belongs to the retained feasible set. Removing
an observation of a deleted vertex gives a proper valid subscope with the
same attainable rewards in the very model proposed as the NRO witness. -/
theorem original_nro_is_retained {P : Problem V} {Noise Seed Value : V → Type} {Score : Type}
    {admissible : (RewardTrace Noise Seed Value P.reward → Score) → Prop}
    [LE Score] [LT Score] [Std.LawfulOrderLT Score] (initial : Assignment Value) {S : Scope V}
    (nro : NRO (fun m : Model P.edge Noise Seed Value P.reward Score admissible => Attainable P initial m)
      P.valid S) : P.retained S := by
  obtain ⟨valid, m, wins⟩ := nro
  refine ⟨valid, ?_⟩
  intro d a observes hd
  have better := wins (removeObservation S d a) (removing_observation_preserves_validity valid d a)
    (removed_observation_proper observes)
  change Beats (Attainable P initial m S) (Attainable P initial m (removeObservation S d a)) at better
  rw [← dropping_deleted_observation_attainable initial m valid hd observes] at better
  exact never_beats_itself _ better

/-- Proposition 5's NRO equality, using the original validity test in the
retained set and one common reward witness for all proper subscopes. -/
theorem nro_original_iff_induced {P : Problem V} {Noise Seed Value : V → Type} {Score : Type}
    (admissible : (RewardTrace Noise Seed Value P.reward → Score) → Prop)
    [LE Score] [LT Score] [Std.LawfulOrderLT Score] (initial : Assignment Value) (S : Scope V) :
    NRO (fun m : Model P.edge Noise Seed Value P.reward Score admissible => Attainable P initial m)
      P.valid S ↔
    NRO (fun m : Model P.induced Noise Seed Value P.reward Score admissible => Attainable P initial m)
      P.retained S := by
  constructor
  · intro nro
    have retained := original_nro_is_retained initial nro
    obtain ⟨valid, m, wins⟩ := nro
    refine ⟨retained, restrictModel initial m, ?_⟩
    intro T smaller proper
    change Beats (Attainable P initial (restrictModel initial m) S)
      (Attainable P initial (restrictModel initial m) T)
    rw [← restriction_preserves_attainable initial m valid,
      ← restriction_preserves_attainable initial m smaller.1]
    exact wins T smaller.1 proper
  · rintro ⟨retained, m, wins⟩
    refine ⟨retained.1, extendModel initial m, ?_⟩
    intro T valid proper
    change Beats (Attainable P initial (extendModel initial m) S)
      (Attainable P initial (extendModel initial m) T)
    rw [extension_preserves_attainable initial m retained.1,
      extension_preserves_attainable initial m valid]
    exact wins T (retained_proper_subscope retained valid proper.1) proper

/-- Proposition 5's POMPS equality. The model transport is simultaneous
across all NRO competitors, so the strict comparisons use one model. -/
theorem pomps_original_iff_induced {P : Problem V} {Noise Seed Value : V → Type} {Score : Type}
    (admissible : (RewardTrace Noise Seed Value P.reward → Score) → Prop)
    [LE Score] [LT Score] [Std.LawfulOrderLT Score] (initial : Assignment Value) (S : Scope V) :
    POMPS (fun m : Model P.edge Noise Seed Value P.reward Score admissible => Attainable P initial m)
      P.valid S ↔
    POMPS (fun m : Model P.induced Noise Seed Value P.reward Score admissible => Attainable P initial m)
      P.retained S := by
  have nro_iff (T : Scope V) :=
    nro_original_iff_induced admissible initial T
  constructor
  · rintro ⟨nro, m, wins⟩
    refine ⟨(nro_iff S).mp nro, restrictModel initial m, ?_⟩
    intro T candidate different
    change Beats (Attainable P initial (restrictModel initial m) S)
      (Attainable P initial (restrictModel initial m) T)
    rw [← restriction_preserves_attainable initial m nro.1,
      ← restriction_preserves_attainable initial m candidate.1.1]
    exact wins T ((nro_iff T).mpr candidate) different
  · rintro ⟨nro, m, wins⟩
    refine ⟨(nro_iff S).mpr nro, extendModel initial m, ?_⟩
    intro T candidate different
    change Beats (Attainable P initial (extendModel initial m) S)
      (Attainable P initial (extendModel initial m) T)
    rw [extension_preserves_attainable initial m nro.1.1,
      extension_preserves_attainable initial m candidate.1]
    exact wins T ((nro_iff T).mp candidate) different

end

end OpenCausalScience.Papers.LeeBareinboim2020.ScopeReduction
