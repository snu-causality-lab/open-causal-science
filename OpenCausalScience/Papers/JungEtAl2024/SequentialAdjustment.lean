module
public import OpenCausalScience.Graph.DSeparation

/-!
# Jung, Park, and Lee (2024), the forbidden-set correction

The 2026-10-25 corrected version, Section 4, p. 7, compares the published
Definition 7 with the new Equation (11) on `X₁ → Z → X₂ → Y`.
The proof below checks the two graph predicates and the adjustment formula
for finite rational kernels on that chain. The last two examples check the
published pruning failures described on p. 10 of the corrected version.

Sources:
* https://proceedings.neurips.cc/paper_files/paper/2024/file/233ff375b9795cd890f78a1f64459b8d-Paper-Conference.pdf
* https://www.sanghacklee.me/ai-corrected/SAC_AI_corrected_2026-10-25.pdf
-/

namespace OpenCausalScience.Papers.JungEtAl2024.SequentialAdjustment

@[expose] public section

variable {n : Nat}

/-- Intervention in a DAG removes arrows into the specified treatments. -/
def intervene (graph : DAG n) (treatments : List (Fin n)) : DAG n where
  edge u v := graph.edge u v && !(treatments.contains v)
  rank := graph.rank
  edge_increases u v h := graph.edge_increases u v (Bool.and_eq_true_iff.mp h).1

private theorem walk_of_intervened (graph : DAG n) (treatments : List (Fin n))
    {u v : Fin n} (walk : (intervene graph treatments).DirectedWalk u v) :
    graph.DirectedWalk u v := by
  induction walk with
  | single edge => exact .single (Bool.and_eq_true_iff.mp edge).1
  | extend _ edge shorter => exact .extend shorter (Bool.and_eq_true_iff.mp edge).1

/-- Equation (11)'s forbidden membership for a singleton treatment and target
in a DAG. The first walk excludes the treatment itself, and the other
reachability tests include their endpoints. -/
def forbiddenDescendant (graph : DAG n) (treatment target covariate : Fin n) : Prop :=
  ∃ vertex, graph.DirectedWalk treatment vertex ∧
    (vertex = target ∨ graph.DirectedWalk vertex target) ∧
    (vertex = covariate ∨ graph.DirectedWalk vertex covariate)

theorem forbidden_descendant_of_intervened (graph : DAG n) (future : List (Fin n))
    {treatment target covariate : Fin n}
    (h : forbiddenDescendant (intervene graph future) treatment target covariate) :
    forbiddenDescendant graph treatment target covariate := by
  obtain ⟨vertex, reach, towardTarget, towardCovariate⟩ := h
  exact ⟨vertex, walk_of_intervened graph future reach,
    towardTarget.elim Or.inl (fun walk => Or.inr (walk_of_intervened graph future walk)),
    towardCovariate.elim Or.inl (fun walk => Or.inr (walk_of_intervened graph future walk))⟩

theorem rank_lt_of_forbidden_descendant (graph : DAG n) {treatment target covariate : Fin n}
    (h : forbiddenDescendant graph treatment target covariate) :
    graph.rank treatment < graph.rank covariate := by
  obtain ⟨vertex, reach, _, towardCovariate⟩ := h
  have hRank := graph.rank_lt_of_directedWalk reach
  rcases towardCovariate with equal | suffix
  · exact equal ▸ hRank
  · exact Nat.lt_trans hRank (graph.rank_lt_of_directedWalk suffix)

/-- For a singleton treatment, an outgoing arrow begins a proper causal
path exactly when its other endpoint is an ancestor of the target. -/
def properBackdoor (graph : DAG n) (treatment target : Fin n) : DAG n where
  edge u v := graph.edge u v &&
    !(u == treatment && (graph.conditioningAncestors [target]).contains v)
  rank := graph.rank
  edge_increases u v h := graph.edge_increases u v (Bool.and_eq_true_iff.mp h).1

/-- A singleton-treatment, singleton-target instance of Equations (10) and
(11). The published and corrected predicates take the same separation graph. -/
def satisfiesStage (separationGraph forbiddenGraph : DAG n) (treatment target : Fin n)
    (history adjustment : List (Fin n)) : Prop :=
  separationGraph.dSeparated treatment target (history ++ adjustment) = some true ∧
    ∀ covariate ∈ adjustment, ¬ forbiddenDescendant forbiddenGraph treatment target covariate

def x1 : Fin 4 := 0
def z : Fin 4 := 1
def x2 : Fin 4 := 2
def y : Fin 4 := 3

def chain : DAG 4 where
  edge u v := (u == x1 && v == z) || (u == z && v == x2) || (u == x2 && v == y)
  rank v := v.val
  edge_increases := by decide

def firstStage : DAG 4 := intervene chain [x2]

/-- The first block contains a nondescendant of the later treatment even in
the original chain. The second block is empty. -/
theorem first_block_nondescendant : ¬ chain.DirectedWalk x2 z := by
  intro walk
  exact (by decide : ¬ chain.rank x2 < chain.rank z) (chain.rank_lt_of_directedWalk walk)

theorem z_forbidden_in_original : forbiddenDescendant chain x1 y z := by
  refine ⟨z, .single (by decide), Or.inr ?_, Or.inl rfl⟩
  exact .extend (.single (v := x2) (by decide)) (by decide)

private theorem walk_preserves {graph : DAG n} {p : Fin n → Prop}
    (closed : ∀ u v, graph.edge u v = true → p u → p v)
    {u v : Fin n} (walk : graph.DirectedWalk u v) (start : p u) : p v := by
  induction walk with
  | single edge => exact closed _ _ edge start
  | extend _ edge ih => exact closed _ _ edge ih

theorem no_first_stage_walk : ¬ firstStage.DirectedWalk x1 y := by
  intro walk
  let inFirstComponent : Fin 4 → Prop := fun v => v = x1 ∨ v = z
  have closed : ∀ u v, firstStage.edge u v = true → inFirstComponent u →
      inFirstComponent v := by
    change ∀ u v, firstStage.edge u v = true → (u = x1 ∨ u = z) → (v = x1 ∨ v = z)
    decide
  have finish : inFirstComponent y := walk_preserves closed walk (Or.inl rfl)
  exact (by decide : ¬ (y = x1 ∨ y = z)) finish

private theorem walk_trans {graph : DAG n} {u v w : Fin n}
    (left : graph.DirectedWalk u v) (right : graph.DirectedWalk v w) :
    graph.DirectedWalk u w := by
  induction right with
  | single edge => exact .extend left edge
  | extend _ edge ih => exact .extend ih edge

theorem first_stage_forbidden_empty (covariate : Fin 4) :
    ¬ forbiddenDescendant firstStage x1 y covariate := by
  rintro ⟨vertex, reach, towardTarget, _⟩
  rcases towardTarget with equal | suffix
  · exact no_first_stage_walk (equal ▸ reach)
  · exact no_first_stage_walk (walk_trans reach suffix)

theorem published_stage_rejects :
    ¬ satisfiesStage (properBackdoor firstStage x1 y) chain x1 y [] [z] := by
  intro passes
  exact passes.2 z (by simp) z_forbidden_in_original

theorem corrected_stages_accept :
    satisfiesStage (properBackdoor firstStage x1 y) firstStage x1 y [] [z] ∧
    satisfiesStage (properBackdoor chain x2 y) chain x2 y [x1, z] [] := by
  constructor
  · exact ⟨by decide, fun covariate _ => first_stage_forbidden_empty covariate⟩
  · exact ⟨by decide, by simp⟩

private theorem sum_mul {α : Type} (values : List α) (p : α → Rat) (c : Rat) :
    (values.map fun v => p v * c).sum = (values.map p).sum * c := by
  induction values with
  | nil => simp
  | cons v values ih => simp [ih, Rat.add_mul]

/-- In the chain, the factors for a fixed observation `(x₁,z,x₂)` are
collected in `alignedMass z`. Positive observations give nonzero mass.
`pZ` is the observed marginal and `pZGivenX1` is the kernel left under
the joint intervention. The outcome kernel depends only on `x₂`. -/
theorem chain_adjustment_formula {Z Y : Type}
    (zs : List Z) (ys : List Y) (pZ pZGivenX1 alignedMass : Z → Rat)
    (pYGivenX2 : Y → Rat) (outcome : Y)
    (observedNorm : (zs.map pZ).sum = 1)
    (intervenedNorm : (zs.map pZGivenX1).sum = 1)
    (outcomeNorm : (ys.map pYGivenX2).sum = 1)
    (observedNonzero : ∀ value ∈ zs, alignedMass value ≠ 0) :
    (zs.map fun value => pZ value *
        (alignedMass value * pYGivenX2 outcome /
          (ys.map fun possible => alignedMass value * pYGivenX2 possible).sum)).sum =
      (zs.map fun value => pZGivenX1 value * pYGivenX2 outcome).sum := by
  have ratio (value : Z) (member : value ∈ zs) :
      alignedMass value * pYGivenX2 outcome /
        (ys.map fun possible => alignedMass value * pYGivenX2 possible).sum = pYGivenX2 outcome := by
    have denominator :
        (ys.map fun possible => alignedMass value * pYGivenX2 possible).sum = alignedMass value := by
      simpa [Rat.mul_comm, outcomeNorm] using sum_mul ys pYGivenX2 (alignedMass value)
    rw [denominator, Rat.mul_comm, Rat.mul_div_cancel (observedNonzero value member)]
  calc
    _ = (zs.map fun value => pZ value * pYGivenX2 outcome).sum :=
      congrArg List.sum (List.map_congr_left (fun value member => by rw [ratio value member]))
    _ = _ := by rw [sum_mul, sum_mul, observedNorm, intervenedNorm]

/-- In this second four-node graph the vertex formerly called `z` is `C`.
The first-stage intervention isolates `X₁`. In the second-stage proper
back-door graph, `X₂ ← C → Y` still has to be blocked. -/
def pruningGraph : DAG 4 where
  edge u v := (u == x1 && v == x2) || (u == z && v == x2) ||
    (u == z && v == y) || (u == x2 && v == y)
  rank v := v.val
  edge_increases := by decide

theorem stale_history_hides_open_fork :
    (properBackdoor pruningGraph x2 y).dSeparated x2 y [x1, z] = some true ∧
    (properBackdoor pruningGraph x2 y).dSeparated x2 y [x1] = some false := by decide

theorem moving_covariate_to_second_stage_passes :
    satisfiesStage (properBackdoor (intervene pruningGraph [x2]) x1 y)
      (intervene pruningGraph [x2]) x1 y [] [] ∧
    satisfiesStage (properBackdoor pruningGraph x2 y) pruningGraph x2 y [x1] [z] := by
  constructor
  · exact ⟨by decide, by simp⟩
  · refine ⟨by decide, ?_⟩
    intro covariate member forbidden
    have same : covariate = z := by simpa using member
    subst covariate
    exact (by decide : ¬ pruningGraph.rank x2 < pruningGraph.rank z)
      (rank_lt_of_forbidden_descendant pruningGraph forbidden)

namespace RequiredHistory

def a : Fin 5 := 0
def b : Fin 5 := 1
def c : Fin 5 := 2
def x : Fin 5 := 3
def y : Fin 5 := 4

def graph : DAG 5 where
  edge u v := (u == a && (v == x || v == c)) || (u == b && (v == c || v == y)) ||
    (u == x && v == y)
  rank v := v.val
  edge_increases := by decide

/-- The collider `C` is absent from the endpoint-only ancestral domain.
It belongs to the required history and makes `X ← A → C ← B → Y` active. -/
theorem endpoint_domain_omits_active_history :
    let backdoor := properBackdoor graph x y
    (backdoor.conditioningAncestors [x, y]).contains c = false ∧
    (backdoor.conditioningAncestors [x, y, c]).contains c = true ∧
    backdoor.dSeparated x y [] = some true ∧
    backdoor.dSeparated x y [c] = some false := by decide

end RequiredHistory

end

end OpenCausalScience.Papers.JungEtAl2024.SequentialAdjustment
