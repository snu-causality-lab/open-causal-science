module
public import OpenCausalScience.Graph.MixedSeparationExecutable
public import OpenCausalScience.Papers.TianPearl2003.IdentifyRecurrence

/-! # The two identification procedures on Figure 1(c)

Shpitser and Pearl (2006), Figure 1(c), Figure 3 and §6 Lemma 3.
The disputed query is `P_x(w | z)`. Tian's Figure 3 uses his §3
convention `Pa(S) = S ∪ ⋃_{v ∈ S} Pa(v)`. In Phase 3 this moves the
identifiable factor on Y into I₀, and the outcome W is then among
the arguments tested in Phase 4. The 2007 Appendum withdraws
the original unsoundness claim. We also check `P_x(y | z)` on the
same graph. For both queries, the IDC trace checks the Rule 2 test
and the joint ID branches that return the pair of induced subgraphs.

Sources:
https://ftp.cs.ucla.edu/pub/stat_ser/r329-uai.pdf
https://arxiv.org/pdf/1207.4161
https://ftp.cs.ucla.edu/pub/stat_ser/r329-appendum.pdf
https://ftp.cs.ucla.edu/pub/stat_ser/r327.pdf
-/

namespace OpenCausalScience.Papers.ShpitserPearl2006Conditional.Figure1C

open TianPearl2003.IdentifyRecurrence

@[expose] public section

abbrev x : Fin 4 := 0
abbrev w : Fin 4 := 1
abbrev y : Fin 4 := 2
abbrev z : Fin 4 := 3

def observed : Vertices 4 := [x, w, y, z]
def withoutX : Vertices 4 := [w, y, z]

/-- The directed edges are X → Z, W → Y and Y → Z, with X ↔ Z. -/
def markedEdge (u : Fin 4) (atU : Bool) (v : Fin 4) (atV : Bool) : Bool :=
  match u.val, v.val with
  | 0, 3 => atV
  | 3, 0 => atU
  | 1, 2 | 2, 3 => !atU && atV
  | 2, 1 | 3, 2 => atU && !atV
  | _, _ => false

def graph : MixedGraph 4 where
  edge := markedEdge
  symmetric := by decide +kernel
  loop_free := by decide +kernel
  no_arrow_of_undirected := by
    intro u v _ _ undirected
    have none : ∀ a b, markedEdge a false b false = false := by decide +kernel
    rw [none] at undirected
    contradiction

theorem directed_edges_increase :
    ∀ u v, graph.edge u false v true = true → u.val < v.val := by decide +kernel

def cComponents (current : Vertices 4) : List (Vertices 4) :=
  (current.map (district graph current)).eraseDups

def ancestralSet (outcome : Fin 4) : Vertices 4 :=
  ancestors graph withoutX [outcome, z]

/-- Tian's D and the c-components in the original and induced graphs. -/
theorem phase_one :
    ancestralSet w = withoutX ∧ ancestralSet y = withoutX ∧
      cComponents observed = [[x, z], [w], [y]] ∧
      cComponents withoutX = [[w], [y], [z]] := by decide +kernel

def factorPlan (current : Vertices 4) (root : Fin 4) : List (Instruction 4) :=
  identifyPlan graph (district graph current root) root (district graph observed root)

theorem phase_two :
    factorPlan withoutX w = [.marginalize [w] [w]] ∧
      factorPlan withoutX y = [.marginalize [y] [y]] ∧
      factorPlan withoutX z = [.ancestorFixedPoint [x, z]] := by
  unfold factorPlan
  rw [identifyPlan, identifyPlan, identifyPlan]
  decide +kernel

/-- The ancestor fixed point is the FAIL branch in Tian's Figure 1. -/
def failedDistricts (current : Vertices 4) : List (Vertices 4) :=
  ((current.filter fun root => (factorPlan current root).any fun
    | .ancestorFixedPoint _ => true
    | _ => false).map (district graph current)).eraseDups

def summationVertices (outcome : Fin 4) : Vertices 4 :=
  (ancestralSet outcome).filter fun v => v != outcome && v != z

/-- The arguments of a factor Q[S] include the members of S. -/
def pa (component : Vertices 4) : Vertices 4 :=
  observed.filter fun v => component.contains v || component.any (graph.edge v false · true)

theorem factor_arguments :
    pa [w] = [w] ∧ pa [y] = [w, y] ∧ pa [z] = [x, y, z] := by decide +kernel

def argumentUnion (components : List (Vertices 4)) : Vertices 4 :=
  observed.filter fun v => components.any fun component => (pa component).contains v

def initialF₀ (outcome : Fin 4) : Vertices 4 :=
  let failed := failedDistricts (ancestralSet outcome)
  (summationVertices outcome).filter (argumentUnion failed).contains

def firstI₀ (outcome : Fin 4) : List (Vertices 4) :=
  let current := ancestralSet outcome
  let failed := failedDistricts current
  (cComponents current).filter fun component =>
    !failed.contains component && (pa component).any (initialF₀ outcome).contains

def additionalSummationVertices (outcome : Fin 4) : Vertices 4 :=
  let f₀ := initialF₀ outcome
  (summationVertices outcome).filter fun v =>
    !f₀.contains v && (argumentUnion (firstI₀ outcome)).contains v

/-- Phase 4's test on the first pass through Phase 3. Both traces below
establish that no further pass is needed. -/
def phaseFourRejects (outcome : Fin 4) : Bool :=
  let failed := failedDistricts (ancestralSet outcome)
  (argumentUnion (failed ++ firstI₀ outcome)).contains outcome

/-- For Pₓ(w | z), Phase 3 moves the factor on Y and then stops because
B is empty. Its arguments bring W into the Phase 4 failure check. -/
theorem tian_w_fails :
    failedDistricts (ancestralSet w) = [[z]] ∧
      summationVertices w = [y] ∧ initialF₀ w = [y] ∧ firstI₀ w = [[y]] ∧
      additionalSummationVertices w = [] ∧ phaseFourRejects w = true := by
  have failed : failedDistricts (ancestralSet w) = [[z]] := by
    rw [phase_one.1]
    unfold failedDistricts
    change ((([w, y, z] : Vertices 4).filter _).map _).eraseDups = [[z]]
    simp only [List.filter_cons, List.filter_nil, phase_two.1, phase_two.2.1, phase_two.2.2]
    decide +kernel
  refine ⟨failed, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [phaseFourRejects, additionalSummationVertices, firstI₀, initialF₀, summationVertices, failed]
    decide +kernel

/-- For Pₓ(y | z), the only summation variable is W and F₀ is empty.
Y is already an argument of the failed factor on Z. -/
theorem tian_y_fails :
    failedDistricts (ancestralSet y) = [[z]] ∧
      summationVertices y = [w] ∧ initialF₀ y = [] ∧ firstI₀ y = [] ∧
      additionalSummationVertices y = [] ∧ phaseFourRejects y = true := by
  have failed : failedDistricts (ancestralSet y) = [[z]] := by
    rw [phase_one.2.1, ← phase_one.1]
    exact tian_w_fails.1
  refine ⟨failed, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [phaseFourRejects, additionalSummationVertices, firstI₀, initialF₀, summationVertices, failed]
    decide +kernel

def barEdge (intervened : Vertices 4)
    (u : Fin 4) (atU : Bool) (v : Fin 4) (atV : Bool) : Bool :=
  (!(intervened.contains u && atU) && !(intervened.contains v && atV)) &&
    graph.edge u atU v atV

/-- Delete arrowheads into intervened vertices. -/
def barred (intervened : Vertices 4) : MixedGraph 4 where
  edge := barEdge intervened
  symmetric := by
    intro u atU v atV
    unfold barEdge
    rw [graph.symmetric u atU v atV, Bool.and_comm (!(intervened.contains u && atU))]
  loop_free := by
    intro u atU atV
    simp [barEdge, graph.loop_free]
  no_arrow_of_undirected := by
    intro u v t mark undirected
    have original := (Bool.and_eq_true_iff.mp undirected).2
    simp [barEdge, graph.no_arrow_of_undirected (w := t) (mark := mark) original]

/-- Z has no outgoing directed edge, so barring X gives the Rule 2
graph for the candidate exchange of Z. -/
abbrev barX : MixedGraph 4 := barred [x]

theorem z_has_no_outgoing_edge : ∀ v, graph.edge z false v true = false := by decide +kernel

/-- IDC line 1 fails its separation test for Z for both outcomes.
W → Y → Z and Y → Z survive the graph cut with X conditioned on. -/
theorem idc_no_exchange :
    barX.mSeparated (· == w) (· == z) (· == x) = false ∧
      barX.mSeparated (· == y) (· == z) (· == x) = false := by
  constructor <;> apply Bool.eq_false_iff.mpr <;> intro separated
  · apply (barX.m_separated_iff_no_walk _ _ _).mp separated
    exact ⟨(y, true), (z, true), ⟨w, false, rfl, rfl⟩,
      .extend (.refl _) ⟨false, rfl, rfl⟩, rfl⟩
  · apply (barX.m_separated_iff_no_walk _ _ _).mp separated
    exact ⟨(z, true), (z, true), ⟨y, false, rfl, rfl⟩, .refl _, rfl⟩

def freeVertices (current intervened : Vertices 4) : Vertices 4 :=
  current.filter fun v => !intervened.contains v

/-- Conditions for passing ID lines 1–3 without an early return. -/
abbrev reachesDistrictCase (current target intervened : Vertices 4) : Prop :=
  intervened ≠ [] ∧ ancestors graph current target = current ∧
    (freeVertices current intervened).all
      (ancestors (barred intervened) current target).contains = true

/-- The failure branches of joint ID used here, from Figure 3 of R-327.
The returned pair lists the vertices of the two induced subgraphs. -/
inductive JointIDFailure : Vertices 4 → Vertices 4 → Vertices 4 →
    Vertices 4 → Vertices 4 → Prop
  | decompose {current target intervened component upper lower} :
      reachesDistrictCase current target intervened →
      1 < (cComponents (freeVertices current intervened)).length →
      component ∈ cComponents (freeVertices current intervened) →
      JointIDFailure current component (freeVertices current component) upper lower →
      JointIDFailure current target intervened upper lower
  | oneComponent {current target intervened component} :
      reachesDistrictCase current target intervened →
      cComponents (freeVertices current intervened) = [component] →
      cComponents current = [current] →
      JointIDFailure current target intervened current component
  | restrict {current target intervened component enclosing upper lower} :
      reachesDistrictCase current target intervened →
      cComponents (freeVertices current intervened) = [component] →
      cComponents current ≠ [current] →
      enclosing ∈ cComponents current →
      component.all enclosing.contains = true → sameVertices component enclosing = false →
      JointIDFailure enclosing target (enclosing.filter intervened.contains) upper lower →
      JointIDFailure current target intervened upper lower

/-- The factor on Z goes through joint ID line 7 and fails at line 5. -/
theorem id_z_fails :
    JointIDFailure observed [z] (freeVertices observed [z]) [x, z] [z] := by
  apply JointIDFailure.restrict (component := [z]) (enclosing := [x, z])
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply JointIDFailure.oneComponent <;> decide +kernel

/-- IDC's exact query in §6 passes to joint ID, whose line 4 propagates
the failure of the factor on Z. -/
theorem idc_w_fails :
    barX.mSeparated (· == w) (· == z) (· == x) = false ∧
      JointIDFailure observed [w, z] [x] [x, z] [z] := by
  refine ⟨idc_no_exchange.1, .decompose (component := [z]) ?_ ?_ ?_ id_z_fails⟩ <;> decide +kernel

theorem idc_y_fails :
    barX.mSeparated (· == y) (· == z) (· == x) = false ∧
      JointIDFailure observed [y, z] [x] [x, z] [z] := by
  refine ⟨idc_no_exchange.2, .decompose (component := [z]) ?_ ?_ ?_ id_z_fails⟩ <;> decide +kernel

end

end OpenCausalScience.Papers.ShpitserPearl2006Conditional.Figure1C
