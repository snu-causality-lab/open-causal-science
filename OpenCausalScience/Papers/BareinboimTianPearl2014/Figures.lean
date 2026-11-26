module
public import OpenCausalScience.Papers.BareinboimTianPearl2014.ConditionalRecovery
public import OpenCausalScience.Papers.BareinboimTianPearl2014.SelectionCriterion

/-! # Recovery examples from Figures 1 and 2

Bareinboim, Tian and Pearl (2014), Figure 1 and Lemma 1, and
Figure 2 and Theorems 2–3.

Source: https://ftp.cs.ucla.edu/pub/stat_ser/r425.pdf
-/

namespace OpenCausalScience.Papers.BareinboimTianPearl2014.Figures

open SelectionCriterion
open OpenCausalScience.Moralization.Query

@[expose] public section

def only {n : Nat} (v : Fin n) : Fin n → Bool := (· == v)
def members {n : Nat} (vs : List (Fin n)) : Fin n → Bool := vs.contains

/-- Topological indices X, Y, S. Panel (a) has both causes of selection,
panel (c) has X alone, and panel (d) has Y alone. -/
def smallFigure (fromX fromY : Bool) : DAG 3 where
  edge u v := (u == 0 && v == 1) ||
      (fromX && u == 0 && v == 2) || (fromY && u == 1 && v == 2)
  rank v := v.val
  edge_increases := by
    revert fromX fromY
    decide

/-- Topological indices Z, W, X, Y, S. When W is absent,
its vertex is isolated and the graph is panel (e). -/
def treatmentSelected (withW : Bool) : DAG 5 where
  edge u v := ([(0, 2), (0, 4), (2, 3), (2, 4)] : List (Fin 5 × Fin 5)).contains (u, v) ||
    (withW && (u == 1 && (v == 2 || v == 3)))
  rank v := v.val
  edge_increases := by
    intro u v
    revert u v
    cases withW <;> decide

def fullMoralEdge {n : Nat} (G : DAG n) (u v : Fin n) : Bool :=
  G.edge u v || (G.edge v u || (List.finRange n).any (fun c => G.edge u c && G.edge v c))

private theorem full_moral_of_query_moral {n : Nat} {G : DAG n}
    {Q : OpenCausalScience.Moralization.Query G} {u v : Fin n}
    (edge : Q.MoralEdge u v) : fullMoralEdge G u v = true := by
  unfold fullMoralEdge
  rcases edge.connection with forward | backward | ⟨c, _, fst, snd⟩
  · simp [forward]
  · simp [backward]
  · exact Bool.or_eq_true_iff.mpr (.inr (Bool.or_eq_true_iff.mpr (.inr
      (List.any_eq_true.mpr ⟨c, List.mem_finRange c, Bool.and_eq_true_iff.mpr ⟨fst, snd⟩⟩))))

private theorem stays_in_cut {n : Nat} {G : DAG n}
    {Q : OpenCausalScience.Moralization.Query G} (side : Fin n → Bool)
    (closed : ∀ u v, side u = true → Q.condition.member u = false → Q.condition.member v = false →
      fullMoralEdge G u v = true → side v = true)
    {u v : Fin n} (walk : Q.MoralWalk u v) (initial : side u = true) : side v = true := by
  induction walk with
  | nil => exact initial
  | cons edge _ ih =>
    exact ih (closed _ _ initial edge.sourceOutside edge.targetOutside
      (full_moral_of_query_moral edge))

private theorem separated_by_cut {n : Nat} {G : DAG n}
    (Y S X side : Fin n → Bool)
    (outcomeOutside : ∀ v, Y v = true → X v = false)
    (selectionOutside : ∀ v, S v = true → X v = false)
    (outcomeSide : ∀ v, Y v = true → side v = true)
    (selectionSide : ∀ v, S v = true → side v = false)
    (closed : ∀ u v, side u = true → X u = false → X v = false →
      fullMoralEdge G u v = true → side v = true) :
    (dagQuery G Y S X).dagMoralSeparated = true := by
  apply ((dagQuery G Y S X).dagMoralSeparated_eq_true_iff outcomeOutside selectionOutside).mpr
  apply ((dagQuery G Y S X).dSeparation_iff_no_moralConnection outcomeOutside selectionOutside).mpr
  rintro ⟨y, s, yHere, sHere, walk⟩
  have right := stays_in_cut side closed walk (outcomeSide _ yHere)
  rw [selectionSide _ sHere] at right
  contradiction

private theorem connected_by_walk {n : Nat} {G : DAG n}
    (Y S X : Fin n → Bool)
    (outcomeOutside : ∀ v, Y v = true → X v = false)
    (selectionOutside : ∀ v, S v = true → X v = false)
    (walk : (dagQuery G Y S X).MoralConnection) :
    (dagQuery G Y S X).dagMoralSeparated = false := by
  apply Bool.eq_false_iff.mpr
  intro separated
  exact ((dagQuery G Y S X).dSeparation_iff_no_moralConnection outcomeOutside selectionOutside).mp
    (((dagQuery G Y S X).dagMoralSeparated_eq_true_iff outcomeOutside selectionOutside).mp separated)
    walk

private theorem outcome_relevant {n : Nat} {G : DAG n}
    {Q : OpenCausalScience.Moralization.Query G} {v : Fin n}
    (onLeft : Q.left v = true) : Q.relevant v :=
  (Q.relevant_iff v).mpr ⟨v, .inl onLeft, .inl rfl⟩

private theorem selection_relevant {n : Nat} {G : DAG n}
    {Q : OpenCausalScience.Moralization.Query G} {v : Fin n}
    (onRight : Q.right v = true) : Q.relevant v :=
  (Q.relevant_iff v).mpr ⟨v, .inr (.inl onRight), .inl rfl⟩

private theorem given_relevant {n : Nat} {G : DAG n}
    {Q : OpenCausalScience.Moralization.Query G} {v : Fin n}
    (fixed : Q.condition.member v = true) : Q.relevant v :=
  (Q.relevant_iff v).mpr ⟨v, .inr (.inr fixed), .inl rfl⟩

private theorem relevant_parent {n : Nat} {G : DAG n}
    {Q : OpenCausalScience.Moralization.Query G} {u v : Fin n}
    (arrow : G.edge u v = true) (child : Q.relevant v) : Q.relevant u := by
  obtain ⟨w, seed, path⟩ := (Q.relevant_iff v).mp child
  refine (Q.relevant_iff u).mpr ⟨w, seed, Or.inr ?_⟩
  rcases path with rfl | path
  · exact .single arrow
  clear seed
  induction path with
  | single last => exact .extend (.single arrow) last
  | extend _ last ih => exact .extend ih last

theorem figure1_conditional_tests :
    (dagQuery (smallFigure true true) (only 1) (only 2) (only 0)).dagMoralSeparated = false ∧
    (dagQuery (smallFigure true false) (only 1) (only 2) (only 0)).dagMoralSeparated = true ∧
    (dagQuery (smallFigure false true) (only 1) (only 2) (only 0)).dagMoralSeparated = false ∧
    (dagQuery (treatmentSelected false) (only 3) (only 4) (only 2)).dagMoralSeparated = true ∧
    (dagQuery (treatmentSelected true) (only 3) (only 4) (only 2)).dagMoralSeparated = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply connected_by_walk _ _ _ (by decide) (by decide)
    exact ⟨1, 2, rfl, rfl,
      .cons ⟨outcome_relevant rfl, selection_relevant rfl, rfl, rfl, by decide, .inl rfl⟩ (.nil _)⟩
  · exact separated_by_cut _ _ _ (only 1) (by decide) (by decide) (by decide) (by decide) (by decide)
  · apply connected_by_walk _ _ _ (by decide) (by decide)
    exact ⟨1, 2, rfl, rfl,
      .cons ⟨outcome_relevant rfl, selection_relevant rfl, rfl, rfl, by decide, .inl rfl⟩ (.nil _)⟩
  · exact separated_by_cut _ _ _ (only 3) (by decide) (by decide) (by decide) (by decide) (by decide)
  · apply connected_by_walk _ _ _ (by decide) (by decide)
    let Q := dagQuery (treatmentSelected true) (only 3) (only 4) (only 2)
    have hy : Q.relevant 3 := outcome_relevant rfl
    have hs : Q.relevant 4 := selection_relevant rfl
    have hw : Q.relevant 1 := relevant_parent rfl hy
    have hz : Q.relevant 0 := relevant_parent rfl hs
    have hx : Q.relevant 2 := given_relevant rfl
    have yw : Q.MoralEdge 3 1 := ⟨hy, hw, rfl, rfl, by decide, .inr (.inl rfl)⟩
    have wz : Q.MoralEdge 1 0 := ⟨hw, hz, rfl, rfl, by decide, .inr (.inr ⟨2, hx, rfl, rfl⟩)⟩
    have zs : Q.MoralEdge 0 4 := ⟨hz, hs, rfl, rfl, by decide, .inl rfl⟩
    exact ⟨3, 4, rfl, rfl, .cons yw (.cons wz (.cons zs (.nil _)))⟩

section OutcomeDependent

/-- A positive binary DAG factorization on X → Y → S. The Boolean
functions give the conditional probabilities of the positive value. -/
structure ChainLaw where
  x : Rat
  y : Bool → Rat
  s : Bool → Rat

def bern (p : Rat) (bit : Bool) : Rat := if bit then p else 1 - p

def ChainLaw.cell (m : ChainLaw) (x y s : Bool) : Rat :=
  bern m.x x * bern (m.y x) y * bern (m.s y) s

def ChainLaw.selectionMass (m : ChainLaw) : Rat :=
  m.cell false false true + m.cell false true true +
    m.cell true false true + m.cell true true true

def ChainLaw.selectedCell (m : ChainLaw) (x y : Bool) : Rat :=
  m.cell x y true / m.selectionMass

def ChainLaw.populationOutcomeProbability (m : ChainLaw) (x : Bool) : Rat :=
  (m.cell x true false + m.cell x true true) /
    (m.cell x false false + m.cell x false true + m.cell x true false + m.cell x true true)

def biasedSelection : ChainLaw :=
  ⟨1 / 2, fun _ => 1 / 2, fun y => if y then 3 / 4 else 1 / 4⟩

def independentSelection : ChainLaw :=
  ⟨1 / 2, fun _ => 3 / 4, fun _ => 1 / 2⟩

/-- Figure 1(d), Lemma 1. The full positively selected (X,Y) table is
identical in both compatible models, yet population P(Y=1 | X=x)
differs at either treatment value. -/
theorem outcome_dependent_selection_nonrecovery :
    (∀ x y s : Bool, 0 < biasedSelection.cell x y s ∧ 0 < independentSelection.cell x y s) ∧
    (∀ x y : Bool, biasedSelection.selectedCell x y = independentSelection.selectedCell x y) ∧
    (∀ x : Bool, biasedSelection.populationOutcomeProbability x = 1 / 2 ∧
      independentSelection.populationOutcomeProbability x = 3 / 4) := by
  decide +kernel

end OutcomeDependent

/-- Topological indices Z1, Z2, W1, W2, Z3, T1, X, W3, Y, S. -/
def externalDataFigure : DAG 10 where
  edge u v := ([(0, 2), (0, 4), (1, 4), (1, 3), (2, 5), (2, 9),
    (5, 6), (4, 6), (4, 8), (6, 7), (7, 8), (3, 8), (3, 9)] :
    List (Fin 10 × Fin 10)).contains (u, v)
  rank v := v.val
  edge_increases := by decide

theorem figure2_external_covariates :
    (dagQuery externalDataFigure (only 8) (only 9) (only 6)).dagMoralSeparated = false ∧
    (dagQuery externalDataFigure (only 8) (only 9) (members [6, 2, 3])).dagMoralSeparated = true ∧
    (dagQuery externalDataFigure (only 8) (only 9) (members [6, 3, 4])).dagMoralSeparated = true ∧
    (dagQuery externalDataFigure (only 8) (only 9) (members [6, 3, 0, 1])).dagMoralSeparated = false := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply connected_by_walk _ _ _ (by decide) (by decide)
    let Q := dagQuery externalDataFigure (only 8) (only 9) (only 6)
    have hy : Q.relevant 8 := outcome_relevant rfl
    have hs : Q.relevant 9 := selection_relevant rfl
    have hw : Q.relevant 3 := relevant_parent rfl hy
    have yw : Q.MoralEdge 8 3 := ⟨hy, hw, rfl, rfl, by decide, .inr (.inl rfl)⟩
    have ws : Q.MoralEdge 3 9 := ⟨hw, hs, rfl, rfl, by decide, .inl rfl⟩
    exact ⟨8, 9, rfl, rfl, .cons yw (.cons ws (.nil _))⟩
  · exact separated_by_cut _ _ _ (fun u => u != 9) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  · exact separated_by_cut _ _ _ (fun u => u == 7 || u == 8) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  · apply connected_by_walk _ _ _ (by decide) (by decide)
    let Q := dagQuery externalDataFigure (only 8) (only 9) (members [6, 3, 0, 1])
    have hy : Q.relevant 8 := outcome_relevant rfl
    have hs : Q.relevant 9 := selection_relevant rfl
    have hx : Q.relevant 6 := given_relevant rfl
    have hz : Q.relevant 4 := relevant_parent rfl hy
    have ht : Q.relevant 5 := relevant_parent rfl hx
    have hw : Q.relevant 2 := relevant_parent rfl hs
    have yz : Q.MoralEdge 8 4 := ⟨hy, hz, rfl, rfl, by decide, .inr (.inl rfl)⟩
    have zt : Q.MoralEdge 4 5 := ⟨hz, ht, rfl, rfl, by decide, .inr (.inr ⟨6, hx, rfl, rfl⟩)⟩
    have tw : Q.MoralEdge 5 2 := ⟨ht, hw, rfl, rfl, by decide, .inr (.inl rfl)⟩
    have ws : Q.MoralEdge 2 9 := ⟨hw, hs, rfl, rfl, by decide, .inl rfl⟩
    exact ⟨8, 9, rfl, rfl, .cons yz (.cons zt (.cons tw (.cons ws (.nil _))))⟩

theorem figure2_single_ancestral_test_with_common_measurements :
    (dagQuery externalDataFigure (only 8) (only 9)
      (add (only 6) (candidate externalDataFigure (only 8) (only 9) (only 6)
        (members [6, 3, 4])))).dagMoralSeparated = true := by
  apply (exists_external_separator_iff _ _ _ _ _ (by decide) (by decide)).mp
  refine ⟨members [3, 4], by unfold validAdditional; decide, ?_⟩
  have same : add (only (6 : Fin 10)) (members [3, 4]) = members [6, 3, 4] := by
    funext v
    revert v
    decide
  rw [same]
  exact ((dagQuery externalDataFigure (only 8) (only 9)
    (members [6, 3, 4])).dagMoralSeparated_eq_true_iff (by decide) (by decide)).mp
      figure2_external_covariates.2.2.1

end
end OpenCausalScience.Papers.BareinboimTianPearl2014.Figures
