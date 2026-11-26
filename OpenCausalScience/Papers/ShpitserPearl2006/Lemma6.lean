module
public import OpenCausalScience.Papers.TianPearl2003.AncestralMarginal

/-! # Extra interventions on nonancestors

Shpitser and Pearl (2006), Lemma 6 and line 3 of ID. Compute ancestors
after applying the original action. Clamping every remaining nonancestor
at an arbitrary value leaves the outcome unchanged on each unit.
Source: https://cdn.aaai.org/AAAI/2006/AAAI06-191.pdf#page=6
-/

namespace OpenCausalScience.Papers.ShpitserPearl2006.Lemma6

open TianPearl2003.AncestralMarginal

@[expose] public section

variable {n : Nat} {Ω : Type}

/-- The ancestor relation in the intervention graph, with arrows into
originally clamped vertices deleted. -/
inductive Ancestor (G : DAG n) (fixed : Setting n) (outcome : Fin n → Bool) : Fin n → Prop
  | outcome {v} : outcome v = true → Ancestor G fixed outcome v
  | parent {u v} : G.edge u v = true → fixed v = none →
      Ancestor G fixed outcome v → Ancestor G fixed outcome u

open Classical in
noncomputable def retainAncestors (G : DAG n) (fixed : Setting n) (outcome : Fin n → Bool)
    (v : Fin n) : Bool :=
  if fixed v = none ∧ Ancestor G fixed outcome v then true else false

theorem retain_ancestors_iff {G : DAG n} {fixed : Setting n}
    {outcome : Fin n → Bool} {v : Fin n} :
    retainAncestors G fixed outcome v = true ↔ fixed v = none ∧ Ancestor G fixed outcome v := by
  simp [retainAncestors]

/-- Existing actions keep their original values. The remaining actions
are exactly the still-free nonancestors. -/
noncomputable def extraActions (G : DAG n) (fixed : Setting n)
    (outcome values : Fin n → Bool) : Setting n :=
  addClamps (retainAncestors G fixed outcome) values fixed

private theorem ancestral_among_free (G : DAG n) (fixed : Setting n) (outcome : Fin n → Bool) :
    ancestralAmongFree G (retainAncestors G fixed outcome) fixed := by
  intro u v edge ancestor
  obtain ⟨free, reached⟩ := retain_ancestors_iff.mp ancestor
  by_cases unclamped : fixed u = none
  · exact .inl (retain_ancestors_iff.mpr ⟨unclamped, .parent edge free reached⟩)
  · exact .inr unclamped

theorem original_action_preserved (G : DAG n) (fixed : Setting n)
    (outcome values : Fin n → Bool) (v : Fin n) {value : Bool} (clamped : fixed v = some value) :
    extraActions G fixed outcome values v = some value := by
  simp [extraActions, addClamps, clamped]

theorem extra_actions_on_free_vertices (G : DAG n) (fixed : Setting n)
    (outcome values : Fin n → Bool) (v : Fin n) (free : fixed v = none) :
    extraActions G fixed outcome values v = some (values v) ↔
      ¬ Ancestor G fixed outcome v := by
  classical
  simp [extraActions, addClamps, retainAncestors, free]

theorem nonancestor_actions_preserve_response (G : DAG n)
    (mechanism : Ω → Fin n → (Fin n → Bool) → Bool) (unit : Ω)
    (fixed : Setting n) (outcome values : Fin n → Bool)
    (v : Fin n) (inOutcome : outcome v = true) (free : fixed v = none) :
    evaluate G mechanism unit fixed v =
      evaluate G mechanism unit (extraActions G fixed outcome values) v :=
  retained_evaluation_unchanged G mechanism unit _ values fixed
    (ancestral_among_free G fixed outcome) v (retain_ancestors_iff.mpr ⟨free, .outcome inOutcome⟩)

theorem nonancestor_actions_preserve_mass (G : DAG n)
    (mechanism : Ω → Fin n → (Fin n → Bool) → Bool) (atoms : List Ω) (weight : Ω → Rat)
    (fixed : Setting n) (outcome values : Fin n → Bool)
    (disjoint : ∀ v, outcome v = true → fixed v = none) (event : (Fin n → Bool) → Bool)
    (reads : readsOnly event outcome) :
    mass atoms weight (fun unit => event (evaluate G mechanism unit fixed)) =
      mass atoms weight (fun unit =>
        event (evaluate G mechanism unit (extraActions G fixed outcome values))) := by
  apply retained_mass_unchanged G mechanism atoms weight _ values fixed
    (ancestral_among_free G fixed outcome) event
  intro first second same
  exact reads first second fun v inOutcome =>
    same v (retain_ancestors_iff.mpr ⟨disjoint v inOutcome, .outcome inOutcome⟩)

theorem nonancestor_marginal_equals_extra_action {A : Type} [DecidableEq A] (G : DAG n)
    (mechanism : Ω → Fin n → (Fin n → Bool) → Bool) (atoms : List Ω) (weight : Ω → Rat)
    (fixed : Setting n) (outcome values : Fin n → Bool)
    (disjoint : ∀ v, outcome v = true → fixed v = none) (event : (Fin n → Bool) → Bool)
    (reads : readsOnly event outcome) (cell : (Fin n → Bool) → A) (cells : List A)
    (unique : cells.Nodup) (exhaustive : ∀ unit ∈ atoms, cell (evaluate G mechanism unit fixed) ∈ cells) :
    (cells.map fun a => mass atoms weight (fun unit =>
      event (evaluate G mechanism unit fixed) &&
        decide (cell (evaluate G mechanism unit fixed) = a))).sum =
      mass atoms weight (fun unit =>
        event (evaluate G mechanism unit (extraActions G fixed outcome values))) := by
  rw [sum_masses_of_partition cells unique atoms weight _ exhaustive]
  exact nonancestor_actions_preserve_mass G mechanism atoms weight fixed outcome values disjoint
    event reads

end
end OpenCausalScience.Papers.ShpitserPearl2006.Lemma6
