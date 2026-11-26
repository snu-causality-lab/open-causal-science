module
public import OpenCausalScience.Papers.WangQinZhou2023.CircleUpdates

/-! Wang, Qin and Zhou (2023), Appendix B, Lemma 13, the case
of three original circles and two Step 2 directions.
Source: https://doi.org/10.1016/j.artint.2023.103964
-/

namespace OpenCausalScience.Papers.WangQinZhou2023.Step2CircleSafety

open LocalBackgroundKnowledge LocalTransformation CircleChordality CircleUpdates
open MixedGraph (Reach)
open Zhang2008OrientationRules.Orientations (Directed AncestralMarks)
open Zhang2008OrientationRules.UnshieldedPaths (unshielded_noncollider_invariant)

@[expose] public section

variable {n : Nat} {P Q : PMG n} {G : MarkedGraph n}
  {x : Fin n} {selected : Fin n → Prop}

private theorem directed_head {u v : Fin n} (edge : Directed G u v) :
    G.arrowheadAt v u = true := by
  change G.marks u v = some (false, true) at edge
  simp [MarkedGraph.arrowheadAt, G.swap_marks u v, edge, Prod.swap]

/-- In the active circle region, two Step 2 directions cannot have a
residual circle shortcut. The preceding MAG class supplies a noncollider
witness for the unshielded triple in the final contradiction. -/
theorem no_step2_chain_with_circle_shortcut
    (conditions : P.PossiblePathConditions) (agree : Agreement P G)
    (gMax : G.HasSeparators) (ancestral : AncestralMarks G) (noSelection : NoSelection G)
    (witness : PreviousTailWitnesses P G) (knowledge : LocalChoice P G x selected) :
    NoDirectedChainWithCircleShortcut P (ActiveDescendant P selected x) (InF P selected x) := by
  intro a b c ab bc ac
  have aActive := (step2_endpoints ab).1
  obtain ⟨_, cActive, bcCircle⟩ := step2_endpoints bc
  have comparable : Comparable P (ActiveDescendant P selected x) (InF P selected x) :=
    comparable_on_active_circles conditions agree gMax ancestral noSelection witness knowledge
  have acEqual := equal_on_residual comparable aActive cActive ac
  have subsetBa := subset_along_step2 ab
  have subsetCb := subset_along_step2 bc
  have abEqual : FEqual (InF P selected x) a b :=
    fun t => ⟨fun atA => subsetCb t ((acEqual t).mp atA), subsetBa t⟩
  have sound := fun {u v} =>
    step2_sound conditions agree gMax ancestral noSelection witness knowledge (u := u) (v := v)
  have abDirected := sound ab
  have bcDirected := sound bc
  cases ab with
  | strict _ _ _ _ difference =>
    obtain ⟨t, atA, notAtB⟩ := difference
    exact notAtB ((abEqual t).mp atA)
  | @propagate d a b da _ _ _ dNeB dNotAdjB =>
    have daDirected := sound da
    have aReachesC := Reach.extend (Reach.extend (.refl a) abDirected) bcDirected
    have dNeC : d ≠ c := by
      intro same
      subst d
      exact ancestral.no_head_into_ancestor aReachesC (directed_head daDirected)
    have dAdjC : P.Adjacent d c := by
      apply Classical.byContradiction
      intro absent
      exact ac.2.1 (.propagate da cActive ac.1 acEqual dNeC absent)
    have dReachesC := Reach.extend (Reach.extend (Reach.extend (.refl d) daDirected) abDirected) bcDirected
    have tailAtD : G.arrowheadAt d c = false := by
      cases mark : G.arrowheadAt d c with
      | false => rfl
      | true => exact (ancestral.no_head_into_ancestor dReachesC mark).elim
    have dcDirected := r11_sound noSelection ((agree.adjacent d c).mp dAdjC) tailAtD
    obtain ⟨H, hAgree, hMax, same, tailAtC⟩ := witness bcCircle.2
    have unavailable : H.adjacent d b = false := by
      cases head : H.adjacent d b with
      | false => rfl
      | true => exact (dNotAdjB ((hAgree.adjacent d b).mpr head)).elim
    have noncollider := unshielded_noncollider_invariant hMax gMax same dNeC dNeB
      (circle_distinct (show P.CircleEdge c b from ⟨bcCircle.2, bcCircle.1⟩))
      ((hAgree.adjacent d c).mp dAdjC)
      ((hAgree.adjacent c b).mp (by simp [PMG.Adjacent, bcCircle.2])) unavailable
      (by simp [MarkedGraph.collider, tailAtC])
    simp [MarkedGraph.collider, directed_head dcDirected, directed_head bcDirected] at noncollider

/-- Lemma 14 from the final circle-region correspondence. The forbidden
triangle is proved from the compatible MAG in the old class. -/
theorem chordal_from_retained_circles (conditions : P.PossiblePathConditions)
    (agree : Agreement P G) (gMax : G.HasSeparators) (ancestral : AncestralMarks G)
    (noSelection : NoSelection G) (witness : PreviousTailWitnesses P G)
    (knowledge : LocalChoice P G x selected) (priorChordal : CircleChordal P)
    (updated : UpdatedCircles P Q (ActiveDescendant P selected x) (InF P selected x)) :
    CircleChordal Q :=
  chordal_after_local_updates_of_no_chain priorChordal conditions.balanced conditions.tail_into_head
    (comparable_on_active_circles conditions agree gMax ancestral noSelection witness knowledge)
    (no_step2_chain_with_circle_shortcut conditions agree gMax ancestral noSelection witness knowledge)
    updated

end
end OpenCausalScience.Papers.WangQinZhou2023.Step2CircleSafety
