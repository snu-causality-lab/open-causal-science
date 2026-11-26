module
public import OpenCausalScience.Papers.WangQinZhou2023.CircleChordality
public import OpenCausalScience.Papers.WangQinZhou2023.LocalTransformation

/-! Algorithm 1's Step 2 on the exact possible-descendant region and
its application to chordality in Lemma 14.
Source: https://doi.org/10.1016/j.artint.2023.103964
-/

namespace OpenCausalScience.Papers.WangQinZhou2023.CircleUpdates

open LocalBackgroundKnowledge LocalTransformation CircleChordality
open Zhang2008OrientationRules.Orientations (Directed AncestralMarks)

@[expose] public section

variable {n : Nat}

def ActiveDescendant (P : PMG n) (selected : Fin n → Prop) (x v : Fin n) : Prop :=
  v ≠ x ∧ PossibleDescendantAvoiding P selected x v

variable {P Q : PMG n} {G : MarkedGraph n} {x : Fin n} {selected : Fin n → Prop}

private theorem active_not_selected {v : Fin n} (active : ActiveDescendant P selected x v) :
    ¬ selected v := by
  obtain ⟨_, length, _, _, finish, avoids⟩ := active.2
  exact finish ▸ avoids length (Nat.le_refl length)

variable (conditions : P.PossiblePathConditions) (agree : Agreement P G)
  (gMax : G.HasSeparators) (ancestral : AncestralMarks G) (noSelection : NoSelection G)
  (witness : PreviousTailWitnesses P G) (knowledge : LocalChoice P G x selected)

include conditions agree gMax ancestral noSelection witness knowledge

private theorem directs_of_difference {u v t : Fin n}
    (uActive : ActiveDescendant P selected x u) (vActive : ActiveDescendant P selected x v)
    (circle : P.CircleEdge u v) (inF : InF P selected x u t) (notInF : ¬ InF P selected x v t) :
    Directed G u v :=
  step2_from_different_f conditions.balanced agree gMax ancestral noSelection witness knowledge
    uActive.1 vActive.1 (active_not_selected uActive) (active_not_selected vActive)
    (possible_descendant_is_descendant conditions agree gMax ancestral noSelection witness knowledge uActive.2)
    (possible_descendant_is_descendant conditions agree gMax ancestral noSelection witness knowledge vActive.2)
    circle inF notInF

/-- Algorithm 1's local sets are comparable on every active circle
edge. Differences in both directions would demand contradictory marks
in the compatible MAG. -/
theorem comparable_on_active_circles :
    Comparable P (ActiveDescendant P selected x) (InF P selected x) := by
  intro u v uActive vActive circle
  by_cases uv : FSubset (InF P selected x) u v
  · exact .inl uv
  · right
    intro t vt
    apply Classical.byContradiction
    intro notUt
    have failure : ∃ s, InF P selected x u s ∧ ¬ InF P selected x v s := by
      apply Classical.byContradiction
      intro noDifference
      exact uv (fun s us => Classical.byContradiction fun notVs => noDifference ⟨s, us, notVs⟩)
    obtain ⟨s, us, notVs⟩ := failure
    exact no_opposing_demands
      (directs_of_difference conditions agree gMax ancestral noSelection witness knowledge
        uActive vActive circle us notVs)
      (directs_of_difference conditions agree gMax ancestral noSelection witness knowledge
        vActive uActive ⟨circle.2, circle.1⟩ vt notUt)

/-- Every Step 2 derivation gives a directed edge in an arbitrary
compatible MAG, including repeated unshielded propagation. -/
theorem step2_sound {u v : Fin n}
    (demand : Step2 P (ActiveDescendant P selected x) (InF P selected x) u v) :
    Directed G u v := by
  induction demand with
  | strict uActive vActive circle _ strict =>
    obtain ⟨t, inF, notInF⟩ := strict
    exact directs_of_difference conditions agree gMax ancestral noSelection witness knowledge
      uActive vActive circle inF notInF
  | @propagate a u v prior _ circle _ distinct absent ih =>
    have ends : a ≠ u := by
      intro same
      subst u
      change G.marks a a = some (false, true) at ih
      simp [G.loop_free] at ih
    exact step2_propagates_direction agree gMax witness ancestral ends distinct
      (circle_distinct circle) ih circle absent

/-- Lemma 14 for the exact Step 2 region and `F` sets. The premises about
the final marks describe the update and the directed case of R2 closure. -/
theorem chordal_after_algorithm1_updates (priorChordal : CircleChordal P)
    (updated : UpdatedCircles P Q (ActiveDescendant P selected x) (InF P selected x))
    (directed : ∀ {u v}, Step2 P (ActiveDescendant P selected x) (InF P selected x) u v → Q.Directed u v)
    (r2 : ∀ {a b c}, Q.Directed a b → Q.Directed b c →
      Q.markAt c a = some .circle → Q.ArrowInto a c) : CircleChordal Q :=
  chordal_after_local_updates priorChordal conditions.balanced conditions.tail_into_head
    (comparable_on_active_circles conditions agree gMax ancestral noSelection witness knowledge)
    updated directed r2

end
end OpenCausalScience.Papers.WangQinZhou2023.CircleUpdates
