module
public import OpenCausalScience.Papers.AnderssonEtAl1997.EssentialGraph
public import OpenCausalScience.Papers.Meek1995.ChainComponents

/-! The graph obtained by forgetting arrowheads on edges internal to
strongly connected components of the possible-arrow relation. This is
the intermediate chain graph in Andersson, Madigan and Perlman (1997),
§4. Its cross-component arrows and chordal undirected components give
the input for the orientation construction.
-/

namespace OpenCausalScience.Papers.AnderssonEtAl1997.Condensation

open OpenCausalScience.Papers.AnderssonEtAl1997.EssentialGraph
open OpenCausalScience.Papers.VermaPearl1990.DAGEquivalence
open OpenCausalScience.Papers.Meek1995.Closure
open OpenCausalScience.Papers.Meek1995.ChainComponents
open MixedGraph (Reach)

@[expose] public section

variable {n m : Nat}

abbrev PossibleReach (G : DAG n) := Reach (PossibleArrow G)

def SameComponent (G : DAG n) (a b : Fin n) : Prop :=
  PossibleReach G a b ∧ PossibleReach G b a

def AcrossArrow (G : DAG n) (a b : Fin n) : Prop :=
  Compelled G a b ∧ ¬ PossibleReach G b a

theorem PossibleReach.trans {G : DAG n} {a b c : Fin n}
    (first : PossibleReach G a b) (second : PossibleReach G b c) : PossibleReach G a c := by
  induction second with
  | refl => exact first
  | extend _ edge ih => exact .extend ih edge

theorem SameComponent.symm {G : DAG n} {a b : Fin n} (within : SameComponent G a b) :
    SameComponent G b a := ⟨within.2, within.1⟩

theorem SameComponent.trans {G : DAG n} {a b c : Fin n}
    (first : SameComponent G a b) (second : SameComponent G b c) : SameComponent G a c :=
  ⟨first.1.trans second.1, second.2.trans first.2⟩

theorem SameComponent.refl (G : DAG n) (a : Fin n) : SameComponent G a a :=
  ⟨.refl a, .refl a⟩

noncomputable def predecessorCount (G : DAG n) (v : Fin n) : Nat :=
  ((List.finRange n).filter (fun u => @decide (PossibleReach G u v)
    (Classical.propDecidable _))).length

noncomputable def chooseMember (set : Fin n → Prop) (nonempty : ∃ x, set x) : Fin n :=
  Classical.choose nonempty

noncomputable def representative (G : DAG n) (v : Fin n) : Fin n :=
  chooseMember (SameComponent G v) ⟨v, SameComponent.refl G v⟩

theorem representative_member (G : DAG n) (v : Fin n) :
    SameComponent G v (representative G v) :=
  Classical.choose_spec (⟨v, SameComponent.refl G v⟩ : ∃ w, SameComponent G v w)

noncomputable def label (G : DAG n) (v : Fin n) : Nat :=
  n * predecessorCount G v + (representative G v).val

private theorem filter_sublist_of_implies {α : Type} {p q : α → Bool}
    (implies : ∀ x, p x = true → q x = true) (xs : List α) :
    (xs.filter p).Sublist (xs.filter q) := by
  induction xs with
  | nil => exact .slnil
  | cons x xs ih =>
    cases hp : p x with
    | false =>
      cases hq : q x with
      | false => simpa [hp, hq] using ih
      | true => simpa [hp, hq] using ih.cons x
    | true =>
      have hq := implies x hp
      simpa [hp, hq] using ih.cons_cons x

private theorem count_lt {G : DAG n} {u v : Fin n}
    (forward : PossibleReach G u v) (noReverse : ¬ PossibleReach G v u) :
    predecessorCount G u < predecessorCount G v := by
  classical
  let candidates (w : Fin n) := (List.finRange n).filter (fun a => decide (PossibleReach G a w))
  have ordered : (candidates u).Sublist (candidates v) :=
    filter_sublist_of_implies (fun _ h => decide_eq_true (PossibleReach.trans
      (of_decide_eq_true h) forward)) _
  have below := ordered.length_le
  have present : v ∈ candidates v := List.mem_filter.mpr ⟨List.mem_finRange _, by
    exact decide_eq_true (.refl v)⟩
  have absent : v ∉ candidates u := fun h =>
    noReverse (of_decide_eq_true (List.mem_filter.mp h).2)
  have noEqual : (candidates u).length ≠ (candidates v).length := fun h =>
    absent ((ordered.length_eq.mp h).symm ▸ present)
  exact Nat.lt_of_le_of_ne below noEqual

private theorem label_lt_of_count_lt {G : DAG n} {u v : Fin n}
    (less : predecessorCount G u < predecessorCount G v) : label G u < label G v := by
  have primary := Nat.mul_le_mul_left n less
  rw [Nat.mul_succ] at primary
  have bounded := (representative G u).isLt
  unfold label
  omega

theorem label_lt_of_across {G : DAG n} {u v : Fin n} (arrow : AcrossArrow G u v) :
    label G u < label G v := by
  exact label_lt_of_count_lt (count_lt (.extend (.refl u) (possible_iff.mpr (.inl arrow.1)))
    arrow.2)

/-- Component labels agree exactly on the strongly connected components. -/
theorem label_eq_iff {G : DAG n} {u v : Fin n} : label G u = label G v ↔ SameComponent G u v := by
  classical
  constructor
  · intro same
    have counts : predecessorCount G u = predecessorCount G v :=
      Nat.le_antisymm
        (Nat.le_of_not_gt (fun h => Nat.ne_of_lt (label_lt_of_count_lt h) same.symm))
        (Nat.le_of_not_gt (fun h => Nat.ne_of_lt (label_lt_of_count_lt h) same))
    have rep : representative G u = representative G v := by
      apply Fin.ext
      unfold label at same
      rw [counts] at same
      omega
    exact (representative_member G u).trans (rep ▸ (representative_member G v).symm)
  · intro within
    have predicates : SameComponent G u = SameComponent G v :=
      funext fun w => propext ⟨fun h => within.symm.trans h, fun h => within.trans h⟩
    have rep : representative G u = representative G v := by
      unfold representative
      congr
    have predecessorPredicates : (fun w => PossibleReach G w u) = fun w => PossibleReach G w v :=
      funext fun w => propext ⟨fun h => PossibleReach.trans h within.1,
        fun h => PossibleReach.trans h within.2⟩
    have count : predecessorCount G u = predecessorCount G v := by
      unfold predecessorCount
      congr 1
      apply congrArg ((List.finRange n).filter)
      funext w
      have eq := congrFun predecessorPredicates w
      simp only [eq]
    simp [label, rep, count]

private theorem line_of_possible_inside {G : DAG n} {a b : Fin n}
    (step : PossibleArrow G a b) (within : SameComponent G a b) :
    Unoriented G (AcrossArrow G) a b := by
  obtain ⟨H, same, edge⟩ := step
  exact ⟨(sameSkeleton_of_sameDConnections same a b).mpr (Or.inl edge),
    fun arrow => arrow.2 within.2, fun arrow => arrow.2 within.1⟩

theorem possible_path_stays_in_component {G : DAG n} {u v : Fin n}
    (path : PossibleReach G u v) (returnPath : PossibleReach G v u) :
    OpenWalk G (AcrossArrow G) u v := by
  induction path with
  | refl => exact .stay _
  | extend first last ih =>
    have step : PossibleReach G _ _ := .extend (.refl _) last
    have before := PossibleReach.trans step returnPath
    exact .step (ih before) (line_of_possible_inside last ⟨step, PossibleReach.trans returnPath first⟩)

private theorem across_of_base {G : DAG n} {a b : Fin n}
    (edge : G.edge a b = true) (outside : ¬ SameComponent G a b) : AcrossArrow G a b := by
  have possible : PossibleArrow G a b := ⟨G, fun _ _ _ => Iff.rfl, edge⟩
  have noBack : ¬ PossibleReach G b a := fun back =>
    outside ⟨.extend (.refl a) possible, back⟩
  exact ⟨(possible_iff.mp possible).resolve_right fun rev => noBack (.extend (.refl b) rev.2),
    noBack⟩

theorem across_or_reverse_of_adjacent {G : DAG n} {a b : Fin n}
    (edge : Adjacent G a b) (outside : ¬ SameComponent G a b) :
    AcrossArrow G a b ∨ AcrossArrow G b a :=
  edge.imp (fun ab => across_of_base ab outside)
    (fun ba => across_of_base ba (fun h => outside h.symm))

theorem line_within {G : DAG n} {a b : Fin n}
    (line : Unoriented G (AcrossArrow G) a b) : SameComponent G a b :=
  Classical.byContradiction fun outside =>
    (across_or_reverse_of_adjacent line.1 outside).elim line.2.1 line.2.2

/-- The condensation is a chain graph with the parent inheritance
property. Compelled arrows on a cycle are temporarily treated as lines. -/
noncomputable def components (G : DAG n) : Components G (AcrossArrow G) :=
  components_of_r1 (label G) (fun _ _ => label_lt_of_across)
    (fun _ _ adj different => across_or_reverse_of_adjacent adj
      (fun h => different (label_eq_iff.mpr h)))
    (fun _ _ equal =>
      let within := label_eq_iff.mp equal
      possible_path_stays_in_component within.1 within.2)
    (fun _ _ _ ab line different absent =>
      let same := line_within line
      (no_flag_after_forgetting_internal_arrows ab.1 line.1 same.1 same.2 different absent).elim)

/-- Forgetting internal arrows preserves every unshielded collider. -/
theorem contains_colliders (G : DAG n) : ContainsColliders G (AcrossArrow G) := by
  intro a b c collider
  have reverse : UnshieldedCollider G c b a :=
    ⟨collider.1.symm, fun edge => collider.2.1 (Or.symm edge), collider.2.2.2, collider.2.2.1⟩
  have fixed := collider_arrows_compelled collider
  exact ⟨⟨fixed.1, collider_arrow_has_no_return collider⟩,
    ⟨fixed.2, collider_arrow_has_no_return reverse⟩⟩

end
end OpenCausalScience.Papers.AnderssonEtAl1997.Condensation
